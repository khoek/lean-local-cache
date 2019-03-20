import tactic.basic

universe u

section lib

def list_to_name_aux : name → list string → name
| n [] := n
| n (s :: rest) := list_to_name_aux (name.mk_string s n) rest

def list_to_name (l : list string) : name :=
list_to_name_aux name.anonymous l

def split_on_aux {α : Type u} [decidable_eq α] (a : α) : list α → list α → list (list α)
| [] l       := [l.reverse]
| (h :: t) l := if h = a then
                  l.reverse :: (split_on_aux t [])
                else
                  split_on_aux t (h :: l)

def list.split_on {α : Type u} [decidable_eq α] (a : α) : list α → list (list α)
| l := split_on_aux a l []

def string.split_on (c : char) (s : string) := (s.to_list.split_on c).map (λ l, l.as_string)

end lib

section local_cache

variables {α : Type} [reflected α] [has_reflect α]

meta def mk_full_namespace (ns : name) : name := `data.cache ++ ns

meta def get_data_name (ns : name) : tactic name :=
do o ← tactic.get_options,
   let opt := mk_full_namespace ns,
   match o.get_string opt "" with
   | "" := do n ← tactic.mk_user_fresh_name,
              tactic.set_options $ o.set_string opt n.to_string,
              return n
   | s := return $ list_to_name $ s.split_on '.'
   end

meta def save_data (dn : name) (a : α) [reflected a] : tactic unit :=
tactic.add_decl $ mk_definition dn [] (reflect α) (reflect a)

meta def load_data (dn : name) : tactic α :=
do e ← tactic.get_env,
   d ← e.get dn,
   tactic.eval_expr α d.value

meta def calculate_once {α : Type} [reflected α] [has_reflect α] (ns : name) (t : tactic α) : tactic α :=
do dn ← get_data_name ns,
   load_data dn <|>
   do {
     a ← t,
     save_data dn a,
     return a
   }

end local_cache