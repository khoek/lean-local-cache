import tactic.local_cache

section example_tactic

-- Example "expensive" function
meta def generate_some_data : tactic (list ℕ) :=
do tactic.trace "cache regenerating",
   return [1, 2, 3, 4]

meta def my_tactic : tactic unit :=
do my_cached_data ← calculate_once `my_tactic generate_some_data,
   -- Do some stuff with `my_cached_data`
   tactic.skip

end example_tactic



section example_usage

-- Note only a single cache regeneration (only a single trace message)
lemma my_lemma : true := begin
    my_tactic,
    my_tactic,
    my_tactic,

    trivial
end

end example_usage