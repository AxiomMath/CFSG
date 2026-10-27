
module

public import CFSG.LocalAnalysis.OddStandard.ONanB2A6FactsBase

public import Certificates.Certificate6151

public section

namespace CFSG.OddStandard.ONanRec.A6C

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

theorem a6_parts :
    a6ExpCheck = true ∧ a6OrdCheck = true ∧ a6SylCheck = true ∧ a6DistCheck = true ∧
      a6InvCheck = true ∧ a6FixCheck = true ∧ a6RelCheck = true := by
  have h := Certificates.certificate6151
  simp only [a6MirrorCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem pow_120_eq_one {b : P10} (hb : b ∈ A6Models.autA6) :
    b ^ 120 = 1 := by
  have := List.all_eq_true.1 a6_parts.1 (code b) (code_mem_autL hb)
  rwa [← code_pow, beq_code_cid] at this

theorem no_order_six_eight {x : P10}
    (hx : x ∈ A6Models.psl29) : (x ^ 6 = 1 → x ^ 2 = 1 ∨ x ^ 3 = 1) ∧ (x ^ 8 = 1 → x ^ 4 = 1) := by
  have := List.all_eq_true.1 a6_parts.2.1 (code x) ((mem_psl29_iff x).1 hx)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', ← code_pow,
    beq_code_cid_false, beq_code_cid] at this
  obtain ⟨h6, h8⟩ := this
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h6 with (h6 | h6) | h6
    · exact absurd h h6
    · exact Or.inl h6
    · exact Or.inr h6
  · rcases h8 with h8 | h8
    · exact absurd h h8
    · exact h8

theorem exists_PC {u : P10} (hu : u ∈ A6Models.psl29)
    (h4 : Ord4 u) : ∃ r ∈ A6Models.psl29, PC u r := by
  have := List.all_eq_true.1 a6_parts.2.2.1 (code u) ((mem_psl29_iff u).1 hu)
  rw [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with h | h
  · rw [← Bool.not_eq_true, ord4_code] at h
    exact absurd h4 h
  · obtain ⟨c, hc, hpc⟩ := List.any_eq_true.1 h
    obtain ⟨r, hr, rfl⟩ := exists_psl29_of_code hc
    exact ⟨r, hr, (pCond_code u r).1 hpc⟩

theorem pElt_injective {u r : P10} (hu : u ∈ A6Models.psl29)
    (hr : r ∈ A6Models.psl29) (h4 : Ord4 u) (hpc : PC u r) {i j i' j' : ℕ} (hi : i < 3)
    (hj : j < 3) (hi' : i' < 3) (hj' : j' < 3) (he : pEltP u r i j = pEltP u r i' j') :
    i = i' ∧ j = j' := by
  have := List.all_eq_true.1 a6_parts.2.2.2.1 (code u) ((mem_psl29_iff u).1 hu)
  rw [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with h | h
  · rw [← Bool.not_eq_true, ord4_code] at h
    exact absurd h4 h
  have h2 := List.all_eq_true.1 h (code r) ((mem_psl29_iff r).1 hr)
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · rw [← Bool.not_eq_true, pCond_code] at h2
    exact absurd hpc h2
  rw [decide_eq_true_eq] at h2
  set L := (List.range 3).flatMap fun i => (List.range 3).map fun j => (i, j) with hL
  have hmap : ((List.range 3).flatMap fun i => (List.range 3).map fun j =>
      pElt (code u) (code r) i j) = L.map fun p => pElt (code u) (code r) p.1 p.2 := by
    rw [hL, List.map_flatMap]
    simp only [List.map_map]
    rfl
  rw [hmap] at h2
  have hmem : ∀ {a b : ℕ}, a < 3 → b < 3 → (a, b) ∈ L := by
    intro a b ha hb
    rw [hL, List.mem_flatMap]
    exact ⟨a, List.mem_range.2 ha, List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩⟩
  have := List.inj_on_of_nodup_map h2 (hmem hi hj) (hmem hi' hj') (by
    simp only [pElt_code, he])
  simp only [Prod.mk.injEq] at this
  exact this

theorem exists_DC {u : P10} (hu : u ∈ A6Models.psl29)
    (h4 : Ord4 u) : ∃ w ∈ A6Models.psl29, DC u w := by
  have := List.all_eq_true.1 a6_parts.2.2.2.2.1 (code u) ((mem_psl29_iff u).1 hu)
  rw [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with h | h
  · rw [← Bool.not_eq_true, ord4_code] at h
    exact absurd h4 h
  · obtain ⟨c, hc, hdc⟩ := List.any_eq_true.1 h
    obtain ⟨w, hw, rfl⟩ := exists_psl29_of_code hc
    exact ⟨w, hw, (dCond_code u w).1 hdc⟩

theorem eq_one_of_comm {b u r : P10}
    (hb : b ∈ A6Models.autA6) (hu : u ∈ A6Models.psl29) (hr : r ∈ A6Models.psl29) (h4 : Ord4 u)
    (hpc : PC u r) (hbu : b * u = u * b) (hbr : b * r = r * b) : b = 1 := by
  have := List.all_eq_true.1 a6_parts.2.2.2.2.2.1 (code b) (code_mem_autL hb)
  rw [Bool.or_eq_true] at this
  rcases this with h | h
  · exact (beq_code_cid b).1 h
  exfalso
  have h2 := List.all_eq_true.1 h (code u) ((mem_psl29_iff u).1 hu)
  have h3 : (ord4 (code u) && Core.cmul (code b) (code u) == Core.cmul (code u) (code b)) =
      true := by
    rw [Bool.and_eq_true, ord4_code, ← code_mul, ← code_mul, beq_code]
    exact ⟨h4, hbu⟩
  rw [h3, Bool.not_true, Bool.false_or] at h2
  have h5 := List.all_eq_true.1 h2 (code r) ((mem_psl29_iff r).1 hr)
  have h6 : (pCond (code u) (code r) && Core.cmul (code b) (code r) ==
      Core.cmul (code r) (code b)) = true := by
    rw [Bool.and_eq_true, pCond_code, ← code_mul, ← code_mul, beq_code]
    exact ⟨hpc, hbr⟩
  rw [h6] at h5
  exact Bool.false_ne_true h5

theorem exists_rel {u d r0 : P10} (hu : u ∈ A6Models.psl29)
    (hd : d ∈ A6Models.psl29) (hr0 : r0 ∈ A6Models.psl29) (h4 : Ord4 u) (hdc : DC u d)
    (hpc : PC u r0) :
    ∃ i j, i < 3 ∧ j < 3 ∧ (d * eOfP u (pEltP u r0 i j)) ^ 3 = 1 := by
  have h1 := List.all_eq_true.1 a6_parts.2.2.2.2.2.2 (code u) ((mem_psl29_iff u).1 hu)
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with h1 | h1
  · rw [← Bool.not_eq_true, ord4_code] at h1
    exact absurd h4 h1
  have h2 := List.all_eq_true.1 h1 (code d) ((mem_psl29_iff d).1 hd)
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · rw [← Bool.not_eq_true, dCond_code] at h2
    exact absurd hdc h2
  rw [Bool.and_eq_true] at h2
  have h3 := List.all_eq_true.1 h2.1 (code r0) ((mem_psl29_iff r0).1 hr0)
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h3
  rcases h3 with h3 | h3
  · rw [← Bool.not_eq_true, pCond_code] at h3
    exact absurd hpc h3
  obtain ⟨i, hi, hi'⟩ := List.any_eq_true.1 h3
  obtain ⟨j, hj, hj'⟩ := List.any_eq_true.1 hi'
  refine ⟨i, j, List.mem_range.1 hi, List.mem_range.1 hj, ?_⟩
  rwa [pElt_code, eOf_code, ← code_mul, ← code_pow, beq_code_cid] at hj'

theorem relP_or {b u d r0 : P10} (hb : b ∈ A6Models.autA6)
    (hu : u ∈ A6Models.psl29) (hd : d ∈ A6Models.psl29) (hr0 : r0 ∈ A6Models.psl29)
    (h4 : Ord4 u) (hdc : DC u d) (hpc : PC u r0) (hbc : BC u d b) {i j : ℕ} (hi : i < 3)
    (hj : j < 3) (hde : (d * eOfP u (pEltP u r0 i j)) ^ 3 = 1) :
    RelP b d (eOfP u (pEltP u r0 i j)) ∨ RelP (u ^ 2 * b) d (eOfP u (pEltP u r0 i j)) := by
  have h1 := List.all_eq_true.1 a6_parts.2.2.2.2.2.2 (code u) ((mem_psl29_iff u).1 hu)
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with h1 | h1
  · rw [← Bool.not_eq_true, ord4_code] at h1
    exact absurd h4 h1
  have h2 := List.all_eq_true.1 h1 (code d) ((mem_psl29_iff d).1 hd)
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · rw [← Bool.not_eq_true, dCond_code] at h2
    exact absurd hdc h2
  rw [Bool.and_eq_true] at h2
  have h3 := List.all_eq_true.1 h2.2 (code b) (code_mem_autL hb)
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h3
  rcases h3 with h3 | h3
  · rw [← Bool.not_eq_true, bCond_code] at h3
    exact absurd hbc h3
  have h5 := List.all_eq_true.1 h3 (code r0) ((mem_psl29_iff r0).1 hr0)
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h5
  rcases h5 with h5 | h5
  · rw [← Bool.not_eq_true, pCond_code] at h5
    exact absurd hpc h5
  have h6 := List.all_eq_true.1 (List.all_eq_true.1 h5 i (List.mem_range.2 hi)) j
    (List.mem_range.2 hj)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h6
  rw [pElt_code, eOf_code, ← code_mul, ← code_pow, beq_code_cid_false, ← code_pow,
    ← code_mul, relG_code, relG_code] at h6
  rcases h6 with (h6 | h6) | h6
  · exact absurd hde h6
  · exact Or.inl h6
  · exact Or.inr h6

end CFSG.OddStandard.ONanRec.A6C
