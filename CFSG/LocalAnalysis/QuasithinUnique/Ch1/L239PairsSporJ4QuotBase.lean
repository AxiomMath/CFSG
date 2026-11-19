
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Check
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsBlocks
public import CFSG.Sporadic.J4.QTProof

@[expose] public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.Mathieu

def StarOK (g : J) (i i' : ℕ) : Prop :=
  ∀ c ∈ starMasks.getD i [], ∃ c' ∈ starMasks.getD i' [], g * eta uJ 11 c * g⁻¹ = eta uJ 11 c'

theorem starOK_one (i : ℕ) : StarOK 1 i i := fun c hc => ⟨c, hc, by simp⟩

theorem starOK_mul {g h : J} {i i' i'' : ℕ} (hg : StarOK g i i') (hh : StarOK h i' i'') :
    StarOK (h * g) i i'' := by
  intro c hc
  obtain ⟨c', hc', e1⟩ := hg c hc
  obtain ⟨c'', hc'', e2⟩ := hh c' hc'
  refine ⟨c'', hc'', ?_⟩
  calc h * g * eta uJ 11 c * (h * g)⁻¹ = h * (g * eta uJ 11 c * g⁻¹) * h⁻¹ := by group
    _ = h * eta uJ 11 c' * h⁻¹ := by rw [e1]
    _ = eta uJ 11 c'' := e2

theorem mem_star_lt
    {i c : ℕ} (hi : i < 24) (hc : c ∈ starMasks.getD i []) : c < 2 ^ 11 := by
  obtain ⟨hd, hlen, hs, -⟩ := star_facts
  have hmem : starMasks.getD i [] ∈ starMasks := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  exact (hd c ((hs _ hmem).2 c hc)).2

theorem genM24_mem (m : ℕ) : genM24 m ∈ CFSG.Blueprint.NativeSporadic.M24 := by
  rw [m24_eq]
  rcases m with _ | _ | m
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · exact (Subgroup.closure _).inv_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem tauOf_mem
    {k : ℕ} (hk : k < 3) : tauOf k ∈ CFSG.Blueprint.NativeSporadic.M24 := by
  rw [← (tau_facts k hk).2]
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
  exact genM24_mem m

theorem not_chi0Order_M24 : ¬ Chi0Order 244823040 := by
  rintro (h | ⟨n, hn, h⟩)
  · norm_num at h
  · have hn28 : n < 28 := by
      by_contra hc
      have h1 : 2 ^ 28 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h4 : 4 ≤ 4 ^ n := by
        calc 4 = 4 ^ 1 := by norm_num
          _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ n ≤ 2 ^ n * (4 ^ n - 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    interval_cases n <;> omega

end CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
