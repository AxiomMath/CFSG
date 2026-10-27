module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcCount
public import CFSG.LieType.Chevalley.OddToralInvolutionComponents

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem gomi_prod_zpow_eq_zpow_sum {ι G : Type*} [CommGroup G] (s : Finset ι) (u : G) (c : ι → ℤ) :
    ∏ i ∈ s, u ^ c i = u ^ ∑ i ∈ s, c i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, zpow_add, ih]

section Toral

variable {τ : Tag} {F : Type} [Field F] [DecidableEq Fˣ]

theorem gomi_rootChar_eq_one_of_even (b : Fin τ.rank → Fˣ) (hb : ∀ i, b i = 1 ∨ b i = -1)
    (α : Fin τ.rank → ℤ) (hα : Even (∑ i, if b i = -1 then α i else 0)) : rootChar b α = 1 := by
  classical
  have h1 : ∀ i, b i ^ α i = (-1 : Fˣ) ^ (if b i = -1 then α i else 0) := by
    intro i
    by_cases hbi : b i = -1
    · rw [if_pos hbi, hbi]
    · rw [if_neg hbi, zpow_zero]
      rcases hb i with h | h
      · rw [h, one_zpow]
      · exact absurd h hbi
  unfold rootChar
  rw [Finset.prod_congr rfl fun i _ => h1 i, gomi_prod_zpow_eq_zpow_sum]
  exact hα.neg_one_zpow

theorem gomi_ofFn_rootVec {τ : Tag} {l : List ℤ} (hl : l.length = τ.rank) :
    List.ofFn (gomiRootVec l : Fin τ.rank → ℤ) = l := by
  refine List.ext_getElem (by simp [hl]) fun n h1 h2 => ?_
  simp only [List.getElem_ofFn, gomiRootVec]
  rw [List.getD_eq_getElem]

end Toral

section ToralCard

variable {τ : Tag} {F : Type} [Field F]

theorem gomi_toral_pow_five_dvd
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (b : Fin τ.rank → Fˣ)
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hne : ∃ i, b i = -1) :
    Nat.card F ^ 5 ∣ Nat.card (toralCentralizer τ F b) := by
  classical
  set S : Set (Fin τ.rank → ℤ) := {α | IsRoot τ α ∧ 0 < height α ∧ rootChar b α = 1} with hSdef
  have hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α := fun α hα => ⟨hα.1, hα.2.1⟩
  have hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a c : ℕ, 1 ≤ a → 1 ≤ c → IsRoot τ (a • α + c • β) →
      a • α + c • β ∈ S := by
    intro α hα β hβ a c ha hc hroot
    refine ⟨hroot, ?_, ?_⟩
    · rw [height_nsmul_add_nsmul]
      have h1 := hα.2.1
      have h2 := hβ.2.1
      have h3 : (0 : ℤ) < a := by exact_mod_cast ha
      have h4 : (0 : ℤ) < c := by exact_mod_cast hc
      positivity
    · rw [← natCast_zsmul α a, ← natCast_zsmul β c, rootChar_add, rootChar_zsmul, rootChar_zsmul,
        hα.2.2, hβ.2.2]
      simp
  have hsub : S ⊆ rootCharKernel b := fun α hα => ⟨hα.1, hα.2.2⟩
  have hle : rootSpan τ F S ≤ toralCentralizer τ F b :=
    (biSup_mono fun α hα => hsub hα).trans (rootSpan_rootCharKernel_le_toralCentralizer b)
  have hcard := card_rootSpan (τ := τ) (K := F) hS hclosed
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hcard] at hdvd
  have h5 : 5 ≤ S.ncard := by
    set m : Fin τ.rank → Bool := fun i => decide (b i = -1) with hm
    have hm' : ∃ i, m i = true := by
      obtain ⟨i, hi⟩ := hne
      exact ⟨i, by simp [hm, hi]⟩
    have hcnt := gomi_count hτ m hm'
    set L := (τ.artifactRoots).filter (fun l =>
      decide (0 < ∑ i : Fin τ.rank, gomiRootVec l i) &&
        decide (Even (∑ i : Fin τ.rank, if m i then gomiRootVec l i else 0))) with hL
    have hLlen : L.length = gomiPosEvenCount τ m := rfl
    have hLnodup : L.Nodup := (nodup_artifactRoots τ).filter _
    have hinj : Set.InjOn (gomiRootVec : List ℤ → Fin τ.rank → ℤ) (↑L.toFinset : Set (List ℤ)) := by
      intro l hl l' hl' hll'
      have hl1 : l ∈ L := List.mem_toFinset.1 hl
      have hl2 : l' ∈ L := List.mem_toFinset.1 hl'
      have h1 := length_of_mem_artifactRoots (List.mem_filter.1 hl1).1
      have h2 := length_of_mem_artifactRoots (List.mem_filter.1 hl2).1
      rw [← gomi_ofFn_rootVec h1, ← gomi_ofFn_rootVec h2, hll']
    have hS₀S : (gomiRootVec : List ℤ → Fin τ.rank → ℤ) '' (↑L.toFinset : Set (List ℤ)) ⊆ S := by
      rintro _ ⟨l, hl, rfl⟩
      have hlL : l ∈ L := List.mem_toFinset.1 hl
      obtain ⟨hlr, hcond⟩ := List.mem_filter.1 hlL
      have hlen := length_of_mem_artifactRoots hlr
      have hv := gomi_ofFn_rootVec (τ := τ) hlen
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      refine ⟨?_, ?_, ?_⟩
      · exact isRoot_iff_mem_artifactRoots.2 (by rw [hv]; exact hlr)
      · exact hcond.1
      · refine gomi_rootChar_eq_one_of_even b hb _ ?_
        have := hcond.2
        simpa [hm] using this
    have hS₀card : ((gomiRootVec : List ℤ → Fin τ.rank → ℤ) '' (↑L.toFinset : Set (List ℤ))).ncard
        = L.length := by
      rw [hinj.ncard_image, Set.ncard_coe_finset, List.toFinset_card_of_nodup hLnodup]
    have hfin : S.Finite := finite_of_forall_isRoot_pos hS
    calc 5 ≤ L.length := by omega
      _ = _ := hS₀card.symm
      _ ≤ S.ncard := Set.ncard_le_ncard hS₀S hfin
  exact (pow_dvd_pow _ h5).trans hdvd

end ToralCard

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
