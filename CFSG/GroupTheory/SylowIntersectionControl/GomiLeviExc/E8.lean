module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.CharTwoSteinberg
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GroupTheory.GomiLeviExc.E8

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley

section Roots

private theorem iform_self_eq_two_E8 {γ : Fin (Tag.rank .E8) → ℤ} (hγ : IsRoot .E8 γ) :
    iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rw [hj, show (Tag.symmetrizer .E8) j j = 1 by simp [Tag.symmetrizer]]
  norm_num

private theorem not_isRoot_sub_of_isRoot_add_E8 {α β : Fin (Tag.rank .E8) → ℤ}
    (hα : IsRoot .E8 α) (hβ : IsRoot .E8 β) (h : IsRoot .E8 (α + β)) :
    ¬ IsRoot .E8 (β - α) := by
  intro hsub
  have hsum : iform (α + β) (α + β) = 2 := iform_self_eq_two_E8 h
  rw [iform_add_left, iform_add_right, iform_add_right, iform_self_eq_two_E8 hα,
    iform_self_eq_two_E8 hβ, iform_comm β α] at hsum
  have hαβ : iform α β = -1 := by omega
  have hsq : iform (β - α) (β - α) = 6 := by
    rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_self_eq_two_E8 hβ,
      iform_self_eq_two_E8 hα, iform_comm β α, hαβ]
    ring
  rcases iform_self_cases noG2_E8 hsub with h2 | h4 <;> omega

private theorem not_isRoot_add_two_smul_E8 {α β : Fin (Tag.rank .E8) → ℤ}
    (hα : IsRoot .E8 α) (hβ : IsRoot .E8 β) (hne : α ≠ β) (hne' : α ≠ -β) :
    ¬ IsRoot .E8 (α + 2 • β) := by
  intro h
  have h' : IsRoot .E8 (1 • α + 2 • β) := by simpa using h
  rcases exponent_pair_cases noG2_E8 hα hβ hne hne' le_rfl (by norm_num) h' with
    h1 | h2 | h3
  · omega
  · obtain ⟨-, -, h4, -⟩ := h2
    have h2' := iform_self_eq_two_E8 hα
    omega
  · omega

private theorem not_isRoot_two_smul_add_E8 {α β : Fin (Tag.rank .E8) → ℤ}
    (hα : IsRoot .E8 α) (hβ : IsRoot .E8 β) (hne : α ≠ β) (hne' : α ≠ -β) :
    ¬ IsRoot .E8 (2 • α + β) := by
  intro h
  have h' : IsRoot .E8 (2 • α + 1 • β) := by simpa using h
  rcases exponent_pair_cases noG2_E8 hα hβ hne hne' (by norm_num) le_rfl h' with
    h1 | h2 | h3
  · omega
  · omega
  · obtain ⟨-, -, -, h4, -⟩ := h3
    have h2' := iform_self_eq_two_E8 hβ
    omega

end Roots

variable (K : Type) [Field K]

private theorem coeff11_eq_one_E8 [CharP K 2] {α β : Fin (Tag.rank .E8) → ℤ}
    (hα : IsRoot .E8 α) (hβ : IsRoot .E8 β) (hne' : α ≠ -β) (h : IsRoot .E8 (α + β)) :
    (RootOperatorFamily'.coeff11 (rootOperatorFamily .E8) e8Data_valid
      ⟨α, hα⟩ ⟨β, hβ⟩ : K) = 1 := by
  have hβα : β ≠ -α := fun h' => hne' (by rw [h', neg_neg])
  have hN : (RootOperatorFamily'.coeff11 (rootOperatorFamily .E8) e8Data_valid
      ⟨α, hα⟩ ⟨β, hβ⟩).natAbs = 1 := by
    rw [RootOperatorFamily'.coeff11,
      RootOperatorFamily'.bracketCoeff_natAbs (rootOperatorFamily .E8) e8Data_valid hβα h]
    exact stringNorm_of_not_isRoot (not_isRoot_sub_of_isRoot_add_E8 hα hβ h)
  rcases Int.natAbs_eq_iff.1 hN with h1 | h1
  · rw [h1]
    norm_num
  · rw [h1]
    simpa using CharTwo.neg_eq (1 : K)

theorem isCharTwoSteinberg [CharP K 2] : IsCharTwoSteinberg (e8Datum K).roots (e8Par K) := by
  refine ⟨fun γ _ c d => ?_, ?_⟩
  · simpa only [e8Par] using xPar_add (F := rootOperatorFamily .E8) (K := K) γ c d
  intro α hα β hβ hsum c d
  have hα' : IsRoot .E8 α := mem_adjDatum_roots.1 hα
  have hβ' : IsRoot .E8 β := mem_adjDatum_roots.1 hβ
  by_cases hαβ : α = β
  · have hβ_eq : β = α := hαβ.symm
    subst hβ_eq
    have hnn : ¬ IsRoot .E8 (β + β) := by
      intro h
      have h2 : IsRoot .E8 (2 • β) := by simpa [two_smul] using h
      have := eq_one_of_isRoot_nsmul h2
      omega
    rw [commutatorElement_eq_one_iff_commute.mpr
      (commute_xPar (F := rootOperatorFamily .E8) (K := K) e8Data_valid noG2_E8 hβ' hβ'
        hsum hnn c d),
      if_neg (fun hmem => hnn (mem_adjDatum_roots.1 hmem))]
  · have hne' : α ≠ -β := fun h => hsum (by rw [h, neg_add_cancel])
    have h12 : ¬ IsRoot .E8 (α + 2 • β) :=
      not_isRoot_add_two_smul_E8 hα' hβ' hαβ hne'
    have h21 : ¬ IsRoot .E8 (2 • α + β) :=
      not_isRoot_two_smul_add_E8 hα' hβ' hαβ hne'
    have hcomm := commutator_xPar (F := rootOperatorFamily .E8) (K := K) e8Data_valid
      noG2_E8 hα' hβ' hαβ hne' c d
    rw [xPar_of_not_isRoot h12, xPar_of_not_isRoot h21, mul_one, mul_one] at hcomm
    rw [hcomm]
    by_cases h : IsRoot .E8 (α + β)
    · rw [if_pos (mem_adjDatum_roots.2 h),
        coeff11_eq_one_E8 (K := K) hα' hβ' hne' h, one_mul]
    · rw [if_neg (fun hmem => h (mem_adjDatum_roots.1 hmem)), xPar_of_not_isRoot h]

end CFSG.GroupTheory.GomiLeviExc.E8
