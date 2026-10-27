module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitInputs
public import CFSG.ClassicalInvolution.SmallCases.Rank3NormalEight

public section

namespace CFSG.OddStandard.Harada75

open CFSG Subgroup

@[expose] def TwoGroupStatement : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsPGroup 2 S → ∀ E : Subgroup S,
    IsElementaryAbelian 2 E → Nat.card E = 8 → centralizer (E : Set S) = E →
    ∀ P : Subgroup S, ∃ s : Finset S, s.card ≤ 4 ∧ closure (s : Set S) = P

theorem haradaInput_of_twoGroup (h : TwoGroupStatement) :
    ComponentClassification.HSFLit.HaradaInput := by
  refine ⟨h, ?_⟩
  intro G _ _ E hE h8 hC P hP
  have : IsElementaryAbelian 2 E := hE
  obtain ⟨Q, hEQ⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  have : IsElementaryAbelian 2 (E.subgroupOf (Q : Subgroup G)) :=
    IsElementaryAbelian.subgroupOf hEQ
  have hcard : Nat.card (E.subgroupOf (Q : Subgroup G)) = 8 := by
    rw [← h8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ centralizer (E : Set G) := by rw [hC]; exact hx
    exact (Subgroup.mem_centralizer_iff.mp hx' y hy).symm
  have hcent : centralizer ((E.subgroupOf (Q : Subgroup G) : Subgroup (Q : Subgroup G)) :
      Set (Q : Subgroup G)) = E.subgroupOf (Q : Subgroup G) := by
    apply le_antisymm
    · intro x hx
      refine Subgroup.mem_subgroupOf.mpr ?_
      have hxG : (x : G) ∈ centralizer (E : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have := Subgroup.mem_centralizer_iff.mp hx ⟨y, hEQ hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
        exact congrArg Subtype.val this
      rw [hC] at hxG
      exact hxG
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      exact hcomm _ (Subgroup.mem_subgroupOf.mp hy) _ (Subgroup.mem_subgroupOf.mp hx)
  have hS := h (Q : Subgroup G) Q.isPGroup' (E.subgroupOf (Q : Subgroup G)) inferInstance hcard
    hcent
  classical
  refine CFSG.ClassicalInvolution.fourGenerated_of_sylow Q (fun P' hP'Q => ?_) P hP
  obtain ⟨X, hX4, hXcl⟩ := hS (P'.subgroupOf (Q : Subgroup G))
  refine ⟨X.image (Q : Subgroup G).subtype, Finset.card_image_le.trans hX4, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hXcl]
  exact Subgroup.map_subgroupOf_eq_of_le hP'Q

end CFSG.OddStandard.Harada75
