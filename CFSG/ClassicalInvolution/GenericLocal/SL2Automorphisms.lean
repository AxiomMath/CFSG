module

public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields

public section

namespace CFSG.ClassicalInvolution

open scoped MatrixGroups
open CFSG.ComponentClassification

variable {F : Type*} [Field F] [Finite F]

theorem outer_sl2_solvable (h4 : 4 ≤ Nat.card F) :
    Group.IsSolvable (OuterAutomorphisms.Outer SL(2, F)) := by
  have := sl2_isPerfect h4
  have : Group.IsSolvable
      (OuterAutomorphisms.Outer (SL(2, F) ⧸ Subgroup.center SL(2, F))) :=
    CatalogueSchreierLinearTwo.outer_solvable F
  exact OuterAutomorphisms.solvable_of_centerQuotient SL(2, F)

theorem perfect_action_inner_of_equiv_sl2 {P Q : Type*} [Group P] [Group.IsPerfect P] [Group Q]
    (h4 : 4 ≤ Nat.card F) (e : Q ≃* SL(2, F)) (ψ : P →* MulAut Q) (x : P) :
    ∃ q : Q, ψ x = MulAut.conj q := by
  have := outer_sl2_solvable (F := F) h4
  have : Group.IsSolvable (OuterAutomorphisms.Outer Q) :=
    OuterAutomorphisms.solvable_of_equiv e.symm
  exact OuterAutomorphisms.perfect_action_inner ψ x

theorem perfect_subgroup_le_range_conj (h4 : 4 ≤ Nat.card F)
    (H : Subgroup (MulAut SL(2, F))) [Group.IsPerfect H] :
    H ≤ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range := by
  intro α hα
  obtain ⟨x, hx⟩ := perfect_action_inner_of_equiv_sl2 h4 (MulEquiv.refl SL(2, F)) H.subtype
    ⟨α, hα⟩
  exact ⟨x, hx.symm⟩

theorem act_trivial_of_orderOf_eq_two (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    {P Q : Type*} [Group P] [Group Q] (eP : P ≃* SL(2, F)) (eQ : Q ≃* SL(2, F))
    (ψ : P →* MulAut Q) {x : P} (hx : orderOf x = 2) : ψ x = 1 := by
  have h4 : 4 ≤ Nat.card F := by omega
  have h3 : 3 ≤ Nat.card F := by omega
  have := isPerfect_of_equiv_sl2 h4 eP
  have hQfin : Finite Q := Finite.of_equiv _ eQ.toEquiv.symm
  have hPQ : Nat.card P = Nat.card Q :=
    Nat.card_congr (eP.toEquiv.trans eQ.toEquiv.symm)
  have hinner : ψ.range ≤ (MulAut.conj : Q →* MulAut Q).range := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨q, hq⟩ := perfect_action_inner_of_equiv_sl2 h4 eQ ψ y
    exact ⟨q, hq.symm⟩
  have hker : ψ.ker ≠ ⊥ := by
    intro hbot
    have hcard := Subgroup.card_ker_mul_card_range ψ
    rw [hbot, Subgroup.card_bot, one_mul, hPQ] at hcard
    have hle : Nat.card ψ.range ≤ Nat.card (MulAut.conj : Q →* MulAut Q).range :=
      Subgroup.card_le_of_le hinner
    have hinn := natCard_conj_range_of_equiv_sl2 hodd eQ
    have hpos : 0 < Nat.card (MulAut.conj : Q →* MulAut Q).range := Nat.card_pos
    omega
  have hcenter : Subgroup.center P ≤ ψ.ker := by
    rcases normal_cases_of_equiv_sl2 h4 eP ψ.ker inferInstance with h | h | h
    · exact absurd h hker
    · exact h.ge
    · rw [h]
      exact le_top
  have hxcenter : x ∈ Subgroup.center P := by
    rw [mem_center_iff_of_equiv_sl2 eP,
      (orderOf_eq_two_iff_of_equiv_sl2 hodd eP x).mp hx, MulEquiv.apply_symm_apply]
    exact (mem_center_sl2_iff _).mpr (Or.inr rfl)
  exact MonoidHom.mem_ker.mp (hcenter hxcenter)

end CFSG.ClassicalInvolution
