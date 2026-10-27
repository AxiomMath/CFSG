module

public import CFSG.LargeExtraspecial.DW4Stmt
public import CFSG.LargeExtraspecial.DWW4ThmA
public import CFSG.LargeExtraspecial.D73Main
public import CFSG.LargeExtraspecial.GLW4Order
public import CFSG.CGT.Timmesfeld75.FinalNodeRest
public import CFSG.CGT.A8S.Final
public import CFSG.CGT.M24S.Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Matrix Subgroup CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

@[expose] def DW41WidthFourStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G)),
    S.width = 4 → (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A) →
    (∃ g₀ : G, g₀ * S.z * g₀⁻¹ ∈ A ∧ g₀ * S.z * g₀⁻¹ ≠ S.z) → SpConfig S A hM → False

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem two_pow_fifteen_dvd_card_of_Mbar_mulEquiv (hw : S.width = 4)
    (h : Nonempty (S.Mbar ≃* GL (Fin S.width) (ZMod 2))) : 2 ^ 15 ∣ Nat.card G := by
  obtain ⟨e⟩ := h
  have hGL : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
    rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
    norm_num
  have hM := GLW4.card_M_eq (S := S)
  rw [S.card_Q_eq, Nat.card_congr e.toEquiv, hw, hGL] at hM
  have hdvd : 2 ^ 15 ∣ Nat.card S.M := by
    rw [hM]
    norm_num
  exact hdvd.trans (Subgroup.card_subgroup_dvd_card S.M)

section CaseI


theorem nonempty_mulEquiv_SL_six_of_caseI (hNode : NodeStatement) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] {S : Setting G} (hw : S.width = 4) {A : Subgroup G}
    [IsElementaryAbelian 2 A] (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G)) {h : G}
    (hhQ : h * S.z * h⁻¹ ∈ S.QG) (hhA : h * S.z * h⁻¹ ∉ A) :
    Nonempty (G ≃* SL(S.width + 2, ZMod 2)) := by
  have hexp : (S.width + 2) * (S.width + 2 - 1) / 2 = 15 := by
    rw [hw]
  have h2 : 2 ^ ((S.width + 2) * (S.width + 2 - 1) / 2) ∣ Nat.card G := by
    have h := two_pow_fifteen_dvd_card_of_Mbar_mulEquiv hw
      (hA.nonempty_Mbar_mulEquiv_of_not_mem hM hhQ hhA)
    rwa [hexp]
  have hnab : ∃ a b : G, a * b ≠ b * a :=
    ⟨h, S.z, fun hc => hhA (by rw [hc, mul_assoc, mul_inv_cancel, mul_one]; exact hA.z_mem)⟩
  exact D73.nonempty_mulEquiv_SL_of_maxEA hNode hnab (by omega) h2 S (by omega) hA hM hhQ hhA

theorem nonempty_mulEquiv_SL_six_of_caseIIG (hNode : NodeStatement) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] {S : Setting G} (hnab : ∃ a b : G, a * b ≠ b * a)
    (hw : S.width = 4) {A : Subgroup G} [IsElementaryAbelian 2 A] (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G))
    (hi : A ≤ closure {d : G | d ∈ A ∧ ∃ g : G, g * S.z * g⁻¹ = d})
    (hii : ∀ g : G, g * S.z * g⁻¹ ∈ A → A ≤ S.Qa g) :
    Nonempty (G ≃* SL(S.width + 2, ZMod 2)) := by
  have hsurj := hA.conjLinear_surjective_of_conj hi hii
  have hti : ∀ g : G, A ⊓ conjSubgroup g⁻¹ A = ⊥ ∨ A ⊓ conjSubgroup g⁻¹ A = A :=
    D73.isTI_of_transitive hM (D73.MaxEA.transitive_of_surjective hA hsurj)
  have hC : centralizer (A : Set G) = A := hA.centralizer_eq hM
  have hsub : (S.width + 2) - 1 = S.width + 1 := by omega
  have hcard : Nat.card A = 2 ^ ((S.width + 2) - 1) := by
    rw [hA.card_eq, hsub]
  have hexp : (S.width + 2) * (S.width + 2 - 1) / 2 = 15 := by
    rw [hw]
  have h2 : 2 ^ ((S.width + 2) * (S.width + 2 - 1) / 2) ∣ Nat.card G := by
    have h := two_pow_fifteen_dvd_card_of_Mbar_mulEquiv hw (hA.nonempty_Mbar_mulEquiv hM hsurj)
    rwa [hexp]
  exact D73.nonempty_mulEquiv_SL_of_ti hNode hnab (by omega) A hcard hC hti h2

end CaseI

theorem dw37WidthFourStatement_of_dw41
    (hNode : NodeStatement) (hSp : DW41WidthFourStatement) :
    DW37WidthFourStatement := by
  intro G _ _ _ S g hw hgQ hgz hred
  obtain ⟨A, hEA, hA, hM⟩ := W4Rank.theoremAWidthFour_holds G S hw ⟨g, hgQ, hgz⟩ hred
  haveI : IsElementaryAbelian 2 A := hEA
  have hnab : ∃ a b : G, a * b ≠ b * a :=
    ⟨g, S.z, fun hc => hgz (by rw [hc, mul_assoc, mul_inv_cancel, mul_one])⟩
  by_cases hcase : ∃ h : G, h * S.z * h⁻¹ ∈ S.QG ∧ h * S.z * h⁻¹ ∉ A
  · obtain ⟨h, hhQ, hhA⟩ := hcase
    exact DW.nonempty_mulEquiv_psl (nonempty_mulEquiv_SL_six_of_caseI hNode hw hA hM hhQ hhA)
  · push Not at hcase
    rcases hA.caseII_dichotomy (by omega : 4 ≤ S.width) hM hcase (hcase g hgQ) hgz with hG | hSp'
    · obtain ⟨hi, hii⟩ := hG
      exact DW.nonempty_mulEquiv_psl
        (nonempty_mulEquiv_SL_six_of_caseIIG hNode hnab hw hA hM hi hii)
    · exact (hSp G S A hA hM hw hcase ⟨g, hcase g hgQ, hgz⟩ hSp').elim

theorem dw37WidthFourStatement_of_dw41'
    (hSp : DW41WidthFourStatement) :
    DW37WidthFourStatement :=
  dw37WidthFourStatement_of_dw41
    (CFSG.CGT.Timmesfeld75.node_final_rest
      ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩) hSp

end CFSG.LargeExtraspecial.DW
