module

public import CFSG.ClassicalInvolution.Q3.Q3CLBasic
import CFSG.ClassicalInvolution.Q3.Q3T8AF01
public import CFSG.ClassicalInvolution.AschTight.Sec7L76A

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Odd

variable {G : Type} [Group G]

theorem exists_fixed_conj_of_isPGroup [Finite G] {O R : Subgroup G} {t : G} (ht : t * t = 1)
    (hodd : Odd (Nat.card O)) (hR : IsPGroup 2 R)
    (hRn : ∀ r ∈ R, ∀ o ∈ O, r * o * r⁻¹ ∈ O) (hrt : ∀ r ∈ R, t⁻¹ * (r * t * r⁻¹) ∈ O) :
    ∃ o ∈ O, ∀ r ∈ R, r * (o * t * o⁻¹) * r⁻¹ = o * t * o⁻¹ :=
  CFSG.ClassicalInvolution.Q3.Q3T8.AF.exists_fixed_conj_of_isPGroup ht hodd hR hRn hrt

end Odd

section Nbr

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_common_nbr_conj (hΩ : HypOmegaGen Ω) {A B M : Subgroup G} (hA : A ∈ Ω)
    (hB : B ∈ Ω) (hM : M ∈ Ω) {zM : G} (hzM : IsUniqueInvolution M zM) {Ra Rb : Subgroup G}
    (hRa : Ra ∈ RSet Ω) (hRaA : Ra ≤ A) (hRb : Rb ∈ RSet Ω) (hRbB : Rb ≤ B)
    (hE : IsPGroup 2 ↥(Ra ⊔ Rb)) {O : Subgroup G} (hodd : Odd (Nat.card O))
    (hOn : ∀ e ∈ Ra ⊔ Rb, ∀ o ∈ O, e * o * e⁻¹ ∈ O)
    (hca : ∀ r ∈ Ra, zM⁻¹ * (r * zM * r⁻¹) ∈ O) (hcb : ∀ r ∈ Rb, zM⁻¹ * (r * zM * r⁻¹) ∈ O)
    (hMA : ∀ o ∈ O, conjSub o M ≠ A) (hMB : ∀ o ∈ O, conjSub o M ≠ B) :
    ∃ o ∈ O, conjSub o M ∈ omegaNbr Ω A ∧ conjSub o M ∈ omegaNbr Ω B := by
  have hrt : ∀ r ∈ Ra ⊔ Rb, zM⁻¹ * (r * zM * r⁻¹) ∈ O := by
    intro e he
    have he' := he
    rw [Subgroup.sup_eq_closure] at he'
    induction he' using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hca x hx
      · exact hcb x hx
    | one => simp
    | mul x y hxm hym ihx ihy =>
      have hxE : x ∈ Ra ⊔ Rb := by rw [Subgroup.sup_eq_closure]; exact hxm
      have hyE : y ∈ Ra ⊔ Rb := by rw [Subgroup.sup_eq_closure]; exact hym
      have e : zM⁻¹ * (x * y * zM * (x * y)⁻¹) =
          (zM⁻¹ * (x * zM * x⁻¹)) * (x * (zM⁻¹ * (y * zM * y⁻¹)) * x⁻¹) := by group
      rw [e]
      exact O.mul_mem (ihx hxE) (hOn x hxE _ (ihy hyE))
    | inv x hxm ihx =>
      have hxE : x ∈ Ra ⊔ Rb := by rw [Subgroup.sup_eq_closure]; exact hxm
      have e : zM⁻¹ * (x⁻¹ * zM * x⁻¹⁻¹) = (x⁻¹ * (zM⁻¹ * (x * zM * x⁻¹)) * x⁻¹⁻¹)⁻¹ := by
        group
      rw [e]
      exact O.inv_mem (hOn x⁻¹ ((Ra ⊔ Rb).inv_mem hxE) _ (ihx hxE))
  obtain ⟨o, hoO, hfix⟩ := exists_fixed_conj_of_isPGroup hzM.sq hodd hE hOn hrt
  have hM' : conjSub o M ∈ Ω := hΩ.conjInvariant o M hM
  have hz' : IsUniqueInvolution (conjSub o M) (o * zM * o⁻¹) := hzM.conj o
  have hcent : ∀ R : Subgroup G, R ≤ Ra ⊔ Rb →
      R ≤ Subgroup.centralizer ({o * zM * o⁻¹} : Set G) := by
    intro R hR r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hfix r (hR hr)
    calc r * (o * zM * o⁻¹) = r * (o * zM * o⁻¹) * r⁻¹ * r := by group
      _ = (o * zM * o⁻¹) * r := by rw [h]
  refine ⟨o, hoO, ?_, ?_⟩
  · have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRa
    have hN := Sec6Gen.le_normalizer_of_le_centralizer hΩ hM' hA (hMA o hoO) hz' hRaA
      (Sec7.isPGroup_of_mem_RSet hRa) (by omega) (hcent Ra le_sup_left)
    exact Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hM' hA
      ⟨hA, (hMA o hoO).symm, Ra, hRa, hRaA, hN⟩
  · have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRb
    have hN := Sec6Gen.le_normalizer_of_le_centralizer hΩ hM' hB (hMB o hoO) hz' hRbB
      (Sec7.isPGroup_of_mem_RSet hRb) (by omega) (hcent Rb le_sup_right)
    exact Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hM' hB
      ⟨hB, (hMB o hoO).symm, Rb, hRb, hRbB, hN⟩

theorem exists_nbr_conj (hΩ : HypOmegaGen Ω) {A M : Subgroup G} (hA : A ∈ Ω) (hM : M ∈ Ω)
    {zM : G} (hzM : IsUniqueInvolution M zM) {Ra : Subgroup G} (hRa : Ra ∈ RSet Ω)
    (hRaA : Ra ≤ A) {O : Subgroup G} (hodd : Odd (Nat.card O))
    (hOn : ∀ e ∈ Ra, ∀ o ∈ O, e * o * e⁻¹ ∈ O)
    (hca : ∀ r ∈ Ra, zM⁻¹ * (r * zM * r⁻¹) ∈ O) (hMA : ∀ o ∈ O, conjSub o M ≠ A) :
    ∃ o ∈ O, conjSub o M ∈ omegaNbr Ω A := by
  have hE : IsPGroup 2 ↥(Ra ⊔ Ra) := by
    rw [sup_idem]
    exact Sec7.isPGroup_of_mem_RSet hRa
  obtain ⟨o, ho, h1, -⟩ := exists_common_nbr_conj hΩ hA hA hM hzM hRa hRaA hRa hRaA hE hodd
    (by rw [sup_idem]; exact hOn) hca hca hMA hMA
  exact ⟨o, ho, h1⟩

end Nbr

end CFSG.ClassicalInvolution.Hat2A7S8
