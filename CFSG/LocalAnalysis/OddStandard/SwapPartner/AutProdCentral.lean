module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProdLemmas

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

theorem card_centralizer_quotient_le {Y : Type*} [Group Y] [Finite Y] (Z : Subgroup Y)
    [Z.Normal] (c : Y) :
    Nat.card (centralizer ({(QuotientGroup.mk c : Y ⧸ Z)} : Set (Y ⧸ Z))) ≤
      Nat.card (centralizer ({c} : Set Y)) := by
  let q : Y →* Y ⧸ Z := QuotientGroup.mk' Z
  let C : Subgroup (Y ⧸ Z) := centralizer ({(QuotientGroup.mk c : Y ⧸ Z)} : Set (Y ⧸ Z))
  let P : Subgroup Y := C.comap q
  have hker : q.ker = Z := QuotientGroup.ker_mk' (N := Z)
  have hrange : C ≤ q.range := by
    rw [QuotientGroup.range_mk']
    exact le_top
  have hP : Nat.card P = Nat.card C * Nat.card Z := by
    have h := card_comap_eq_of_le_range q C hrange
    rw [hker] at h
    simpa only [P] using h
  have hmem : ∀ z ∈ P, z * c * z⁻¹ * c⁻¹ ∈ Z := by
    intro z hz
    have hzc : q z ∈ centralizer ({(QuotientGroup.mk c : Y ⧸ Z)} : Set (Y ⧸ Z)) := hz
    have hcomm : q z * (QuotientGroup.mk c : Y ⧸ Z) =
        (QuotientGroup.mk c : Y ⧸ Z) * q z := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hzc
      exact hzc
    have hq1 : q (z * c * z⁻¹ * c⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      change q z * (QuotientGroup.mk c : Y ⧸ Z) * (q z)⁻¹ *
        (QuotientGroup.mk c : Y ⧸ Z)⁻¹ = 1
      rw [hcomm]
      group
    rw [← hker, MonoidHom.mem_ker]
    exact hq1
  have hS := card_le_card_inf_centralizer_mul P Z c hmem
  have hle2 : Nat.card ↥(P ⊓ centralizer ({c} : Set Y)) * Nat.card Z ≤
      Nat.card ↥(centralizer ({c} : Set Y)) * Nat.card Z :=
    Nat.mul_le_mul_right (Nat.card Z)
      (Nat.card_le_card_of_injective
        (fun x : ↥(P ⊓ centralizer ({c} : Set Y)) =>
          (⟨(x : Y), x.2.2⟩ : ↥(centralizer ({c} : Set Y))))
        (fun _ _ hab => Subtype.ext
          (congrArg (fun y : ↥(centralizer ({c} : Set Y)) => (y : Y)) hab)))
  have hmain : Nat.card C * Nat.card Z ≤
      Nat.card (centralizer ({c} : Set Y)) * Nat.card Z := by
    rw [← hP]
    exact le_trans hS hle2
  haveI : Nonempty Z := ⟨⟨1, Z.one_mem⟩⟩
  exact Nat.le_of_mul_le_mul_right hmain Nat.card_pos

end CFSG.OddStandard.AltStdSec.SwapPartner
