module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ1Model
public import CFSG.Walter.Models

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Family CFSG.Open CFSG.Blueprint CFSG.Walter
  CFSG.Walter.J1Props

section J1

theorem walterJ1_autInner
    : ∀ φ : walterJ1 ≃* walterJ1, ∃ s : walterJ1, ∀ x, φ x = s * x * s⁻¹ := by
  intro φ
  obtain ⟨x, hx⟩ := CFSG.QuasithinUnique.K1.autInner_walterJ1 φ
  exact ⟨x⁻¹, fun y => by rw [hx y, inv_inv]⟩

theorem walterJ1_elemAbelian_le :
    ∀ B : Subgroup walterJ1, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ 3 := by
  intro B _ hB
  have : Finite walterJ1 := Nat.finite_of_card_ne_zero (by rw [J1_card]; norm_num)
  exact card_le_of_exponent_two (a := 3) (m := 3 * 5 * 7 * 11 * 19)
    (by rw [J1_card]; ring) (by decide) B hB

theorem walterJ1_dihedral :
    ∀ t : walterJ1, t * t = 1 → t ≠ 1 → ∃ c : walterJ1, orderOf (t * (c * t * c⁻¹)) = 19 := by
  intro t ht2 ht1
  have hp19 : (19 = 3 ∨ 19 = 5 ∨ 19 = 7 ∨ 19 = 11 ∨ 19 = 19 : Prop) := by norm_num
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨hix, hixy⟩ := iJ_inv (p := 19) hp19
  have hy := orderOf_yJ (p := 19) hp19
  have hord2 : orderOf t = 2 :=
    orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  obtain ⟨h, hh⟩ := isConj_iff.1 (J1_isConj_involutions hix hord2)
  have hx2 : iJ 19 * iJ 19 = 1 := by
    have := pow_orderOf_eq_one (iJ 19)
    rwa [hix, sq] at this
  have hxinv : (iJ 19)⁻¹ = iJ 19 := inv_eq_of_mul_eq_one_right hx2
  have hxyx : iJ 19 * yJ 19 * iJ 19 = (yJ 19)⁻¹ := by
    have := hixy
    rwa [hxinv] at this
  refine ⟨h * yJ 19 * h⁻¹, ?_⟩
  have hprod : t * ((h * yJ 19 * h⁻¹) * t * (h * yJ 19 * h⁻¹)⁻¹) =
      h * ((yJ 19)⁻¹ * (yJ 19)⁻¹) * h⁻¹ := by
    rw [← hh]
    calc h * iJ 19 * h⁻¹ * (h * yJ 19 * h⁻¹ * (h * iJ 19 * h⁻¹) * (h * yJ 19 * h⁻¹)⁻¹)
        = h * (iJ 19 * yJ 19 * iJ 19 * (yJ 19)⁻¹) * h⁻¹ := by group
      _ = h * ((yJ 19)⁻¹ * (yJ 19)⁻¹) * h⁻¹ := by rw [hxyx]
  rw [hprod, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have h1 : (yJ 19)⁻¹ * (yJ 19)⁻¹ = (yJ 19 ^ 2)⁻¹ := by group
  rw [h1, orderOf_inv, orderOf_pow' _ (by norm_num), hy]
  norm_num

theorem j1_weight_le
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (e : CQ L ≃* NativeSporadic.Carrier .J1)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E) :
    64 * (Nat.card E * Nat.card (fixV E)) ≤ Nat.card W := by
  have e' : CQ L ≃* walterJ1 := e.trans walterJ1EquivNative.symm
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have h := exclusion_of_autInner_le hW hperf hirr hE hEne hEel e' walterJ1_autInner
    (r := 3) (ρ := 9) (by norm_num) walterJ1_elemAbelian_le
    (rank_of_dihedral hW hirr e' (ρ := 9) (p := 19) (by norm_num)
      (by norm_num [orderOf_two_zmod_19]) walterJ1_dihedral)
  simpa using h

theorem j1ExclusionProp : J1ExclusionProp := by
  intro W _ _ hW L E hperf hirr ⟨e⟩ hE hEne hEel
  have h := j1_weight_le hW hperf hirr e hE hEne hEel
  have hpos : 0 < Nat.card E * Nat.card (fixV E) := Nat.mul_pos Nat.card_pos Nat.card_pos
  omega

end J1

end CFSG.QuasithinUnique.Setup.X1
