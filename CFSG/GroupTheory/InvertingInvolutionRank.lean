module

public import CFSG.GroupTheory.FixedPointFreeFiveTwist
public import CFSG.Quasithin.Background.SimsE2DihMod
public import CFSG.CGT.PushingUpLit.CGT6.EmbCommV

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

theorem normalizes_zpowers_of_conj_mem {G : Type*} [Group G] {y c : G}
    (h : c * y * c⁻¹ ∈ Subgroup.zpowers y) :
    ∀ x ∈ Subgroup.zpowers y, c * x * c⁻¹ ∈ Subgroup.zpowers y := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ h k

theorem rk_eq_two_mul_rk_fix_of_inverting [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {y c : MulAut W} (hc2 : c * c = 1) (hcy : c * y * c⁻¹ = y⁻¹) (hy : Odd (orderOf y))
    {U : Subgroup W} (hUy : ∀ u ∈ U, y u ∈ U) (hUc : ∀ u ∈ U, c u ∈ U)
    (hfix : ∀ u ∈ U, y u = u → u = 1) :
    rk ↥U = 2 * rk ↥(U ⊓ SimsE2.Dih.fixSub c) := by
  have hcomm : ∀ a b : W, a * b = b * a := fun a b => mul_comm a b
  have hsq : ∀ a : W, a * a = 1 := fun a => by rw [← pow_two]; exact hW a
  set A : Subgroup W := U ⊓ SimsE2.Dih.fixSub c with hA
  have ha : Nat.card U ≤ Nat.card A ^ 2 :=
    SimsE2.Dih.card_le_sq_card_fixSub hcomm hsq hc2 hUc
  let B : Subgroup W := A.map y.toMonoidHom
  have hBU : B ≤ U := by
    rintro _ ⟨a, ha, rfl⟩
    exact hUy a ha.1
  obtain ⟨k, hk⟩ := hy
  have hy1 : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
  have hyeq : (y * y) ^ (k + 1) = y := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hy1,
      one_mul]
  have hAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, a, haA, rfl⟩
    have hxc : c (y a) = y a := hxA.2
    have hca : c a = a := haA.2
    have h1 : c (y a) = y⁻¹ a := by
      have e : (c * y * c⁻¹) (c a) = c (y a) := by
        simp [MulAut.mul_apply]
      rw [← e, hcy, hca]
    have h2 : (y * y) a = a := by
      have e1 : y a = y⁻¹ a := hxc.symm.trans h1
      rw [MulAut.mul_apply, e1]
      simp
    have hya : y a = a := by
      calc y a = ((y * y) ^ (k + 1)) a := by rw [hyeq]
        _ = a := SimsE2.Dih.pow_apply_eq h2 (k + 1)
    have ha1 : a = 1 := hfix a haA.1 hya
    rw [Subgroup.mem_bot]
    show y a = 1
    rw [ha1, map_one]
  have hBcard : Nat.card B = Nat.card A := Subgroup.card_map_of_injective y.injective
  have hb : Nat.card A * Nat.card B ≤ Nat.card U :=
    SimsE2.Dih.card_mul_card_le inf_le_left hBU hAB
  have heq : Nat.card U = Nat.card A ^ 2 := by
    rw [hBcard] at hb
    rw [sq] at ha ⊢
    exact le_antisymm ha hb
  rw [card_eq_two_pow hW U, card_eq_two_pow hW A, ← pow_mul] at heq
  have := Nat.pow_right_injective (le_refl 2) heq
  omega

theorem eight_dvd_rk_of_inverting [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {y c f : MulAut W} (hc2 : c * c = 1) (hcy : c * y * c⁻¹ = y⁻¹) (hy : Odd (orderOf y))
    (hf5 : f ^ 5 = 1) (hffix : fixV (Subgroup.zpowers f) = ⊥) (hfc : f * c = c * f)
    {U : Subgroup W} (hUy : ∀ u ∈ U, y u ∈ U) (hUc : ∀ u ∈ U, c u ∈ U)
    (hUf : ∀ u ∈ U, f u ∈ U) (hfix : ∀ u ∈ U, y u = u → u = 1) : 8 ∣ rk ↥U := by
  rw [rk_eq_two_mul_rk_fix_of_inverting hW hc2 hcy hy hUy hUc hfix]
  have h4 : 4 ∣ rk ↥(U ⊓ SimsE2.Dih.fixSub c) := by
    apply CFSG.GroupTheory.four_dvd_rk_of_invariant hW hf5 hffix
    intro u hu
    refine ⟨hUf u hu.1, ?_⟩
    have hcu : c u = u := hu.2
    show c (f u) = f u
    calc c (f u) = (c * f) u := rfl
      _ = (f * c) u := by rw [hfc]
      _ = f (c u) := rfl
      _ = f u := by rw [hcu]
  obtain ⟨k, hk⟩ := h4
  exact ⟨k, by omega⟩

theorem rk_commV_conj_comm_le [Finite W] {φ x y : MulAut W} (hy : y = x⁻¹ * (φ * x * φ⁻¹)) :
    rk ↥(commV (Subgroup.zpowers y)) ≤ 2 * rk ↥(commV (Subgroup.zpowers φ)) := by
  let u : MulAut W := x⁻¹ * φ * x⁻¹⁻¹
  have hyu : y = u * φ⁻¹ := by
    simp only [u, hy]
    group
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers φ⁻¹ := by
    rw [Subgroup.zpowers_le, hyu]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers u) (Subgroup.mem_zpowers φ⁻¹)
  have hcommle : commV (Subgroup.zpowers y) ≤
      commV (Subgroup.zpowers u) ⊔ commV (Subgroup.zpowers φ⁻¹) :=
    (CFSG.CGT.PushingUpLit.CGT6.commV_mono hle).trans
      (CFSG.CGT.PushingUpLit.CGT6.commV_sup_le _ _)
  have hru : rk (commV (Subgroup.zpowers u)) = rk (commV (Subgroup.zpowers φ)) := by
    rw [show u = x⁻¹ * φ * x⁻¹⁻¹ from rfl, CFSG.Quasithin.commV_zpowers_conj_eq φ x⁻¹]
    unfold rk
    rw [Subgroup.card_map_of_injective (MulEquiv.injective x⁻¹)]
  have hrv : rk (commV (Subgroup.zpowers φ⁻¹)) = rk (commV (Subgroup.zpowers φ)) := by
    rw [Subgroup.zpowers_inv]
  have h1 : rk (commV (Subgroup.zpowers y)) ≤
      rk ↥(commV (Subgroup.zpowers u) ⊔ commV (Subgroup.zpowers φ⁻¹)) :=
    CFSG.Quasithin.rk_mono (G := W) hcommle
  have hsum := CFSG.Quasithin.rk_sup_add_rk_inf
    (commV (Subgroup.zpowers u)) (commV (Subgroup.zpowers φ⁻¹))
  omega

end CFSG.GroupTheory
