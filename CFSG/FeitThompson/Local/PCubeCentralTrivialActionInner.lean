module

public import CFSG.FeitThompson.Local.PrimeCubeNonabelianCommutatorCentre
public import CFSG.FeitThompson.Foundations.MinimalNormalInFittingCenter
import Mathlib.Data.Rat.Floor

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise
open scoped commutatorElement

variable {p : ℕ} {R : Type*} [Group R] {B : Subgroup R}

private theorem finite_of_card_eq_prime_cube {G : Type*} (hp : p.Prime)
    (hG : Nat.card G = p ^ 3) : Finite G :=
  Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero _ hp.ne_zero)

theorem closure_pair_eq_top_of_mul_ne_mul {G : Type*} [Group G] (hp : p.Prime)
    (hG : Nat.card G = p ^ 3) {x y : G} (hxy : x * y ≠ y * x) : closure {x, y} = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite G := finite_of_card_eq_prime_cube hp hG
  set S := closure ({x, y} : Set G) with hS
  have hxS : x ∈ S := subset_closure (by simp)
  have hyS : y ∈ S := subset_closure (by simp)
  have hncS : ¬ IsMulCommutative S := fun hcS =>
    hxy (by simpa using congrArg Subtype.val (isMulCommutative_iff.mp hcS ⟨x, hxS⟩ ⟨y, hyS⟩))
  obtain ⟨k, hk3, hkc⟩ := (Nat.dvd_prime_pow hp).mp (hG ▸ S.card_subgroup_dvd_card)
  interval_cases k
  · have hbot : S = ⊥ := Subgroup.card_eq_one.mp (by simpa using hkc)
    rw [hbot] at hxS
    exact absurd (by rw [Subgroup.mem_bot.mp hxS]; simp) hxy
  · have : IsCyclic S := isCyclic_of_prime_card (by simpa using hkc)
    exact absurd (IsCyclic.isMulCommutative (α := S)) hncS
  · exact absurd (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hkc) hncS
  · exact Subgroup.eq_top_of_card_eq _ (by rw [hkc, hG])

theorem closure_pair_eq_of_mul_ne_mul (hp : p.Prime) (hB : Nat.card ↥B = p ^ 3) {x y : R}
    (hx : x ∈ B) (hy : y ∈ B) (hxy : x * y ≠ y * x) : closure ({x, y} : Set R) = B := by
  have hxy' : (⟨x, hx⟩ : ↥B) * ⟨y, hy⟩ ≠ ⟨y, hy⟩ * ⟨x, hx⟩ := by
    simpa [Subtype.ext_iff] using hxy
  calc closure ({x, y} : Set R)
      = (closure ({(⟨x, hx⟩ : ↥B), ⟨y, hy⟩} : Set ↥B)).map B.subtype := by
        rw [MonoidHom.map_closure]; congr 1; rw [Subgroup.coe_subtype, Set.image_pair]
    _ = (⊤ : Subgroup ↥B).map B.subtype := by
        rw [closure_pair_eq_top_of_mul_ne_mul hp hB hxy']
    _ = B := by rw [← MonoidHom.range_eq_map, Subgroup.subtype_range]

theorem exists_mul_ne_mul_of_not_isMulCommutative {G : Type*} [Group G]
    (hnab : ¬ IsMulCommutative G) : ∃ x y : G, x * y ≠ y * x := by
  by_contra h
  exact hnab (isMulCommutative_iff.mpr (by simpa using h))

theorem center_eq_zpowers_commutatorElement {G : Type*} [Group G] (hp : p.Prime)
    (hG : Nat.card G = p ^ 3) (hnab : ¬ IsMulCommutative G) {x y : G} (hxy : x * y ≠ y * x) :
    center G = zpowers ⁅x, y⁆ := by
  have : Finite G := finite_of_card_eq_prime_cube hp hG
  have hZ : Nat.card (center G) = p := card_center_of_card_eq_prime_cube hp hG hnab
  have hmem : ⁅x, y⁆ ∈ center G := by
    rw [← commutator_eq_center_of_card_eq_prime_cube hp hG hnab, commutator_def]
    exact Subgroup.commutator_mem_commutator (mem_top x) (mem_top y)
  have hne : ⁅x, y⁆ ≠ 1 := fun h => hxy (commutatorElement_eq_one_iff_commute.mp h).eq
  refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hmem) ?_).symm
  rcases (Nat.dvd_prime hp).mp (hZ ▸ Subgroup.card_dvd_of_le (zpowers_le.mpr hmem)) with h | h
  · exact absurd (by simpa using Subgroup.card_eq_one.mp h) hne
  · rw [h, hZ]

theorem map_center_subtype_eq_zpowers (hp : p.Prime) (hB : Nat.card ↥B = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥B) {x y : R} (hx : x ∈ B) (hy : y ∈ B) (hxy : x * y ≠ y * x) :
    (center ↥B).map B.subtype = zpowers ⁅x, y⁆ := by
  have hxy' : (⟨x, hx⟩ : ↥B) * ⟨y, hy⟩ ≠ ⟨y, hy⟩ * ⟨x, hx⟩ := by
    simpa [Subtype.ext_iff] using hxy
  rw [center_eq_zpowers_commutatorElement hp hB hnab hxy', MonoidHom.map_zpowers,
    map_commutatorElement]
  rfl

section Weak

variable (hBR : ⁅B, (⊤ : Subgroup R)⁆ ≤ (center ↥B).map B.subtype)

include hBR

theorem commutatorElement_mem_map_center {b : R} (hb : b ∈ B) (r : R) :
    ⁅b, r⁆ ∈ (center ↥B).map B.subtype :=
  hBR (Subgroup.commutator_mem_commutator hb (mem_top r))

theorem commutatorElement_mem_of_mem {b : R} (hb : b ∈ B) (r : R) : ⁅b, r⁆ ∈ B := by
  have := commutatorElement_mem_map_center hBR hb r
  rw [map_center_subtype_eq_inf_centralizer, mem_inf] at this
  exact this.1

theorem normal_of_commutator_le_map_center : B.Normal :=
  Subgroup.commutator_top_right_le_iff.mp fun _ hg => by
    rw [map_center_subtype_eq_inf_centralizer] at hBR; exact (mem_inf.mp (hBR hg)).1

theorem commute_commutatorElement_of_mem {b : R} (hb : b ∈ B) (r : R) {b' : R} (hb' : b' ∈ B) :
    Commute ⁅b, r⁆ b' := by
  have := commutatorElement_mem_map_center hBR hb r
  rw [map_center_subtype_eq_inf_centralizer, mem_inf, mem_centralizer_iff] at this
  exact (this.2 b' hb').symm

def commutatorHomLeft (r : R) : ↥B →* R :=
  MonoidHom.mk' (fun b => ⁅(b : R), r⁆) fun a b => by
    rw [Subgroup.coe_mul, commutatorElement_mul_left_eq_conj_mul,
      ← (commute_commutatorElement_of_mem hBR b.2 r a.2).eq, mul_inv_cancel_right,
      (commute_commutatorElement_of_mem hBR b.2 r
        (commutatorElement_mem_of_mem hBR a.2 r)).eq]

theorem commutatorHomLeft_apply (r : R) (b : ↥B) :
    commutatorHomLeft hBR r b = ⁅(b : R), r⁆ := (rfl)

theorem map_commutator_subtype_le_center : (commutator ↥B).map B.subtype ≤ center R := by
  rintro g ⟨b, hb, rfl⟩
  rw [mem_center_iff]
  intro r
  have hker : commutator ↥B ≤ (commutatorHomLeft hBR r).ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ c _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorHomLeft_apply,
      commutatorHomLeft_apply]
    exact (commute_commutatorElement_of_mem hBR a.2 r
      (commutatorElement_mem_of_mem hBR c.2 r)).commutator_eq
  have h1 : ⁅(b : R), r⁆ = 1 := by
    have := hker hb
    rwa [MonoidHom.mem_ker, commutatorHomLeft_apply] at this
  exact ((commutatorElement_eq_one_iff_commute.mp h1).symm).eq

theorem commutatorElement_mem_center (hp : p.Prime) (hB : Nat.card ↥B = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥B) {b : R} (hb : b ∈ B) (r : R) : ⁅b, r⁆ ∈ center R := by
  refine map_commutator_subtype_le_center hBR ?_
  rw [commutator_eq_center_of_card_eq_prime_cube hp hB hnab]
  exact commutatorElement_mem_map_center hBR hb r

end Weak

section Strong

variable (hcz : ∀ b ∈ B, ∀ r : R, ⁅b, r⁆ ∈ center R)

include hcz

def commutatorHomRight {b : R} (hb : b ∈ B) : R →* R :=
  MonoidHom.mk' (fun r => ⁅b, r⁆) fun r s => by
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅b, r⁆,
      mem_center_iff.mp (hcz b hb s) r, ← mul_assoc, mul_inv_cancel_right]

theorem commutatorHomRight_apply {b : R} (hb : b ∈ B) (r : R) :
    commutatorHomRight hcz hb r = ⁅b, r⁆ := (rfl)

theorem commutatorElement_mul_right_of_mem {b : R} (hb : b ∈ B) (r s : R) :
    ⁅b, r * s⁆ = ⁅b, r⁆ * ⁅b, s⁆ := by
  simpa [commutatorHomRight_apply] using (commutatorHomRight hcz hb).map_mul r s

theorem commutatorElement_inv_right_of_mem {b : R} (hb : b ∈ B) (r : R) :
    ⁅b, r⁻¹⁆ = ⁅b, r⁆⁻¹ := by
  simpa [commutatorHomRight_apply] using (commutatorHomRight hcz hb).map_inv r

theorem commutatorElement_zpow_right_of_mem {b : R} (hb : b ∈ B) (r : R) (n : ℤ) :
    ⁅b, r ^ n⁆ = ⁅b, r⁆ ^ n := by
  simpa [commutatorHomRight_apply] using (commutatorHomRight hcz hb).map_zpow r n

theorem commutatorElement_zpow_mul_zpow_left {x y : R} (hx : x ∈ B) (i j : ℤ) :
    ⁅x, x ^ (-j) * y ^ i⁆ = ⁅x, y⁆ ^ i := by
  rw [commutatorElement_mul_right_of_mem hcz hx, commutatorElement_zpow_right_of_mem hcz hx,
    commutatorElement_zpow_right_of_mem hcz hx, commutatorElement_self, one_zpow, one_mul]

theorem commutatorElement_zpow_mul_zpow_right {x y : R} (hy : y ∈ B) (i j : ℤ) :
    ⁅y, x ^ (-j) * y ^ i⁆ = ⁅x, y⁆ ^ j := by
  rw [commutatorElement_mul_right_of_mem hcz hy, commutatorElement_zpow_right_of_mem hcz hy,
    commutatorElement_zpow_right_of_mem hcz hy, commutatorElement_self, one_zpow, mul_one,
    zpow_neg, ← inv_zpow, commutatorElement_inv]

theorem commute_of_commutatorElement_eq {b : R} (hb : b ∈ B) {r u : R} (h : ⁅b, r⁆ = ⁅b, u⁆) :
    Commute b (r * u⁻¹) := by
  refine commutatorElement_eq_one_iff_commute.mp ?_
  rw [commutatorElement_mul_right_of_mem hcz hb, commutatorElement_inv_right_of_mem hcz hb, h,
    mul_inv_cancel]

theorem mem_centralizer_of_commutatorElement_eq {x y : R} (hx : x ∈ B) (hy : y ∈ B)
    (hgen : closure ({x, y} : Set R) = B) {r u : R} (hxru : ⁅x, r⁆ = ⁅x, u⁆)
    (hyru : ⁅y, r⁆ = ⁅y, u⁆) : r * u⁻¹ ∈ centralizer (B : Set R) := by
  rw [← hgen, Subgroup.centralizer_closure, mem_centralizer_iff]
  intro g hg
  rcases hg with rfl | hg
  · exact (commute_of_commutatorElement_eq hcz hx hxru).eq
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (commute_of_commutatorElement_eq hcz hy hyru).eq

end Strong

theorem exists_mem_mul_mem_centralizer (hp : p.Prime) (hB : Nat.card ↥B = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥B)
    (hBR : ⁅B, (⊤ : Subgroup R)⁆ ≤ (center ↥B).map B.subtype) (r : R) :
    ∃ b ∈ B, ∃ c ∈ centralizer (B : Set R), r = b * c := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy'⟩ := exists_mul_ne_mul_of_not_isMulCommutative hnab
  have hxy : x * y ≠ y * x := by simpa [Subtype.ext_iff] using hxy'
  have hgen : closure ({x, y} : Set R) = B := closure_pair_eq_of_mul_ne_mul hp hB hx hy hxy
  have hZ : (center ↥B).map B.subtype = zpowers ⁅x, y⁆ :=
    map_center_subtype_eq_zpowers hp hB hnab hx hy hxy
  have hcz : ∀ b ∈ B, ∀ r : R, ⁅b, r⁆ ∈ center R := fun b hb r =>
    commutatorElement_mem_center hBR hp hB hnab hb r
  obtain ⟨i, hi⟩ : ∃ i : ℤ, ⁅x, y⁆ ^ i = ⁅x, r⁆ :=
    Subgroup.mem_zpowers_iff.mp (hZ ▸ commutatorElement_mem_map_center hBR hx r)
  obtain ⟨j, hj⟩ : ∃ j : ℤ, ⁅x, y⁆ ^ j = ⁅y, r⁆ :=
    Subgroup.mem_zpowers_iff.mp (hZ ▸ commutatorElement_mem_map_center hBR hy r)
  set u : R := x ^ (-j) * y ^ i with hu
  have huB : u ∈ B := B.mul_mem (B.zpow_mem hx _) (B.zpow_mem hy _)
  have hxu : ⁅x, r⁆ = ⁅x, u⁆ := by
    rw [hu, commutatorElement_zpow_mul_zpow_left hcz hx i j, hi]
  have hyu : ⁅y, r⁆ = ⁅y, u⁆ := by
    rw [hu, commutatorElement_zpow_mul_zpow_right hcz hy i j, hj]
  have hc : r * u⁻¹ ∈ centralizer (B : Set R) :=
    mem_centralizer_of_commutatorElement_eq hcz hx hy hgen hxu hyu
  refine ⟨u, huB, r * u⁻¹, hc, ?_⟩
  rw [mem_centralizer_iff.mp hc u huB]
  group

theorem sup_centralizer_eq_top (hp : p.Prime) (hB : Nat.card ↥B = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥B)
    (hBR : ⁅B, (⊤ : Subgroup R)⁆ ≤ (center ↥B).map B.subtype) :
    B ⊔ centralizer (B : Set R) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro r
  obtain ⟨b, hb, c, hcm, rfl⟩ := exists_mem_mul_mem_centralizer hp hB hnab hBR r
  exact Subgroup.mul_mem _ (le_sup_left (α := Subgroup R) hb)
    (le_sup_right (α := Subgroup R) hcm)

theorem coe_mul_coe_centralizer_eq_univ (hp : p.Prime) (hB : Nat.card ↥B = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥B)
    (hBR : ⁅B, (⊤ : Subgroup R)⁆ ≤ (center ↥B).map B.subtype) :
    (B : Set R) * (centralizer (B : Set R) : Set R) = Set.univ := by
  ext r
  simp only [Set.mem_univ, iff_true, Set.mem_mul]
  obtain ⟨b, hb, c, hcm, rfl⟩ := exists_mem_mul_mem_centralizer hp hB hnab hBR r
  exact ⟨b, hb, c, hcm, rfl⟩

theorem sup_centralizer_eq_top_of_exponent (hp : p.Prime) (hB : Nat.card ↥B = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥B) (_hexp : ∀ b ∈ B, b ^ p = 1)
    (hBR : ⁅B, (⊤ : Subgroup R)⁆ ≤ (center ↥B).map B.subtype) :
    B ⊔ centralizer (B : Set R) = ⊤ :=
  sup_centralizer_eq_top hp hB hnab hBR

end

end CFSG.FeitThompson
