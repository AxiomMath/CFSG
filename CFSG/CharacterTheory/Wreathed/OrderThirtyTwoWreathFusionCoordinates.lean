module

public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionSupport

public noncomputable section

namespace CFSG.Wreathed.OrderThirtyTwo

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.AdaptedBaseFusion

universe u

variable {G : Type u} [Group G]

@[expose] def coord (σ υ : G) (p : ZMod 4 × ZMod 4) : G := σ ^ p.1.val * υ ^ p.2.val

@[expose] def swapMap (p : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 := (p.2, p.1)

@[expose] def cycleMap (p : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 := (-p.2, p.1 - p.2)

section Coord

variable {σ υ : G} (hσ : σ ^ 4 = 1) (hυ : υ ^ 4 = 1) (hc : Commute σ υ)

include hσ in
theorem pow_natCast_val (i : ℕ) : σ ^ ((i : ZMod 4).val) = σ ^ i := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod i hσ]

include hσ hυ in
theorem pow_mul_pow_eq_coord (i j : ℕ) :
    σ ^ i * υ ^ j = coord σ υ ((i : ZMod 4), (j : ZMod 4)) := by
  rw [coord, pow_natCast_val hσ, pow_natCast_val hυ]

include hσ hυ hc in
theorem coord_mul (p q : ZMod 4 × ZMod 4) :
    coord σ υ p * coord σ υ q = coord σ υ (p + q) := by
  simp only [coord, Prod.fst_add, Prod.snd_add, ZMod.val_add]
  rw [← pow_eq_pow_mod _ hσ, ← pow_eq_pow_mod _ hυ, pow_add, pow_add]
  have h := (hc.pow_pow q.1.val p.2.val).eq
  calc σ ^ p.1.val * υ ^ p.2.val * (σ ^ q.1.val * υ ^ q.2.val) =
      σ ^ p.1.val * (σ ^ q.1.val * υ ^ p.2.val) * υ ^ q.2.val := by
        rw [h]
        simp only [mul_assoc]
    _ = σ ^ p.1.val * σ ^ q.1.val * (υ ^ p.2.val * υ ^ q.2.val) := by
        simp only [mul_assoc]

theorem coord_zero : coord σ υ 0 = 1 := by
  simp [coord]

include hσ hυ hc in
theorem coord_inv (p : ZMod 4 × ZMod 4) : (coord σ υ p)⁻¹ = coord σ υ (-p) := by
  apply inv_eq_of_mul_eq_one_right
  rw [coord_mul hσ hυ hc, add_neg_cancel, coord_zero]

include hσ hυ hc in
theorem coord_pow (p : ZMod 4 × ZMod 4) (k : ℕ) : coord σ υ p ^ k = coord σ υ (k • p) := by
  induction k with
  | zero => rw [pow_zero, zero_smul, coord_zero]
  | succ k ih => rw [pow_succ, ih, coord_mul hσ hυ hc, succ_nsmul]

include hσ hυ hc in
theorem coord_zpow (p : ZMod 4 × ZMod 4) (k : ℤ) : coord σ υ p ^ k = coord σ υ (k • p) := by
  rcases Int.eq_nat_or_neg k with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, coord_pow hσ hυ hc, natCast_zsmul]
  · rw [zpow_neg, zpow_natCast, coord_pow hσ hυ hc, coord_inv hσ hυ hc, neg_smul,
      natCast_zsmul]

theorem coord_left : coord σ υ (1, 0) = σ := by
  rw [coord, show (1 : ZMod 4).val = 1 from rfl, show (0 : ZMod 4).val = 0 from rfl, pow_one,
    pow_zero, mul_one]

theorem coord_right : coord σ υ (0, 1) = υ := by
  rw [coord, show (1 : ZMod 4).val = 1 from rfl, show (0 : ZMod 4).val = 0 from rfl, pow_one,
    pow_zero, one_mul]

include hσ hυ hc in
theorem exists_coord {u : G} (hu : u ∈ Subgroup.closure {σ, υ}) :
    ∃ p : ZMod 4 × ZMod 4, u = coord σ υ p := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨(1, 0), coord_left.symm⟩
    · exact ⟨(0, 1), coord_right.symm⟩
  | one => exact ⟨0, coord_zero.symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p + q, coord_mul hσ hυ hc p q⟩
  | inv x _ hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨-p, coord_inv hσ hυ hc p⟩

theorem coord_mem {U : Subgroup G} (hσU : σ ∈ U) (hυU : υ ∈ U) (p : ZMod 4 × ZMod 4) :
    coord σ υ p ∈ U :=
  U.mul_mem (U.pow_mem hσU _) (U.pow_mem hυU _)

include hσ hυ hc in
theorem coord_injective (hσo : orderOf σ = 4) (hυo : orderOf υ = 4)
    (hinf : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) {p q : ZMod 4 × ZMod 4}
    (h : coord σ υ p = coord σ υ q) : p = q := by
  have h' : coord σ υ (p - q) = 1 := by
    rw [sub_eq_add_neg, ← coord_mul hσ hυ hc, ← coord_inv hσ hυ hc, h, mul_inv_cancel]
  set r := p - q with hr
  have hmem : σ ^ r.1.val ∈ Subgroup.zpowers σ ⊓ Subgroup.zpowers υ := by
    refine ⟨Subgroup.npow_mem_zpowers _ _, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h']
    exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _)
  rw [hinf, Subgroup.mem_bot] at hmem
  have hυ1 : υ ^ r.2.val = 1 := by
    rw [coord, hmem, one_mul] at h'
    exact h'
  have h1 : r.1.val = 0 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hmem
    rw [hσo] at hdvd
    have hlt : r.1.val < 4 := ZMod.val_lt _
    omega
  have h2 : r.2.val = 0 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hυ1
    rw [hυo] at hdvd
    have hlt : r.2.val < 4 := ZMod.val_lt _
    omega
  have hr0 : r = 0 := Prod.ext ((ZMod.val_eq_zero _).mp h1) ((ZMod.val_eq_zero _).mp h2)
  rw [hr] at hr0
  exact sub_eq_zero.mp hr0

end Coord

end CFSG.Wreathed.OrderThirtyTwo
