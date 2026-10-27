module

public import CFSG.Fischer.Classification.Basic.Small
public import CFSG.Fischer.Classification.PartII.O3.AffineF3

public section

namespace CFSG.Fischer.Classification.O3

open CFSG.Blueprint.Fischer CFSG.Fischer
open scoped commutatorElement

variable {X : Type} [Group X] {E : Set X}

@[expose] def planePt (d e z : X) (p : Pt) : X :=
  (d * e) ^ p.1.val * (d * z) ^ p.2.val * d * ((d * e) ^ p.1.val * (d * z) ^ p.2.val)⁻¹

variable (hP : Pair X E) {d e z : X} (hd : d ∈ E) (he : e ∈ E) (hz : z ∈ E)
  (hde : d * e ≠ e * d) (hdz : d * z ≠ z * d) (hez : e * z ≠ z * e)
  (hzl : z * (d * e * d) ≠ d * e * d * z)

theorem planePt_zero : planePt d e z 0 = d := by
  simp [planePt]

include hP hd he hde in
theorem planePt_one_zero : planePt d e z (1, 0) = e := by
  have h3 : (d * e) ^ 3 = 1 := by
    rw [← Pair.orderOf_mul_eq_three hP hd he hde, pow_orderOf_eq_one]
  have hval : ((1 : ZMod 3)).val = 1 := rfl
  have hval0 : ((0 : ZMod 3)).val = 0 := rfl
  simp only [planePt, hval, hval0, pow_one, pow_zero, mul_one]
  have hdd := Pair.mul_self hP hd
  have hee := Pair.mul_self hP he
  rw [mul_inv_rev, Pair.inv_eq hP hd, Pair.inv_eq hP he]
  calc d * e * d * (e * d) = d * e * d * e * d * e * e := by
        rw [mul_assoc (d * e * d * e * d) e e, hee, mul_one]; simp only [mul_assoc]
    _ = (d * e) ^ 3 * e := by rw [pow_three]; simp only [mul_assoc]
    _ = e := by rw [h3, one_mul]

include hP hd hz hdz in
theorem planePt_zero_one : planePt d e z (0, 1) = z := by
  have h3 : (d * z) ^ 3 = 1 := by
    rw [← Pair.orderOf_mul_eq_three hP hd hz hdz, pow_orderOf_eq_one]
  have hval : ((1 : ZMod 3)).val = 1 := rfl
  have hval0 : ((0 : ZMod 3)).val = 0 := rfl
  simp only [planePt, hval, hval0, pow_one, pow_zero, one_mul]
  have hzz := Pair.mul_self hP hz
  rw [mul_inv_rev, Pair.inv_eq hP hd, Pair.inv_eq hP hz]
  calc d * z * d * (z * d) = d * z * d * z * d * z * z := by
        rw [mul_assoc (d * z * d * z * d) z z, hzz, mul_one]; simp only [mul_assoc]
    _ = (d * z) ^ 3 * z := by rw [pow_three]; simp only [mul_assoc]
    _ = z := by rw [h3, one_mul]

include hP hd he hz hde hdz hez hzl in
theorem planePt_injective : Function.Injective (planePt d e z) := by
  intro p q hpq
  have h := Pair.conj_injective_of_affine hP hd he hz hde hdz hez hzl
    (a₁ := (⟨p.1.val, p.1.isLt⟩, ⟨p.2.val, p.2.isLt⟩))
    (a₂ := (⟨q.1.val, q.1.isLt⟩, ⟨q.2.val, q.2.isLt⟩)) hpq
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (ZMod.val_injective _ (congrArg Fin.val h.1))
    (ZMod.val_injective _ (congrArg Fin.val h.2))

include hP hd he hz hde hdz hez hzl in
theorem range_planePt :
    Set.range (planePt d e z) = E ∩ (Subgroup.closure ({d, e, z} : Set X) : Set X) := by
  rw [Pair.inter_closure_eq_range_of_affine hP hd he hz hde hdz hez hzl]
  ext f
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(⟨p.1.val, p.1.isLt⟩, ⟨p.2.val, p.2.isLt⟩), rfl⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨((a : ℕ), (b : ℕ)), ?_⟩
    simp only [planePt, ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt]

theorem pow_val_add {x : X} (hx : x ^ 3 = 1) (a b : ZMod 3) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ hx).symm

include hP hd he hz hde hdz hez hzl in
theorem conj_planePt_u (p : Pt) :
    (d * e) * planePt d e z p * (d * e)⁻¹ = planePt d e z (p + (1, 0)) := by
  have hR := Pair.cubeRel_of_affine hP hd he hz hde hdz hez hzl
  obtain ⟨a, b⟩ := p
  have hv1 : (1 : ZMod 3).val = 1 := rfl
  have h1 : (d * e) ^ (a + 1).val = (d * e) * (d * e) ^ a.val := by
    rw [add_comm, pow_val_add hR.cube_left, hv1, pow_one]
  simp only [planePt, Prod.mk_add_mk, add_zero, h1]
  generalize d * e = x
  generalize d * z = y
  group

include hP hd he hz hde hdz hez hzl in
theorem conj_planePt_v (p : Pt) :
    (d * z) * planePt d e z p * (d * z)⁻¹ = planePt d e z (p + (0, 1)) := by
  have hR := Pair.cubeRel_of_affine hP hd he hz hde hdz hez hzl
  have hdc := Pair.commute_commutator_of_affine hP hd he hz hde hdz hez hzl
  obtain ⟨a, b⟩ := p
  have hv1 : (1 : ZMod 3).val = 1 := rfl
  have h1 : (d * z) ^ (b + 1).val = (d * z) ^ b.val * (d * z) := by
    rw [pow_val_add hR.cube_right, hv1, pow_one]
  have hyx := hR.mul_pow_eq a.val
  have hwy := (hR.commute_commutator_right.inv_left).pow_left a.val
  have hwd := (hdc.symm.inv_left).pow_left a.val
  simp only [planePt, Prod.mk_add_mk, add_zero]
  set x := d * e
  set y := d * z
  set w := ⁅x, y⁆⁻¹ ^ a.val
  have hyg : y * (x ^ a.val * y ^ b.val) = x ^ a.val * y ^ (b + 1).val * w := by
    rw [h1, ← mul_assoc, hyx, mul_assoc (x ^ a.val * y), (hwy.pow_right b.val).eq,
      ← mul_assoc, mul_assoc (x ^ a.val) y, ← pow_succ', pow_succ]
  calc y * (x ^ a.val * y ^ b.val * d * (x ^ a.val * y ^ b.val)⁻¹) * y⁻¹
      = (y * (x ^ a.val * y ^ b.val)) * d * (y * (x ^ a.val * y ^ b.val))⁻¹ := by group
    _ = x ^ a.val * y ^ (b + 1).val * (w * d * w⁻¹) * (x ^ a.val * y ^ (b + 1).val)⁻¹ := by
        rw [hyg]; group
    _ = x ^ a.val * y ^ (b + 1).val * d * (x ^ a.val * y ^ (b + 1).val)⁻¹ := by
        rw [hwd.eq, mul_inv_cancel_right]

theorem pow_val_neg {x : X} (hx : x ^ 3 = 1) (a : ZMod 3) : x ^ (-a).val = (x ^ a.val)⁻¹ := by
  have h2 : x ^ 2 = x⁻¹ := sq_eq_inv_of_pow_three hx
  fin_cases a
  · show x ^ 0 = (x ^ 0)⁻¹
    simp
  · show x ^ 2 = (x ^ 1)⁻¹
    rw [h2, pow_one]
  · show x ^ 1 = (x ^ 2)⁻¹
    rw [h2, inv_inv, pow_one]

include hP hd he hz hde hdz hez hzl in
theorem conj_planePt_d (p : Pt) : d * planePt d e z p * d = planePt d e z (-p) := by
  have hR := Pair.cubeRel_of_affine hP hd he hz hde hdz hez hzl
  obtain ⟨a, b⟩ := p
  have hx := Pair.conj_mul_pow_eq_inv hP hd he a.val
  have hy := Pair.conj_mul_pow_eq_inv hP hd hz b.val
  have hdd := Pair.mul_self hP hd
  have hdi := Pair.inv_eq hP hd
  simp only [planePt, Prod.neg_mk, pow_val_neg hR.cube_left, pow_val_neg hR.cube_right]
  set u := (d * e) ^ a.val
  set v := (d * z) ^ b.val
  have hdg : d * (u * v) * d = u⁻¹ * v⁻¹ := by
    calc d * (u * v) * d = (d * u * d) * (d * v * d) := by
          simp only [mul_assoc, ← mul_assoc d d, hdd, one_mul]
      _ = u⁻¹ * v⁻¹ := by rw [hx, hy]
  calc d * (u * v * d * (u * v)⁻¹) * d
      = d * (u * v * d * (u * v)⁻¹) * d⁻¹ := by rw [hdi]
    _ = (d * (u * v) * d) * d * (d * (u * v) * d)⁻¹ := by
        rw [hdi]; simp only [mul_inv_rev, hdi, mul_assoc, hdd, one_mul]
    _ = u⁻¹ * v⁻¹ * d * (u⁻¹ * v⁻¹)⁻¹ := by rw [hdg]

include hP hd he hz hde hdz hez hzl in
theorem conj_pow_planePt_u (n : ℕ) (p : Pt) :
    (d * e) ^ n * planePt d e z p * ((d * e) ^ n)⁻¹ = planePt d e z (p + ((n : ZMod 3), 0)) := by
  induction n generalizing p with
  | zero => simp [Prod.mk_zero_zero]
  | succ n ih =>
    rw [pow_succ', mul_inv_rev, show (d * e) * (d * e) ^ n * planePt d e z p *
        (((d * e) ^ n)⁻¹ * (d * e)⁻¹) = (d * e) * ((d * e) ^ n * planePt d e z p *
        ((d * e) ^ n)⁻¹) * (d * e)⁻¹ by group, ih,
      conj_planePt_u hP hd he hz hde hdz hez hzl]
    congr 1
    simp only [Prod.mk_add_mk, add_zero, Nat.cast_succ, add_assoc]

include hP hd he hz hde hdz hez hzl in
theorem conj_pow_planePt_v (n : ℕ) (p : Pt) :
    (d * z) ^ n * planePt d e z p * ((d * z) ^ n)⁻¹ = planePt d e z (p + (0, (n : ZMod 3))) := by
  induction n generalizing p with
  | zero => simp [Prod.mk_zero_zero]
  | succ n ih =>
    rw [pow_succ', mul_inv_rev, show (d * z) * (d * z) ^ n * planePt d e z p *
        (((d * z) ^ n)⁻¹ * (d * z)⁻¹) = (d * z) * ((d * z) ^ n * planePt d e z p *
        ((d * z) ^ n)⁻¹) * (d * z)⁻¹ by group, ih,
      conj_planePt_v hP hd he hz hde hdz hez hzl]
    congr 1
    simp only [Prod.mk_add_mk, zero_add, Nat.cast_succ, add_assoc]

include hP hd he hz hde hdz hez hzl in
theorem conj_planePt_trans (q p : Pt) :
    ((d * e) ^ q.1.val * (d * z) ^ q.2.val) * planePt d e z p *
      ((d * e) ^ q.1.val * (d * z) ^ q.2.val)⁻¹ = planePt d e z (p + q) := by
  rw [show (d * e) ^ q.1.val * (d * z) ^ q.2.val * planePt d e z p *
      ((d * e) ^ q.1.val * (d * z) ^ q.2.val)⁻¹ = (d * e) ^ q.1.val * ((d * z) ^ q.2.val *
      planePt d e z p * ((d * z) ^ q.2.val)⁻¹) * ((d * e) ^ q.1.val)⁻¹ by group,
    conj_pow_planePt_v hP hd he hz hde hdz hez hzl, conj_pow_planePt_u hP hd he hz hde hdz hez hzl]
  obtain ⟨a, b⟩ := q
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  congr 1
  ext <;> simp [add_comm]

include hP hd he hz hde hdz hez hzl in
theorem planePt_tau (p q : Pt) :
    planePt d e z q * planePt d e z p * planePt d e z q = planePt d e z (-p - q) := by
  set g := (d * e) ^ q.1.val * (d * z) ^ q.2.val
  have hq : planePt d e z q = g * d * g⁻¹ := rfl
  have h1 : g⁻¹ * planePt d e z p * g = planePt d e z (p - q) := by
    have := conj_planePt_trans hP hd he hz hde hdz hez hzl q (p - q)
    rw [show ((d * e) ^ q.1.val * (d * z) ^ q.2.val) = g from rfl, sub_add_cancel] at this
    rw [← this]
    group
  have h2 : g * planePt d e z (q - p) * g⁻¹ = planePt d e z (-p - q) := by
    rw [conj_planePt_trans hP hd he hz hde hdz hez hzl q (q - p)]
    congr 1
    have h3 : (3 : ℕ) • q = 0 := three_nsmul_pt q
    rw [show (3 : ℕ) • q = q + q + q by rw [succ_nsmul, succ_nsmul, one_nsmul]] at h3
    calc q - p + q = q + q + q - p - q := by abel
      _ = -p - q := by rw [h3]; abel
  calc planePt d e z q * planePt d e z p * planePt d e z q
      = g * (d * (g⁻¹ * planePt d e z p * g) * d) * g⁻¹ := by rw [hq]; group
    _ = g * planePt d e z (q - p) * g⁻¹ := by
        rw [h1, conj_planePt_d hP hd he hz hde hdz hez hzl]
        congr 2
        abel_nf
    _ = planePt d e z (-p - q) := h2

end CFSG.Fischer.Classification.O3
