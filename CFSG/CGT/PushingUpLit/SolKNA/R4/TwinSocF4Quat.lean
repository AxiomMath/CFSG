module

public import CFSG.ClassicalInvolution.Q3.TL3C11R
public import CFSG.CGT.PushingUpLit.SolKNA.R4.QuatAlg

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open QuaternionGroup CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

structure QRel8 {G : Type*} [Group G] (x b : G) : Prop where
  x8 : x ^ 8 = 1
  x4 : x ^ 4 ≠ 1
  bx : b * x * b⁻¹ = x⁻¹
  b2 : b * b = x ^ 4

theorem quaternion_qrel8 (m : ℕ) (hm : 2 ≤ m) :
    QRel8 ((a 1 : QuaternionGroup (2 ^ m)) ^ (2 ^ (m - 2))) (xa 0) := by
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have hk8 : 2 ^ (j + 2 - 2) * 8 = 2 * 2 ^ (j + 2) := by
    rw [Nat.add_sub_cancel, pow_succ, pow_succ]; ring
  have hk4 : 2 ^ (j + 2 - 2) * 4 = 2 ^ (j + 2) := by
    rw [Nat.add_sub_cancel, pow_succ, pow_succ]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← pow_mul, hk8]; exact a_one_pow_n
  · rw [← pow_mul, hk4, a_one_pow]
    exact QSub.Alg.a_n_ne_one
  · have h1 : (xa 0 : QuaternionGroup (2 ^ (j + 2))) * a 1 * (xa 0)⁻¹ = (a 1)⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]
      show xa (0 + 1) = a (-1) * xa 0
      rw [a_mul_xa]
      congr 1
      ring
    calc (xa 0 : QuaternionGroup (2 ^ (j + 2))) * (a 1 ^ 2 ^ (j + 2 - 2)) * (xa 0)⁻¹
        = (xa 0 * a 1 * (xa 0)⁻¹) ^ 2 ^ (j + 2 - 2) := (conj_pow).symm
      _ = ((a 1) ^ 2 ^ (j + 2 - 2))⁻¹ := by rw [h1, inv_pow]
  · rw [← pow_mul, hk4, a_one_pow, xa_mul_xa]
    congr 1
    simp

theorem QRel8.map {G H : Type*} [Group G] [Group H] {x b : G} (h : QRel8 x b) (φ : G →* H)
    (hφ : Function.Injective φ) : QRel8 (φ x) (φ b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h.x8, map_one]
  · rw [← map_pow]
    intro h1
    exact h.x4 (hφ (by rw [h1, map_one]))
  · rw [← map_inv, ← map_mul, ← map_mul, h.bx, map_inv]
  · rw [← map_mul, h.b2, map_pow]

theorem exists_qrel8 {G : Type*} [Group G] {Q : Subgroup G} {r : ℕ} (hr : 4 ≤ r)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) : ∃ x b : G, x ∈ Q ∧ b ∈ Q ∧ QRel8 x b := by
  let φ : QuaternionGroup (2 ^ (r - 2)) →* G := Q.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := Q.subtype_injective.comp e.symm.injective
  exact ⟨φ ((a 1 : QuaternionGroup (2 ^ (r - 2))) ^ (2 ^ (r - 2 - 2))), φ (xa 0), (e.symm _).2,
    (e.symm _).2, (quaternion_qrel8 (r - 2) (by omega)).map φ hφ⟩

@[expose] def sylowSet {A : Type*} [Group A] {R : Subgroup A} (S : Sylow 2 R) : Subgroup A :=
  (S : Subgroup R).map R.subtype

theorem mem_sylowSet_le {A : Type*} [Group A] {R : Subgroup A} (S : Sylow 2 R) {y : A}
    (hy : y ∈ sylowSet S) : y ∈ R :=
  Subgroup.map_subtype_le _ hy

theorem exists_qrel8_of_datum {r : ℕ} (hr : 4 ≤ r) {A : Type} [Group A] [Finite A] {R : Subgroup A}
    {S : Sylow 2 R} {z : A} (hd : TightDatum R S z) (hc : TightClsR r A R S z) :
    ∃ x b : A, x ∈ sylowSet S ∧ b ∈ sylowSet S ∧ QRel8 x b ∧ x ^ 4 = z := by
  obtain ⟨e⟩ := hc.1
  let e' : ↥(sylowSet S) ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans e
  obtain ⟨x, b, hx, hb, h⟩ := exists_qrel8 hr e'
  refine ⟨x, b, hx, hb, h, ?_⟩
  have hx4 : (x ^ 4) ^ 2 = 1 := by rw [← pow_mul]; exact h.x8
  have hxR : x ∈ R := mem_sylowSet_le S hx
  have h2 : orderOf (x ^ 4) = 2 :=
    orderOf_eq_prime hx4 h.x4
  exact hd.eq_of_orderOf_eq_two (R.pow_mem hxR 4) h2

theorem quaternion_pow_exp (m : ℕ) (hm : 1 ≤ m) (x : QuaternionGroup (2 ^ m)) :
    x ^ 2 ^ (m + 1) = 1 := by
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  have hN : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
  rcases x with i | i
  · have h1 : (a i : QuaternionGroup (2 ^ m)) = (a 1) ^ i.val := by
      rw [a_one_pow, ZMod.natCast_zmod_val]
    have h2 : (a 1 : QuaternionGroup (2 ^ m)) ^ 2 ^ (m + 1) = 1 := by
      rw [hN]; exact a_one_pow_n
    rw [h1, ← pow_mul, mul_comm i.val, pow_mul, h2, one_pow]
  · have h4 : (4 : ℕ) ∣ 2 ^ (m + 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      exact ⟨2 ^ j, by ring⟩
    obtain ⟨c, hc⟩ := h4
    rw [hc, pow_mul, xa_pow_four, one_pow]

theorem pow_exp_of_quat {G : Type*} [Group G] {Q : Subgroup G} {r : ℕ} (hr : 3 ≤ r)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) {y : G} (hy : y ∈ Q) : y ^ 2 ^ (r - 1) = 1 := by
  have h := quaternion_pow_exp (r - 2) (by omega) (e ⟨y, hy⟩)
  rw [show r - 2 + 1 = r - 1 by omega, ← map_pow, ← map_one e] at h
  have h' := e.injective h
  exact congrArg Subtype.val h'

theorem pow_exp_of_datum {r : ℕ} (hr : 3 ≤ r) {A : Type} [Group A] {R : Subgroup A}
    {S : Sylow 2 R} {z : A} (hc : TightClsR r A R S z) {y : A} (hy : y ∈ sylowSet S) :
    y ^ 2 ^ (r - 1) = 1 := by
  obtain ⟨e⟩ := hc.1
  exact pow_exp_of_quat hr
    ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans e) hy

theorem exists_quat_full {G : Type*} [Group G] {Q : Subgroup G} {r : ℕ} (hr : 3 ≤ r)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) :
    ∃ x b : G, x ∈ Q ∧ b ∈ Q ∧ orderOf x = 2 ^ (r - 1) ∧ b * x * b⁻¹ = x⁻¹ ∧
      b * b = x ^ 2 ^ (r - 2) := by
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  let φ : QuaternionGroup (2 ^ (r - 2)) →* G := Q.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := Q.subtype_injective.comp e.symm.injective
  refine ⟨φ (a 1), φ (xa 0), (e.symm _).2, (e.symm _).2, ?_, ?_, ?_⟩
  · rw [orderOf_injective φ hφ, orderOf_a_one, show r - 1 = (r - 2) + 1 by omega, pow_succ]
    ring
  · have h1 : (xa 0 : QuaternionGroup (2 ^ (r - 2))) * a 1 * (xa 0)⁻¹ = (a 1)⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]
      show xa (0 + 1) = a (-1) * xa 0
      rw [a_mul_xa]
      congr 1
      ring
    calc φ (xa 0) * φ (a 1) * (φ (xa 0))⁻¹ = φ (xa 0 * a 1 * (xa 0)⁻¹) := by
          simp only [map_mul, map_inv]
      _ = φ ((a 1)⁻¹) := by rw [h1]
      _ = (φ (a 1))⁻¹ := map_inv φ _
  · rw [← map_mul, ← map_pow]
    congr 1
    rw [a_one_pow, xa_mul_xa]
    congr 1
    simp

theorem exists_quat_full_of_datum {r : ℕ} (hr : 3 ≤ r) {A : Type} [Group A] {R : Subgroup A}
    {S : Sylow 2 R} {z : A} (hc : TightClsR r A R S z) :
    ∃ x b : A, x ∈ sylowSet S ∧ b ∈ sylowSet S ∧ orderOf x = 2 ^ (r - 1) ∧ b * x * b⁻¹ = x⁻¹ ∧
      b * b = x ^ 2 ^ (r - 2) := by
  obtain ⟨e⟩ := hc.1
  exact exists_quat_full hr
    ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans e)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
