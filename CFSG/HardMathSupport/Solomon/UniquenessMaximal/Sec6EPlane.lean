module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E

open Matrix QuaternionGroup

@[expose] def fixSub {M : Type*} [AddCommGroup M] [Module (ZMod 3) M]
    (U : Subgroup (M ≃ₗ[ZMod 3] M)) : AddSubgroup M where
  carrier := {m | ∀ u ∈ U, u m = m}
  zero_mem' := fun u _ => map_zero u
  add_mem' := fun {a b} ha hb u hu => by rw [map_add, ha u hu, hb u hu]
  neg_mem' := fun {a} ha u hu => by rw [map_neg, ha u hu]

@[expose] def commSub {M : Type*} [AddCommGroup M] [Module (ZMod 3) M]
    (U : Subgroup (M ≃ₗ[ZMod 3] M)) : AddSubgroup M :=
  AddSubgroup.closure {x | ∃ u ∈ U, ∃ m : M, x = u m - m}

private abbrev Mat2 := Matrix (Fin 2) (Fin 2) (ZMod 3)

private def Q8rel (P R : Mat2) : Prop := P ^ 4 = 1 ∧ P ^ 2 ≠ 1 ∧ R ^ 2 = P ^ 2 ∧ R * P = P ^ 3 * R

private instance (P R : Mat2) : Decidable (Q8rel P R) := by unfold Q8rel; infer_instance

private def Sq (P R : Mat2) : Finset Mat2 :=
  Finset.univ.image (fun ij : Fin 4 × Fin 2 => P ^ (ij.1 : ℕ) * R ^ (ij.2 : ℕ))

set_option maxRecDepth 100000 in
private theorem q8_sq : ∀ P R : Mat2, Q8rel P R → P ^ 2 = -1 ∧ R ^ 2 = -1 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem q8_neg : ∀ P R : Mat2, Q8rel P R →
    (-1 : Mat2) ∈ Sq P R ∧ ∀ N ∈ Sq P R, N ^ 2 = 1 → N = 1 ∨ N = -1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
private theorem q8_free : ∀ P R : Mat2, Q8rel P R → ∀ v : Fin 2 → ZMod 3, ∀ N ∈ Sq P R, N ≠ 1 →
    N.mulVec v = v → v = 0 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem q8_trans : ∀ P R : Mat2, Q8rel P R → ∀ v w : Fin 2 → ZMod 3, v ≠ 0 → w ≠ 0 →
    ∃ N ∈ Sq P R, N.mulVec v = w := by decide +kernel

set_option maxRecDepth 100000 in
private theorem q8_zd : ∀ P R : Mat2, Q8rel P R →
    (∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ v + P.mulVec v + R.mulVec v = 0) ∧
      (∃ v : Fin 2 → ZMod 3, v + P.mulVec v + R.mulVec v ≠ 0) := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
private theorem q8_norm3 : ∀ P R : Mat2, Q8rel P R → ∀ U : Mat2, U ^ 3 = 1 → U ≠ 1 →
    ∃ N ∈ Sq P R, ¬ (N * U = U * N ∨ N * U = U ^ 2 * N) := by decide +kernel

set_option maxRecDepth 100000 in
private theorem q8_e4 : ∀ P R : Mat2, Q8rel P R → ∀ N : Mat2, N ^ 4 = 1 → N ^ 2 ≠ 1 →
    N ∈ Sq P R := by decide +kernel

set_option maxRecDepth 100000 in
private theorem mat_comm3 : ∀ U U' : Mat2, U ^ 3 = 1 → U' ^ 3 = 1 → U * U' = U' * U →
    (U' - 1) * (U - 1) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem mat_fix_card : ∀ N : Mat2, N ^ 3 = 1 → N ≠ 1 →
    (Finset.univ.filter (fun v : Fin 2 → ZMod 3 => N.mulVec v = v)).card = 3 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem mat_comm_card : ∀ N : Mat2, N ^ 3 = 1 → N ≠ 1 →
    (Finset.univ.filter
      (fun w : Fin 2 → ZMod 3 => ∃ v : Fin 2 → ZMod 3, N.mulVec v - v = w)).card = 3 := by
  decide +kernel

section Coords

variable {M : Type*} [AddCommGroup M] [Module (ZMod 3) M] [Finite M]

private theorem finrank_of_card (hM : Nat.card M = 9) : Module.finrank (ZMod 3) M = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := M)
  rw [hM, Nat.card_zmod] at h
  have : (3 : ℕ) ^ 2 = 3 ^ Module.finrank (ZMod 3) M := by simpa using h
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) this).symm

private noncomputable def planeBasis (hM : Nat.card M = 9) : Module.Basis (Fin 2) (ZMod 3) M :=
  Module.finBasisOfFinrankEq (ZMod 3) M (finrank_of_card hM)

private noncomputable def rho (hM : Nat.card M = 9) :
    (M ≃ₗ[ZMod 3] M) ≃* GL (Fin 2) (ZMod 3) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) M).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (planeBasis hM)).toMulEquiv)

private noncomputable def mat (hM : Nat.card M = 9) (g : M ≃ₗ[ZMod 3] M) : Mat2 :=
  ((rho hM g : GL (Fin 2) (ZMod 3)) : Mat2)

private theorem mat_eq (hM : Nat.card M = 9) (g : M ≃ₗ[ZMod 3] M) :
    mat hM g = LinearMap.toMatrix (planeBasis hM) (planeBasis hM) (g : M →ₗ[ZMod 3] M) := rfl

private theorem mat_mul (hM : Nat.card M = 9) (g h : M ≃ₗ[ZMod 3] M) :
    mat hM (g * h) = mat hM g * mat hM h := by
  simp [mat, map_mul]

private theorem mat_one (hM : Nat.card M = 9) : mat hM (1 : M ≃ₗ[ZMod 3] M) = 1 := by
  simp [mat]

private theorem mat_injective (hM : Nat.card M = 9) : Function.Injective (mat hM) := by
  intro g h hgh
  apply (rho hM).injective
  apply Units.ext
  exact hgh

private theorem mat_apply (hM : Nat.card M = 9) (g : M ≃ₗ[ZMod 3] M) (m : M) :
    (planeBasis hM).equivFun (g m) = (mat hM g).mulVec ((planeBasis hM).equivFun m) := by
  rw [mat_eq]
  exact (LinearMap.toMatrix_mulVec_repr (planeBasis hM) (planeBasis hM)
    (g : M →ₗ[ZMod 3] M) m).symm

private noncomputable def matHom (hM : Nat.card M = 9) : (M ≃ₗ[ZMod 3] M) →* Mat2 where
  toFun := mat hM
  map_one' := mat_one hM
  map_mul' := mat_mul hM

private theorem mat_pow (hM : Nat.card M = 9) (g : M ≃ₗ[ZMod 3] M) (n : ℕ) :
    mat hM (g ^ n) = mat hM g ^ n := map_pow (matHom hM) g n

private theorem mat_eq_one_iff (hM : Nat.card M = 9) (g : M ≃ₗ[ZMod 3] M) :
    mat hM g = 1 ↔ g = 1 := by
  rw [← mat_one hM]
  exact (mat_injective hM).eq_iff

private theorem equivFun_eq_zero (hM : Nat.card M = 9) (m : M) :
    (planeBasis hM).equivFun m = 0 ↔ m = 0 :=
  (planeBasis hM).equivFun.map_eq_zero_iff

theorem plane_card_aut (hM : Nat.card M = 9) : Nat.card (M ≃ₗ[ZMod 3] M) = 48 := by
  rw [Nat.card_congr (rho hM).toEquiv, Matrix.card_GL_field]
  simp [Fin.prod_univ_two]

private theorem q8_words : ∀ g : QuaternionGroup 2,
    ∃ i : Fin 4, ∃ j : Fin 2, g = (a 1) ^ (i : ℕ) * (xa 0) ^ (j : ℕ) := by decide

private theorem q8_rel1 : (a 1 : QuaternionGroup 2) ^ 4 = 1 := by decide
private theorem q8_rel2 : (a 1 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
private theorem q8_rel3 : (xa 0 : QuaternionGroup 2) ^ 2 = (a 1) ^ 2 := by decide
private theorem q8_rel4 : (xa 0 : QuaternionGroup 2) * a 1 = (a 1) ^ 3 * xa 0 := by decide

private theorem q8rel_of_inj (hM : Nat.card M = 9) (f : QuaternionGroup 2 →* (M ≃ₗ[ZMod 3] M))
    (hf : Function.Injective f) : Q8rel (mat hM (f (a 1))) (mat hM (f (xa 0))) := by
  have hFinj : Function.Injective ((matHom hM).comp f) := fun x y h => hf (mat_injective hM h)
  show Q8rel (((matHom hM).comp f) (a 1)) (((matHom hM).comp f) (xa 0))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_pow, q8_rel1, map_one]
  · intro h
    rw [← map_pow, ← map_one ((matHom hM).comp f)] at h
    exact q8_rel2 (hFinj h)
  · rw [← map_pow, ← map_pow, q8_rel3]
  · rw [← map_mul, ← map_pow, ← map_mul, q8_rel4]

section Q8

private theorem mat_mem_Sq (hM : Nat.card M = 9) (f : QuaternionGroup 2 →* (M ≃ₗ[ZMod 3] M))
    (q : M ≃ₗ[ZMod 3] M) (hq : q ∈ f.range) :
    mat hM q ∈ Sq (mat hM (f (a 1))) (mat hM (f (xa 0))) := by
  obtain ⟨x, rfl⟩ := hq
  obtain ⟨i, j, rfl⟩ := q8_words x
  simp only [Sq, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨(i, j), by simp only [map_mul, map_pow, mat_mul, mat_pow]⟩

private theorem exists_range (hM : Nat.card M = 9) (f : QuaternionGroup 2 →* (M ≃ₗ[ZMod 3] M))
    (N : Mat2) (hN : N ∈ Sq (mat hM (f (a 1))) (mat hM (f (xa 0)))) :
    ∃ q ∈ f.range, mat hM q = N := by
  simp only [Sq, Finset.mem_image, Finset.mem_univ, true_and] at hN
  obtain ⟨⟨i, j⟩, rfl⟩ := hN
  exact ⟨f ((a 1) ^ (i : ℕ) * (xa 0) ^ (j : ℕ)), ⟨_, rfl⟩,
    by simp only [map_mul, map_pow, mat_mul, mat_pow]⟩

theorem plane_q8_neg (hM : Nat.card M = 9) (f : QuaternionGroup 2 →* (M ≃ₗ[ZMod 3] M))
    (hf : Function.Injective f) :
    ∃ t ∈ f.range, (∀ m : M, t m = -m) ∧ ∀ q ∈ f.range, q * q = 1 → q = 1 ∨ q = t := by
  obtain ⟨h1, h2⟩ := q8_neg _ _ (q8rel_of_inj hM f hf)
  obtain ⟨t, ht, htm⟩ := exists_range hM f (-1) h1
  refine ⟨t, ht, fun m => ?_, fun q hq hqq => ?_⟩
  · apply (planeBasis hM).equivFun.injective
    rw [mat_apply, htm, map_neg]
    exact (Matrix.neg_mulVec _ 1).trans (by rw [Matrix.one_mulVec])
  · rcases h2 (mat hM q) (mat_mem_Sq hM f q hq)
        (by rw [pow_two, ← mat_mul, hqq, mat_one]) with h | h
    · exact Or.inl ((mat_eq_one_iff hM q).1 h)
    · exact Or.inr (mat_injective hM (h.trans htm.symm))

theorem plane_q8_free (hM : Nat.card M = 9) (f : QuaternionGroup 2 →* (M ≃ₗ[ZMod 3] M))
    (hf : Function.Injective f) :
    ∀ q ∈ f.range, q ≠ 1 → ∀ m : M, q m = m → m = 0 := by
  intro q hq hq1 m hm
  have hN : mat hM q ≠ 1 := fun h => hq1 ((mat_eq_one_iff hM q).1 h)
  have := q8_free _ _ (q8rel_of_inj hM f hf) ((planeBasis hM).equivFun m) _
    (mat_mem_Sq hM f q hq) hN (by rw [← mat_apply, hm])
  exact (equivFun_eq_zero hM m).1 this

theorem plane_q8_trans (hM : Nat.card M = 9) (f : QuaternionGroup 2 →* (M ≃ₗ[ZMod 3] M))
    (hf : Function.Injective f) :
    ∀ m n : M, m ≠ 0 → n ≠ 0 → ∃ q ∈ f.range, q m = n := by
  intro m n hm hn
  obtain ⟨N, hN, hNv⟩ := q8_trans _ _ (q8rel_of_inj hM f hf) ((planeBasis hM).equivFun m)
    ((planeBasis hM).equivFun n) (mt (equivFun_eq_zero hM m).1 hm)
    (mt (equivFun_eq_zero hM n).1 hn)
  obtain ⟨q, hq, hqN⟩ := exists_range hM f N hN
  refine ⟨q, hq, (planeBasis hM).equivFun.injective ?_⟩
  rw [mat_apply, hqN, hNv]

theorem plane_q8_zd (hM : Nat.card M = 9) (f : QuaternionGroup 2 →* (M ≃ₗ[ZMod 3] M))
    (hf : Function.Injective f) :
    ∃ q1 ∈ f.range, ∃ q2 ∈ f.range, (∃ m : M, m ≠ 0 ∧ m + q1 m + q2 m = 0) ∧
      ∃ m : M, m + q1 m + q2 m ≠ 0 := by
  obtain ⟨⟨v, hv0, hv⟩, ⟨w, hw⟩⟩ := q8_zd _ _ (q8rel_of_inj hM f hf)
  have hsum : ∀ m : M, (planeBasis hM).equivFun (m + f (a 1) m + f (xa 0) m) =
      (planeBasis hM).equivFun m + (mat hM (f (a 1))).mulVec ((planeBasis hM).equivFun m) +
        (mat hM (f (xa 0))).mulVec ((planeBasis hM).equivFun m) := by
    intro m
    rw [map_add, map_add, mat_apply, mat_apply]
  have hcoord : ∀ v : Fin 2 → ZMod 3, (planeBasis hM).equivFun ((planeBasis hM).equivFun.symm v) = v :=
    fun v => LinearEquiv.apply_symm_apply _ _
  refine ⟨f (a 1), ⟨_, rfl⟩, f (xa 0), ⟨_, rfl⟩, ⟨(planeBasis hM).equivFun.symm v, ?_, ?_⟩,
    ⟨(planeBasis hM).equivFun.symm w, ?_⟩⟩
  · intro h
    apply hv0
    rw [← hcoord v, h, map_zero]
  · apply (equivFun_eq_zero hM _).1
    rw [hsum, hcoord]
    exact hv
  · intro h
    apply hw
    have := (equivFun_eq_zero hM _).2 h
    rw [hsum, hcoord] at this
    exact this

private theorem range_le (hM : Nat.card M = 9) (f f' : QuaternionGroup 2 →* (M ≃ₗ[ZMod 3] M))
    (hf : Function.Injective f) (hf' : Function.Injective f') : f'.range ≤ f.range := by
  have hrel := q8rel_of_inj hM f hf
  obtain ⟨h1, h2, h3, -⟩ := q8rel_of_inj hM f' hf'
  have e1 : f' (a 1) ∈ f.range := by
    obtain ⟨q, hq, hqN⟩ := exists_range hM f _ (q8_e4 _ _ hrel _ h1 h2)
    exact (mat_injective hM hqN) ▸ hq
  have e2 : f' (xa 0) ∈ f.range := by
    have h4 : mat hM (f' (xa 0)) ^ 4 = 1 := by
      calc mat hM (f' (xa 0)) ^ 4 = (mat hM (f' (xa 0)) ^ 2) ^ 2 := by rw [← pow_mul]
        _ = (mat hM (f' (a 1)) ^ 2) ^ 2 := by rw [h3]
        _ = mat hM (f' (a 1)) ^ 4 := by rw [← pow_mul]
        _ = 1 := h1
    obtain ⟨q, hq, hqN⟩ := exists_range hM f _ (q8_e4 _ _ hrel _ h4 (h3 ▸ h2))
    exact (mat_injective hM hqN) ▸ hq
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, j, rfl⟩ := q8_words x
  rw [map_mul, map_pow, map_pow]
  exact mul_mem (pow_mem e1 _) (pow_mem e2 _)

theorem plane_q8_unique (hM : Nat.card M = 9) (f : QuaternionGroup 2 →* (M ≃ₗ[ZMod 3] M))
    (hf : Function.Injective f) :
    ∀ f' : QuaternionGroup 2 →* (M ≃ₗ[ZMod 3] M), Function.Injective f' → f'.range = f.range :=
  fun f' hf' => le_antisymm (range_le hM f f' hf hf') (range_le hM f' f hf' hf)

end Q8

private theorem finite_aut (hM : Nat.card M = 9) : Finite (M ≃ₗ[ZMod 3] M) :=
  Nat.finite_of_card_ne_zero (by rw [plane_card_aut hM]; norm_num)

private theorem zpow_cases {G : Type*} [Group G] (u : G) (hu : u ^ 3 = 1) (k : ℤ) :
    u ^ k = 1 ∨ u ^ k = u ∨ u ^ k = u ^ 2 := by
  have h3 : u ^ (3 : ℤ) = 1 := by exact_mod_cast hu
  have hk : u ^ k = u ^ (k % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 3, _root_.zpow_add, _root_.zpow_mul, h3, _root_.one_zpow, one_mul]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · left; rw [hk, h]; simp
  · right; left; rw [hk, h]; simp
  · right; right; rw [hk, h]; simp [zpow_ofNat]

theorem plane_three_card (hM : Nat.card M = 9) (U : Subgroup (M ≃ₗ[ZMod 3] M))
    (hU : IsPGroup 3 U) : Nat.card U ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := finite_aut hM
  obtain ⟨n, hn⟩ := hU.exists_card_eq
  have hd : Nat.card U ∣ 48 := plane_card_aut hM ▸ Subgroup.card_subgroup_dvd_card U
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · rw [hn]; norm_num
    · rw [hn]; norm_num
  · exfalso
    have h9 : 3 ^ 2 ∣ 48 := (pow_dvd_pow 3 h).trans (by rw [← hn]; exact hd)
    omega

private theorem three_cases (hM : Nat.card M = 9) (U : Subgroup (M ≃ₗ[ZMod 3] M))
    (hU : IsPGroup 3 U) :
    U = ⊥ ∨ ∃ u0 : M ≃ₗ[ZMod 3] M, u0 ≠ 1 ∧ u0 ^ 3 = 1 ∧ U = Subgroup.zpowers u0 ∧
      Nat.card U = 3 := by
  have := finite_aut hM
  rcases (Nat.dvd_prime Nat.prime_three).1 (plane_three_card hM U hU) with h | h
  · exact Or.inl (Subgroup.eq_bot_of_card_eq U h)
  · right
    have hne : U ≠ ⊥ := fun hb => by simp [hb] at h
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have ha3 : a ^ 3 = 1 := by
      have := pow_card_eq_one' (G := U) (x := a)
      rwa [h] at this
    have hu1 : a.1 ≠ 1 := fun h1 => ha (Subtype.ext h1)
    have hu3 : a.1 ^ 3 = 1 := congrArg Subtype.val ha3
    have hord : orderOf a.1 = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hu3) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.1 h1) hu1
      · exact h1
    refine ⟨a.1, hu1, hu3, ?_, h⟩
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 a.2) ?_).symm
    rw [Nat.card_zpowers, hord, h]

theorem plane_three_exp (hM : Nat.card M = 9) (U : Subgroup (M ≃ₗ[ZMod 3] M))
    (hU : IsPGroup 3 U) :
    (∀ u ∈ U, u ^ 3 = 1) ∧ ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u := by
  rcases three_cases hM U hU with rfl | ⟨u0, -, h3, rfl, -⟩
  · refine ⟨fun u hu => ?_, fun u hu u' hu' => ?_⟩
    · rw [Subgroup.mem_bot] at hu; rw [hu]; simp
    · rw [Subgroup.mem_bot] at hu hu'; rw [hu, hu']
  · refine ⟨fun u hu => ?_, fun u hu u' hu' => ?_⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, h3, _root_.one_zpow]
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu'
      exact (Commute.zpow_zpow_self u0 k l).eq

theorem plane_three_nil (hM : Nat.card M = 9) (U : Subgroup (M ≃ₗ[ZMod 3] M))
    (hU : IsPGroup 3 U) :
    ∀ u ∈ U, ∀ u' ∈ U, ∀ m : M, u' (u m - m) = u m - m := by
  intro u hu u' hu' m
  obtain ⟨h3, hc⟩ := plane_three_exp hM U hU
  have key := mat_comm3 (mat hM u) (mat hM u') (by rw [← mat_pow, h3 u hu, mat_one])
    (by rw [← mat_pow, h3 u' hu', mat_one]) (by rw [← mat_mul, ← mat_mul, hc u hu u' hu'])
  apply (planeBasis hM).equivFun.injective
  rw [mat_apply hM u' (u m - m), map_sub, mat_apply hM u m]
  have h2 : (mat hM u' - 1).mulVec ((mat hM u - 1).mulVec ((planeBasis hM).equivFun m)) = 0 := by
    rw [Matrix.mulVec_mulVec, key, Matrix.zero_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] at h2
  exact sub_eq_zero.1 h2

theorem plane_q8_odd (hM : Nat.card M = 9) (f : QuaternionGroup 2 →* (M ≃ₗ[ZMod 3] M))
    (hf : Function.Injective f) :
    ∀ Z : Subgroup (M ≃ₗ[ZMod 3] M), Odd (Nat.card Z) →
      (∀ q ∈ f.range, ∀ z ∈ Z, q * z * q⁻¹ ∈ Z) → Z = ⊥ := by
  intro Z hodd hnorm
  have hdvd : Nat.card Z ∣ 48 := plane_card_aut hM ▸ Subgroup.card_subgroup_dvd_card Z
  have h3 : Nat.card Z ∣ 3 := by
    have : ∀ d ∈ Nat.divisors 48, Odd d → d ∣ 3 := by decide
    exact this _ (Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩) hodd
  have hpg : IsPGroup 3 Z := IsPGroup.of_card_dvd_pow (n := 1) (by simpa using h3)
  rcases three_cases hM Z hpg with hb | ⟨u0, h1, h3', hZ, -⟩
  · exact hb
  · exfalso
    obtain ⟨N, hN, hnc⟩ := q8_norm3 _ _ (q8rel_of_inj hM f hf) (mat hM u0)
      (by rw [← mat_pow, h3', mat_one]) (fun h => h1 ((mat_eq_one_iff hM u0).1 h))
    obtain ⟨q, hq, hqN⟩ := exists_range hM f N hN
    subst hqN
    have hmem : q * u0 * q⁻¹ ∈ Z := hnorm q hq u0 (hZ ▸ Subgroup.mem_zpowers u0)
    rw [hZ] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    apply hnc
    rcases zpow_cases u0 h3' k with h | h | h
    · rw [h] at hk
      exfalso
      apply h1
      have := mul_inv_eq_one.1 hk.symm
      simpa using this
    · rw [h] at hk
      have : q * u0 = u0 * q := mul_inv_eq_iff_eq_mul.1 hk.symm
      exact Or.inl (by rw [← mat_mul, ← mat_mul, this])
    · rw [h] at hk
      have : q * u0 = u0 ^ 2 * q := mul_inv_eq_iff_eq_mul.1 hk.symm
      exact Or.inr (by rw [← mat_pow, ← mat_mul, ← mat_mul, this])

private theorem card_subtype_fun (p : (Fin 2 → ZMod 3) → Prop) [DecidablePred p] :
    Nat.card {w // p w} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem plane_three_dichotomy (hM : Nat.card M = 9) (U : Subgroup (M ≃ₗ[ZMod 3] M))
    (hU : IsPGroup 3 U) :
    (U = ⊥ ∧ commSub U = ⊥ ∧ fixSub U = ⊤) ∨
      (Nat.card U = 3 ∧ Nat.card (commSub U) = 3 ∧ Nat.card (fixSub U) = 3) := by
  rcases three_cases hM U hU with rfl | ⟨u0, h1, h3, rfl, hc⟩
  · left
    refine ⟨rfl, ?_, ?_⟩
    · refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) bot_le
      rintro x ⟨u, hu, m, rfl⟩
      rw [Subgroup.mem_bot] at hu
      subst hu
      simp
    · refine eq_top_iff.2 fun m _ u hu => ?_
      rw [Subgroup.mem_bot] at hu
      rw [hu]
      rfl
  · right
    refine ⟨hc, ?_⟩
    have hN3 : mat hM u0 ^ 3 = 1 := by rw [← mat_pow, h3, mat_one]
    have hN1 : mat hM u0 ≠ 1 := fun h => h1 ((mat_eq_one_iff hM u0).1 h)
    have hfix : ∀ m, m ∈ fixSub (Subgroup.zpowers u0) ↔ u0 m = m := by
      intro m
      constructor
      · exact fun h => h u0 (Subgroup.mem_zpowers u0)
      · intro h u hu
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
        rcases zpow_cases u0 h3 k with hk | hk | hk <;> rw [hk]
        · rfl
        · exact h
        · rw [pow_two]
          show u0 (u0 m) = m
          rw [h, h]
    have hcomm : ∀ x, x ∈ commSub (Subgroup.zpowers u0) ↔ ∃ m, u0 m - m = x := by
      intro x
      constructor
      · intro hx
        have hle : commSub (Subgroup.zpowers u0) ≤
            AddMonoidHom.range (u0.toLinearMap.toAddMonoidHom - AddMonoidHom.id M) := by
          refine (AddSubgroup.closure_le _).2 ?_
          rintro x ⟨u, hu, m, rfl⟩
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
          rcases zpow_cases u0 h3 k with h | h | h <;> rw [h]
          · exact AddMonoidHom.mem_range.2 ⟨0, by simp⟩
          · exact AddMonoidHom.mem_range.2 ⟨m, rfl⟩
          · refine AddMonoidHom.mem_range.2 ⟨u0 m + m, ?_⟩
            rw [pow_two]
            show u0 (u0 m + m) - (u0 m + m) = u0 (u0 m) - m
            rw [map_add]
            abel
        obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.1 (hle hx)
        exact ⟨y, hy⟩
      · rintro ⟨m, rfl⟩
        exact AddSubgroup.subset_closure ⟨u0, Subgroup.mem_zpowers u0, m, rfl⟩
    constructor
    · have heq : Nat.card (commSub (Subgroup.zpowers u0)) = Nat.card
          {w : Fin 2 → ZMod 3 // ∃ v : Fin 2 → ZMod 3, (mat hM u0).mulVec v - v = w} := by
        refine Nat.card_congr ((planeBasis hM).equivFun.toEquiv.subtypeEquiv (fun x => ?_))
        show x ∈ commSub (Subgroup.zpowers u0) ↔
          ∃ v : Fin 2 → ZMod 3, (mat hM u0).mulVec v - v = (planeBasis hM).equivFun x
        rw [hcomm]
        constructor
        · rintro ⟨m, rfl⟩
          exact ⟨(planeBasis hM).equivFun m, by rw [map_sub, mat_apply]⟩
        · rintro ⟨v, hv⟩
          refine ⟨(planeBasis hM).equivFun.symm v, (planeBasis hM).equivFun.injective ?_⟩
          rw [map_sub, mat_apply, LinearEquiv.apply_symm_apply]
          exact hv
      rw [heq, card_subtype_fun, mat_comm_card _ hN3 hN1]
    · have heq : Nat.card (fixSub (Subgroup.zpowers u0)) = Nat.card
          {w : Fin 2 → ZMod 3 // (mat hM u0).mulVec w = w} := by
        refine Nat.card_congr ((planeBasis hM).equivFun.toEquiv.subtypeEquiv (fun x => ?_))
        show x ∈ fixSub (Subgroup.zpowers u0) ↔
          (mat hM u0).mulVec ((planeBasis hM).equivFun x) = (planeBasis hM).equivFun x
        rw [hfix, ← mat_apply]
        exact ⟨fun h => by rw [h], fun h => (planeBasis hM).equivFun.injective h⟩
      rw [heq, card_subtype_fun, mat_fix_card _ hN3 hN1]

end Coords

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E
