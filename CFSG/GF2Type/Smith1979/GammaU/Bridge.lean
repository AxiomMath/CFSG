module

public import CFSG.GF2Type.Smith1979.GammaU.Model
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GF2Type.Smith1979.GammaU

open Module QuadraticMap

theorem zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

theorem zmod2_mul_self : ∀ a : ZMod 2, a * a = a := by decide

theorem zmod2_eq_zero_or_eq_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

section General

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem vec_add_self (w : V) : w + w = 0 := by
  rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul]

@[expose] def famMap (θ : V →ₗ[ZMod 2] V) (b : ℕ → V) : V12 →ₗ[ZMod 2] V where
  toFun x := ∑ i : Fin 6, (x (lo i) • b i + x (hi i) • θ (b i))
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by abel
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum, smul_add]

theorem famMap_apply (θ : V →ₗ[ZMod 2] V) (b : ℕ → V) (x : V12) :
    famMap θ b x = ∑ i : Fin 6, (x (lo i) • b i + x (hi i) • θ (b i)) := rfl

variable (q : QuadraticForm (ZMod 2) V)

theorem polar_self_eq_zero (v : V) : polar q v v = 0 := by
  rw [QuadraticMap.polar_self q v, two_nsmul, zmod2_add_self]

theorem polar_sum_left {ι : Type*} (s : Finset ι) (w : ι → V) (y : V) :
    polar q (∑ i ∈ s, w i) y = ∑ i ∈ s, polar q (w i) y := by
  induction s using Finset.cons_induction with
  | empty => simp [polar_zero_left]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, polar_add_left, ih]

theorem polar_sum_right {ι : Type*} (s : Finset ι) (x : V) (w : ι → V) :
    polar q x (∑ i ∈ s, w i) = ∑ i ∈ s, polar q x (w i) := by
  rw [polar_comm, polar_sum_left]
  exact Finset.sum_congr rfl fun i _ => polar_comm _ _ _

theorem map_sum_of_orth {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → V)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → polar q (w i) (w j) = 0) :
    q (∑ i ∈ s, w i) = ∑ i ∈ s, q (w i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, QuadraticMap.map_add (⇑q) (w a),
      polar_sum_right,
      Finset.sum_eq_zero fun j hj => h a (Finset.mem_insert_self a s) j
        (Finset.mem_insert_of_mem hj) (fun e => ha (e ▸ hj)),
      ih fun i hi j hj => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj),
      add_zero]

variable {q} {θ : V →ₗ[ZMod 2] V} (hθq : ∀ v, q (θ v) = q v)
include hθq

theorem polar_theta (u v : V) : polar q (θ u) (θ v) = polar q u v := by
  simp only [polar, ← map_add θ, hθq]

theorem theta_theta (hθ3 : ∀ v, θ (θ (θ v)) = v) (hfix : ∀ v, θ v = v → v = 0) (v : V) :
    θ (θ v) = θ v + v := by
  have h := hfix (θ (θ v) + θ v + v) (by rw [map_add θ, map_add θ, hθ3]; abel)
  calc θ (θ v) = θ (θ v) + θ v + v + (θ v + v) := by
        rw [show θ (θ v) + θ v + v + (θ v + v) = θ (θ v) + ((θ v + θ v) + (v + v)) by abel,
          vec_add_self, vec_add_self, add_zero, add_zero]
    _ = θ v + v := by rw [h, zero_add]

theorem q_eq_polar_theta (hθ3 : ∀ v, θ (θ (θ v)) = v) (hfix : ∀ v, θ v = v → v = 0) (v : V) :
    q v = polar q (θ v) v := by
  have h1 : q (θ (θ v)) = q v := by rw [hθq, hθq]
  rw [theta_theta hθq hθ3 hfix, QuadraticMap.map_add (⇑q) (θ v) v, hθq, zmod2_add_self,
    zero_add] at h1
  exact h1.symm

variable (q θ) in
def IsFam (k : ℕ) (b : ℕ → V) : Prop :=
  (∀ i < k, q (b i) = 1) ∧
    ∀ i < k, ∀ j < k, i ≠ j → polar q (b i) (b j) = 0 ∧ polar q (θ (b i)) (b j) = 0

variable (hθ3 : ∀ v, θ (θ (θ v)) = v) (hfix : ∀ v, θ v = v → v = 0)
include hθ3 hfix

theorem IsFam.polar_theta_self {k : ℕ} {b : ℕ → V} (hb : IsFam q θ k b) {i : ℕ} (hi : i < k) :
    polar q (θ (b i)) (b i) = 1 := by
  rw [← q_eq_polar_theta hθq hθ3 hfix, hb.1 i hi]

theorem IsFam.polar_comb_b {k : ℕ} {b : ℕ → V} (hb : IsFam q θ k b) (α β : Fin k → ZMod 2)
    (j : Fin k) : polar q (∑ i, (α i • b i + β i • θ (b i))) (b j) = β j := by
  rw [polar_sum_left, Finset.sum_eq_single j]
  · rw [polar_add_left, polar_smul_left, polar_smul_left, polar_self_eq_zero,
      hb.polar_theta_self hθq hθ3 hfix j.isLt, smul_eq_mul, smul_eq_mul, mul_zero, mul_one,
      zero_add]
  · intro i _ hij
    have h := hb.2 i i.isLt j j.isLt (Fin.val_ne_of_ne hij)
    rw [polar_add_left, polar_smul_left, polar_smul_left, h.1, h.2, smul_zero, smul_zero,
      add_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem IsFam.polar_comb_theta_b {k : ℕ} {b : ℕ → V} (hb : IsFam q θ k b)
    (α β : Fin k → ZMod 2) (j : Fin k) :
    polar q (∑ i, (α i • b i + β i • θ (b i))) (θ (b j)) = α j := by
  rw [polar_sum_left, Finset.sum_eq_single j]
  · rw [polar_add_left, polar_smul_left, polar_smul_left, polar_self_eq_zero, polar_comm,
      hb.polar_theta_self hθq hθ3 hfix j.isLt, smul_eq_mul, smul_eq_mul, mul_zero, mul_one,
      add_zero]
  · intro i _ hij
    have h := hb.2 j j.isLt i i.isLt (Fin.val_ne_of_ne (Ne.symm hij))
    have h' := hb.2 i i.isLt j j.isLt (Fin.val_ne_of_ne hij)
    rw [polar_add_left, polar_smul_left, polar_smul_left, polar_comm, h.2, polar_theta hθq,
      h'.1, smul_zero, smul_zero, add_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem exists_next (hq : q.polarBilin.Nondegenerate) [FiniteDimensional (ZMod 2) V] {k : ℕ}
    (hk : 2 * k < finrank (ZMod 2) V) {b : ℕ → V} (hb : IsFam q θ k b) :
    ∃ w, q w = 1 ∧ ∀ i < k, polar q w (b i) = 0 ∧ polar q w (θ (b i)) = 0 := by
  set π : V →ₗ[ZMod 2] (Fin k → ZMod 2) × (Fin k → ZMod 2) :=
    LinearMap.prod (LinearMap.pi fun i : Fin k => (polarBilin q).flip (b i))
      (LinearMap.pi fun i : Fin k => (polarBilin q).flip (θ (b i))) with hπ
  have mem_ker : ∀ w, w ∈ LinearMap.ker π ↔
      ∀ i : Fin k, polar q w (b i) = 0 ∧ polar q w (θ (b i)) = 0 := by
    intro w
    simp only [LinearMap.mem_ker, hπ, LinearMap.coe_prod, Function.prod, Prod.mk_eq_zero,
      funext_iff, LinearMap.pi_apply, LinearMap.flip_apply, polarBilin_apply_apply,
      Pi.zero_apply]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  have hdim : 0 < finrank (ZMod 2) (LinearMap.ker π) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker π
    have h2 := Submodule.finrank_le (LinearMap.range π)
    rw [Module.finrank_prod, Module.finrank_fin_fun] at h2
    omega
  suffices hex : ∃ w ∈ LinearMap.ker π, q w = 1 by
    obtain ⟨w, hw, hw1⟩ := hex
    exact ⟨w, hw1, fun i hi => (mem_ker w).1 hw ⟨i, hi⟩⟩
  by_contra hne
  push Not at hne
  have hzero : ∀ w ∈ LinearMap.ker π, q w = 0 := fun w hw =>
    (zmod2_eq_zero_or_eq_one (q w)).resolve_right (hne w hw)
  have hbot : LinearMap.ker π ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hdim
    exact lt_irrefl 0 hdim
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨v, hv⟩ : ∃ v, polar q w v ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (hq.1 w fun n => by rw [polarBilin_apply_apply, h n])
  set u : V := ∑ i : Fin k, (polar q v (θ (b i)) • b i + polar q v (b i) • θ (b i)) with hu
  have hvu : v - u ∈ LinearMap.ker π := by
    refine (mem_ker _).2 fun i => ⟨?_, ?_⟩
    · rw [polar_sub_left, hu, hb.polar_comb_b hθq hθ3 hfix, sub_self]
    · rw [polar_sub_left, hu, hb.polar_comb_theta_b hθq hθ3 hfix, sub_self]
  have hwu : polar q w u = 0 := by
    rw [hu, polar_sum_right]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨h1, h2⟩ := (mem_ker w).1 hw i
    rw [polar_add_right, polar_smul_right, polar_smul_right, h1, h2, smul_zero, smul_zero,
      add_zero]
  have hwvu : polar q w (v - u) = 0 := by
    rw [polar, hzero _ (Submodule.add_mem _ hw hvu), hzero w hw, hzero _ hvu, sub_zero, sub_zero]
  apply hv
  rw [show v = u + (v - u) by abel, polar_add_right, hwu, hwvu, add_zero]

theorem exists_fam (hq : q.polarBilin.Nondegenerate) [FiniteDimensional (ZMod 2) V] :
    ∀ k, 2 * k ≤ finrank (ZMod 2) V → ∃ b : ℕ → V, IsFam q θ k b
  | 0, _ => ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | k + 1, hk => by
    obtain ⟨b, hb⟩ := exists_fam hq k (by omega)
    obtain ⟨w, hw1, hw⟩ := exists_next hθq hθ3 hfix hq (by omega) hb
    have hθw : ∀ i < k, polar q (θ w) (b i) = 0 := fun i hi => by
      rw [← polar_theta hθq, theta_theta hθq hθ3 hfix, polar_add_left, polar_theta hθq,
        (hw i hi).1, (hw i hi).2, add_zero]
    refine ⟨fun i => if i = k then w else b i, fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · by_cases hik : i = k
      · simp only [hik, if_true, hw1]
      · simp only [hik, if_false]
        exact hb.1 i (by omega)
    · by_cases hik : i = k
      · have hjk : j ≠ k := fun e => hij (hik.trans e.symm)
        simp only [hik, if_true, hjk, if_false]
        exact ⟨(hw j (by omega)).1, hθw j (by omega)⟩
      · by_cases hjk : j = k
        · simp only [hik, if_false, hjk, if_true]
          rw [polar_comm, (hw i (by omega)).1, polar_comm, (hw i (by omega)).2]
          exact ⟨rfl, rfl⟩
        · simp only [hik, if_false, hjk]
          exact hb.2 i (by omega) j (by omega) hij

variable {b : ℕ → V} (hb : IsFam q θ 6 b)
include hb

theorem polar_famMap_b (x : V12) (j : Fin 6) : polar q (famMap θ b x) (b j) = x (hi j) :=
  hb.polar_comb_b hθq hθ3 hfix (fun i => x (lo i)) (fun i => x (hi i)) j

theorem polar_famMap_theta_b (x : V12) (j : Fin 6) :
    polar q (famMap θ b x) (θ (b j)) = x (lo j) :=
  hb.polar_comb_theta_b hθq hθ3 hfix (fun i => x (lo i)) (fun i => x (hi i)) j

theorem famMap_injective : Function.Injective (famMap θ b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine ext_lo_hi (fun j => ?_) (fun j => ?_)
  · rw [← polar_famMap_theta_b hθq hθ3 hfix hb x j, hx, polar_zero_left]
    rfl
  · rw [← polar_famMap_b hθq hθ3 hfix hb x j, hx, polar_zero_left]
    rfl

theorem q_famMap (x : V12) : q (famMap θ b x) = q0 x := by
  have hp : ∀ i j : Fin 6, i ≠ j → polar q (b i) (b j) = 0 ∧ polar q (θ (b i)) (b j) = 0 ∧
      polar q (b i) (θ (b j)) = 0 ∧ polar q (θ (b i)) (θ (b j)) = 0 := fun i j hij => by
    have h := hb.2 i i.isLt j j.isLt (Fin.val_ne_of_ne hij)
    have h' := hb.2 j j.isLt i i.isLt (Fin.val_ne_of_ne (Ne.symm hij))
    exact ⟨h.1, h.2, by rw [polar_comm, h'.2], by rw [polar_theta hθq, h.1]⟩
  rw [famMap_apply, map_sum_of_orth q Finset.univ _ fun i _ j _ hij => ?_, q0]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hb.1 i i.isLt
    have h2 : polar q (b i) (θ (b i)) = 1 := by
      rw [polar_comm, hb.polar_theta_self hθq hθ3 hfix i.isLt]
    rw [QuadraticMap.map_add (⇑q), QuadraticMap.map_smul, QuadraticMap.map_smul, hθq, h1,
      polar_smul_left, polar_smul_right, h2, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, zmod2_mul_self, zmod2_mul_self]
    simp only [mul_one]
    ring
  · obtain ⟨h1, h2, h3, h4⟩ := hp i j hij
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, h1, h2, h3,
      h4, smul_zero, add_zero]

theorem theta_famMap (x : V12) : θ (famMap θ b x) = famMap θ b (theta0 x) := by
  simp only [famMap_apply, map_sum, map_add, map_smul, theta0_lo, theta0_hi,
    theta_theta hθq hθ3 hfix, smul_add, add_smul]
  exact Finset.sum_congr rfl fun i _ => by abel

end General

theorem exists_isometry_theta0 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 12) {θ : V →ₗ[ZMod 2] V}
    (hθq : ∀ v, q (θ v) = q v) (hθ3 : ∀ v, θ (θ (θ v)) = v) (hfix : ∀ v, θ v = v → v = 0) :
    ∃ φ : V ≃ₗ[ZMod 2] V12, (∀ v, q0 (φ v) = q v) ∧ ∀ v, φ (θ v) = theta0 (φ v) := by
  obtain ⟨b, hb⟩ := exists_fam hθq hθ3 hfix hq 6 (by omega)
  have hinj := famMap_injective hθq hθ3 hfix hb
  have hsurj : Function.Surjective (famMap θ b) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fin_fun, hV])).1 hinj
  set e := LinearEquiv.ofBijective (famMap θ b) ⟨hinj, hsurj⟩ with he
  have he' : ∀ v, famMap θ b (e.symm v) = v := fun v => e.apply_symm_apply v
  refine ⟨e.symm, fun v => ?_, fun v => hinj ?_⟩
  · rw [← q_famMap hθq hθ3 hfix hb, he']
  · rw [he', ← theta_famMap hθq hθ3 hfix hb, he']

end CFSG.GF2Type.Smith1979.GammaU
