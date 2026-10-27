module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryVectorCount
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LinearGroups

open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type*} [Field K]

section Frames

variable {V : Type*} [AddCommGroup V] [Module K V] {σ : K →+* K}

@[expose] def orthonormalFrames (B : V →ₛₗ[σ] V →ₗ[K] K) (r : ℕ) : Set (Fin r → V) :=
  {v | ∀ i j, B (v i) (v j) = if i = j then 1 else 0}

theorem mem_orthonormalFrames {B : V →ₛₗ[σ] V →ₗ[K] K} {r : ℕ} {v : Fin r → V} :
    v ∈ orthonormalFrames B r ↔ ∀ i j, B (v i) (v j) = if i = j then 1 else 0 :=
  Iff.rfl

theorem sesq_sum_smul_of_mem {B : V →ₛₗ[σ] V →ₗ[K] K} {r : ℕ} {v : Fin r → V}
    (hv : v ∈ orthonormalFrames B r) (a b : Fin r → K) :
    B (∑ i, a i • v i) (∑ j, b j • v j) = ∑ i, σ (a i) * b i := by
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    mem_orthonormalFrames.mp hv, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, RingHom.id_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem isometry_of_mem_orthonormalFrames {B : V →ₛₗ[σ] V →ₗ[K] K} {r : ℕ}
    (e : Module.Basis (Fin r) K V) (he : ⇑e ∈ orthonormalFrames B r) {φ : V →ₗ[K] V}
    (hφ : (fun i => φ (e i)) ∈ orthonormalFrames B r) (x y : V) : B (φ x) (φ y) = B x y := by
  have hexp : ∀ z : V, φ z = ∑ i, e.repr z i • φ (e i) := fun z => by
    conv_lhs => rw [← e.sum_repr z]
    simp only [map_sum, map_smul]
  have hxy := sesq_sum_smul_of_mem he (e.repr x) (e.repr y)
  rw [e.sum_repr, e.sum_repr] at hxy
  rw [hexp x, hexp y, sesq_sum_smul_of_mem hφ, hxy]

theorem isUnit_of_isometry [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K}
    (hBl : B.SeparatingLeft) {φ : V →ₗ[K] V} (hφ : ∀ x y, B (φ x) (φ y) = B x y) : IsUnit φ := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  exact hBl x fun y => by rw [← hφ, hx, map_zero, LinearMap.zero_apply]

@[expose] noncomputable def isometryUnit [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K}
    (hBl : B.SeparatingLeft) {φ : V →ₗ[K] V} (hφ : ∀ x y, B (φ x) (φ y) = B x y) :
    sesqUnitaryGroup B :=
  ⟨(isUnit_of_isometry hBl hφ).unit,
    mem_sesqUnitaryGroup.mpr fun x y => by rw [IsUnit.unit_spec]; exact hφ x y⟩

@[simp] theorem coe_isometryUnit [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K}
    (hBl : B.SeparatingLeft) {φ : V →ₗ[K] V} (hφ : ∀ x y, B (φ x) (φ y) = B x y) :
    (((isometryUnit hBl hφ : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) = φ :=
  IsUnit.unit_spec _

theorem card_sesqUnitaryGroup_eq [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K}
    (hBl : B.SeparatingLeft) {r : ℕ} (e : Module.Basis (Fin r) K V)
    (he : ⇑e ∈ orthonormalFrames B r) :
    Nat.card (sesqUnitaryGroup B) = Nat.card (orthonormalFrames B r) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨fun i => ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (e i),
        mem_orthonormalFrames.mpr fun i j => by
          rw [mem_sesqUnitaryGroup.mp g.2]
          exact mem_orthonormalFrames.mp he i j⟩
      invFun := fun v => isometryUnit hBl (φ := e.constr K v.1)
        (isometry_of_mem_orthonormalFrames e he (by
          simp only [Module.Basis.constr_basis]
          exact v.2))
      left_inv := fun g => ?_
      right_inv := fun v => ?_ }
  · refine Subtype.ext (Units.ext (e.ext fun i => ?_))
    rw [coe_isometryUnit, Module.Basis.constr_basis]
  · refine Subtype.ext (funext fun i => ?_)
    simp only [coe_isometryUnit, Module.Basis.constr_basis]

theorem card_orthonormalFrames_cons {B : V →ₛₗ[σ] V →ₗ[K] K} (hB : B.IsSymm) {x : V}
    (hx : B x x = 1) (r : ℕ) :
    Nat.card {v : orthonormalFrames B (r + 1) // v.1 0 = x} =
      Nat.card (orthonormalFrames
        (B.domRestrict₁₂ (LinearMap.ker (B x)) (LinearMap.ker (B x))) r) := by
  refine Nat.card_congr
    { toFun := fun v => ⟨fun i => ⟨v.1.1 i.succ, by
          have h0 := mem_orthonormalFrames.mp v.1.2 0 i.succ
          rw [v.2, ite_eq_right (Fin.succ_ne_zero i).symm] at h0
          exact LinearMap.mem_ker.mpr h0⟩,
        mem_orthonormalFrames.mpr fun i j => by
          rw [LinearMap.domRestrict₁₂_apply, mem_orthonormalFrames.mp v.1.2]
          simp only [Fin.succ_inj]⟩
      invFun := fun w => ⟨⟨Fin.cons x fun i => (w.1 i : V), mem_orthonormalFrames.mpr ?_⟩,
        by simp⟩
      left_inv := fun v => ?_
      right_inv := fun w => ?_ }
  · have hw : ∀ i, B x (w.1 i) = 0 := fun i => LinearMap.mem_ker.mp (w.1 i).2
    have hw' : ∀ i, B (w.1 i) x = 0 := fun i => by rw [← hB.eq x, hw, map_zero]
    have hww : ∀ i j, B (w.1 i) (w.1 j) = if i = j then 1 else 0 := fun i j =>
      mem_orthonormalFrames.mp w.2 i j
    intro i j
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [hx, hw, hw', hww, (Fin.succ_ne_zero _).symm, Fin.succ_ne_zero]
  · refine Subtype.ext (Subtype.ext ?_)
    change Fin.cons x (Fin.tail v.1.1) = v.1.1
    calc Fin.cons x (Fin.tail v.1.1) = Fin.cons (v.1.1 0) (Fin.tail v.1.1) := by rw [v.2]
      _ = v.1.1 := Fin.cons_self_tail _
  · exact Subtype.ext (funext fun i => Subtype.ext (by simp))

end Frames

section Unitary

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem separatingLeft_ker_of_norm_one [FiniteDimensional K V] (h : UnitaryFieldData p f K)
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft) {x : V}
    (hx : B x x = 1) :
    (B.domRestrict₁₂ (LinearMap.ker (B x)) (LinearMap.ker (B x))).SeparatingLeft ∧
      Module.finrank K (LinearMap.ker (B x)) + 1 = Module.finrank K V := by
  refine ⟨?_, ?_⟩
  · rintro ⟨w, hw⟩ hw0
    have hwx : B w x = 0 := by rw [← hB.eq x w, LinearMap.mem_ker.mp hw, map_zero]
    refine Subtype.ext (hBl w fun y => ?_)
    have hy : y - B x y • x ∈ LinearMap.ker (B x) := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hx, smul_eq_mul, mul_one, sub_self]
    have h1 := hw0 ⟨_, hy⟩
    simpa only [LinearMap.domRestrict₁₂_apply, map_sub, map_smul, hwx, smul_zero,
      sub_zero] using h1
  · have hsurj : LinearMap.range (B x) = ⊤ := by
      rw [LinearMap.range_eq_top]
      exact fun c => ⟨c • x, by rw [map_smul, hx, smul_eq_mul, mul_one]⟩
    have := LinearMap.finrank_range_add_finrank_ker (B x)
    rw [hsurj, finrank_top, Module.finrank_self] at this
    omega

theorem card_orthonormalFrames (h : UnitaryFieldData p f K) (n : ℕ) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : Module.finrank K V = n) :
    (Nat.card (orthonormalFrames B n) : ℤ) = ∏ i ∈ Finset.range n,
      ((p ^ f : ℕ) : ℤ) ^ i * (((p ^ f : ℕ) : ℤ) ^ (i + 1) - (-1) ^ (i + 1)) := by
  induction n generalizing V with
  | zero =>
    rw [Finset.prod_range_zero, Nat.cast_eq_one, Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩,
      ⟨⟨Fin.elim0, mem_orthonormalFrames.mpr fun i => i.elim0⟩⟩⟩
  | succ n ih =>
    classical
    have := h.finite
    have : Finite V := Module.finite_of_finite K
    have : Fintype {x : V // B x x = 1} := Fintype.ofFinite _
    let F : orthonormalFrames B (n + 1) → {x : V // B x x = 1} := fun v =>
      ⟨v.1 0, by simpa using mem_orthonormalFrames.mp v.2 0 0⟩
    have hfib : ∀ x : {x : V // B x x = 1}, (Nat.card {v // F v = x} : ℤ) =
        ∏ i ∈ Finset.range n,
          ((p ^ f : ℕ) : ℤ) ^ i * (((p ^ f : ℕ) : ℤ) ^ (i + 1) - (-1) ^ (i + 1)) := by
      intro x
      obtain ⟨hsep, hdim⟩ := separatingLeft_ker_of_norm_one h hB hBl x.2
      rw [Nat.card_congr (Equiv.subtypeEquivRight fun v => Subtype.ext_iff (a1 := F v) (a2 := x)),
        card_orthonormalFrames_cons hB x.2 n]
      exact ih (hB.domRestrict _) hsep (by omega)
    have hcount := (unitary_hermitian_vector_count h hB hBl hn (by omega)).2.1 1
      h.fixedField.one_mem one_ne_zero
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv F), Nat.card_sigma, Nat.cast_sum,
      Finset.sum_congr rfl fun x _ => hfib x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, hcount, Finset.prod_range_succ, Nat.add_sub_cancel]
    ring

theorem norm_det_of_isometry (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K} {r : ℕ}
    (e : Module.Basis (Fin r) K V) (he : ⇑e ∈ orthonormalFrames B r) {φ : V →ₗ[K] V}
    (hφ : ∀ x y, B (φ x) (φ y) = B x y) : h.norm (LinearMap.det φ) = 1 := by
  obtain ⟨M, hM⟩ : ∃ M, M = LinearMap.toMatrix e e φ := ⟨_, rfl⟩
  have hcol : ∀ j, φ (e j) = ∑ k, M k j • e k := fun j => by
    rw [hM]
    simp only [LinearMap.toMatrix_apply, e.sum_repr]
  have hMM : (M.map h.bar).transpose * M = 1 := by
    ext i j
    have hij := hφ (e i) (e j)
    rw [hcol i, hcol j, sesq_sum_smul_of_mem he, mem_orthonormalFrames.mp he] at hij
    rw [Matrix.mul_apply, Matrix.one_apply, ← hij]
    rfl
  have hdet := congrArg Matrix.det hMM
  rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Matrix.det_one, hM, LinearMap.det_toMatrix] at hdet
  rw [UnitaryFieldData.norm, mul_comm]
  exact hdet

theorem exists_isometry_det_eq (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K} {r : ℕ}
    (e : Module.Basis (Fin (r + 1)) K V) (he : ⇑e ∈ orthonormalFrames B (r + 1)) {c : K}
    (hc : h.norm c = 1) :
    ∃ φ : V →ₗ[K] V, (∀ x y, B (φ x) (φ y) = B x y) ∧ LinearMap.det φ = c := by
  classical
  obtain ⟨d, hd⟩ : ∃ d : Fin (r + 1) → K, d = Function.update (1 : Fin (r + 1) → K) 0 c :=
    ⟨_, rfl⟩
  have hdn : ∀ i, d i * h.bar (d i) = 1 := by
    intro i
    by_cases hi : i = 0
    · rw [hd, hi, Function.update_self]
      exact hc
    · rw [hd, Function.update_of_ne hi, Pi.one_apply, map_one, one_mul]
  obtain ⟨φ, hφ⟩ : ∃ φ : V →ₗ[K] V, φ = Matrix.toLin e e (Matrix.diagonal d) := ⟨_, rfl⟩
  have hφe : ∀ i, φ (e i) = d i • e i := fun i => by
    rw [hφ, Matrix.toLin_self]
    simp [Matrix.diagonal_apply]
  refine ⟨φ, isometry_of_mem_orthonormalFrames e he (mem_orthonormalFrames.mpr fun i j => ?_), ?_⟩
  · simp only [hφe, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, mem_orthonormalFrames.mp he,
      RingHom.id_apply]
    split_ifs with hij
    · subst hij
      linear_combination hdn i
    · simp only [mul_zero]
  · rw [hφ, LinearMap.det_toLin, Matrix.det_diagonal, Fin.prod_univ_succ, hd,
      Function.update_self]
    simp [Fin.succ_ne_zero]

@[expose] noncomputable def unitaryDet {σ : K →+* K} (B : V →ₛₗ[σ] V →ₗ[K] K) :
    sesqUnitaryGroup B →* Kˣ :=
  (Units.map (LinearMap.det : (V →ₗ[K] V) →* K)).comp (sesqUnitaryGroup B).subtype

theorem unitaryDet_apply {σ : K →+* K} (B : V →ₛₗ[σ] V →ₗ[K] K) (g : sesqUnitaryGroup B) :
    ((unitaryDet B g : Kˣ) : K) =
      LinearMap.det (((g : LinearMap.GeneralLinearGroup K V)) : V →ₗ[K] V) :=
  rfl

end Unitary

section Arithmetic

theorem prod_range_eq_pow_mul_prod_Icc (Q : ℤ) (n : ℕ) :
    ∏ i ∈ Finset.range n, Q ^ i * (Q ^ (i + 1) - (-1) ^ (i + 1)) =
      Q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 1 n, (Q ^ i - (-1) ^ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Finset.prod_Icc_succ_top (by omega)]
    have hexp : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
      have h1 : n * (n - 1) = n * n - n := Nat.mul_sub_one n n
      have h2 : (n + 1) * (n + 1 - 1) = n * n + n := by
        rw [Nat.add_sub_cancel]
        ring
      have h3 : n ≤ n * n := Nat.le_mul_self n
      rw [h1, h2]
      omega
    rw [hexp, pow_add]
    ring

theorem prod_Icc_one_eq_mul (g : ℕ → ℤ) {n : ℕ} (hn : 1 ≤ n) :
    ∏ i ∈ Finset.Icc 1 n, g i = g 1 * ∏ i ∈ Finset.Icc 2 n, g i := by
  rw [Finset.Icc_eq_cons_Ioc hn, Finset.prod_cons]
  rfl

theorem not_dvd_prod_pow_sub_neg_one_pow (hp : p.Prime) (hf : 1 ≤ f) (s : Finset ℕ)
    (hs : ∀ i ∈ s, 1 ≤ i) : ¬ (p : ℤ) ∣ ∏ i ∈ s, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  intro hd
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finsetProd_iff hpZ _).mp hd
  have hq : (p : ℤ) ∣ ((p ^ f : ℕ) : ℤ) ^ i := by
    push_cast
    exact dvd_pow (dvd_pow_self _ (by omega)) (by have := hs i hi; omega)
  have h1 : (p : ℤ) ∣ (-1) ^ i := by simpa using dvd_sub hq hdi
  exact hpZ.not_isUnit (isUnit_of_dvd_unit h1 (isUnit_neg_one.pow i))

theorem pow_factorization_eq_of_eq_mul (hp : p.Prime) {N a : ℕ} {P : ℤ}
    (ha : (a : ℤ) = ((p ^ f : ℕ) : ℤ) ^ N * P) (hP : ¬ (p : ℤ) ∣ P) :
    p ^ a.factorization p = (p ^ f) ^ N := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact hP (dvd_zero _)
  have ha' : a = p ^ (f * N) * P.natAbs := by
    have := congrArg Int.natAbs ha
    rwa [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, ← pow_mul] at this
  have hPn : ¬ p ∣ P.natAbs := fun hd => hP (Int.natCast_dvd.mpr hd)
  rw [ha', Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (Int.natAbs_ne_zero.mpr hP0),
    Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hPn, add_zero, pow_mul]

end Arithmetic

end CFSG.LinearGroups
