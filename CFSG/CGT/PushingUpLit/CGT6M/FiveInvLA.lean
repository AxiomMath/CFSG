module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CFSG.Open.StatedDefs
public import CFSG.CGT.PushingUpLit.CGT6M.FiveLocal

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open Matrix

section Nil

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

@[expose] def invNil (M : Matrix n n K) (c : K) (v w : n → K) : Matrix n n K :=
  vecMulVec v w - c⁻¹ • vecMulVec (M *ᵥ v) (w ᵥ* M)

theorem mul_invNil (M : Matrix n n K) {c : K} (hc : c ≠ 0) (hM : M * M = c • 1) (v w : n → K) :
    M * invNil M c v w = -(invNil M c v w * M) := by
  have h1 : M *ᵥ (M *ᵥ v) = c • v := by
    rw [mulVec_mulVec, hM, smul_mulVec, one_mulVec]
  have h2 : (w ᵥ* M) ᵥ* M = c • w := by
    rw [vecMul_vecMul, hM, vecMul_smul, vecMul_one]
  simp only [invNil, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_vecMulVec, vecMulVec_mul, h1, h2, smul_vecMulVec, vecMulVec_smul, smul_smul,
    inv_mul_cancel₀ hc, one_smul]
  abel

theorem invNil_mul (M : Matrix n n K) {c : K} (hM : M * M = c • 1) (v w w' : n → K)
    (h1 : w ⬝ᵥ v = 0) (h2 : w ⬝ᵥ (M *ᵥ v) = 0) :
    invNil M c v w * invNil M c v w' = 0 := by
  have h3 : (w ᵥ* M) ⬝ᵥ v = 0 := by rw [← dotProduct_mulVec]; exact h2
  have h4 : (w ᵥ* M) ⬝ᵥ (M *ᵥ v) = 0 := by
    rw [← dotProduct_mulVec, mulVec_mulVec, hM, smul_mulVec, one_mulVec, dotProduct_smul, h1,
      smul_zero]
  simp only [invNil, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    vecMulVec_mul_vecMulVec, h1, h2, h3, h4, zero_smul]
  ext i j
  simp

omit [DecidableEq n] in
theorem invNil_mulVec (M : Matrix n n K) (c : K) (v w x : n → K) :
    invNil M c v w *ᵥ x = (w ⬝ᵥ x) • v - (c⁻¹ * (w ⬝ᵥ (M *ᵥ x))) • (M *ᵥ v) := by
  simp only [invNil, Matrix.sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    ← dotProduct_mulVec, mul_smul]

omit [DecidableEq n] in
theorem invNil_smul (M : Matrix n n K) (c s : K) (v w : n → K) :
    invNil M c v (s • w) = s • invNil M c v w := by
  simp only [invNil, vecMulVec_smul, smul_vecMul, smul_sub, smul_comm s c⁻¹]

omit [DecidableEq n] in
theorem invNil_add (M : Matrix n n K) (c : K) (v w w' : n → K) :
    invNil M c v (w + w') = invNil M c v w + invNil M c v w' := by
  simp only [invNil, vecMulVec_add, add_vecMul, smul_add]
  abel

theorem eq_zero_of_invNil_eq_zero (M : Matrix n n K) (c : K) {v w : n → K}
    (hv : LinearIndependent K ![v, M *ᵥ v]) (h : invNil M c v w = 0) : w = 0 := by
  rw [LinearIndependent.pair_iff] at hv
  ext i
  have h1 := congrArg (fun N => N *ᵥ (Pi.single i (1 : K) : n → K)) h
  simp only [invNil_mulVec, zero_mulVec] at h1
  have h2 := hv (w ⬝ᵥ Pi.single i 1) (-(c⁻¹ * (w ⬝ᵥ (M *ᵥ Pi.single i 1)))) (by
    rw [neg_smul, ← sub_eq_add_neg]
    exact h1)
  simpa [dotProduct_single] using h2.1

end Nil

section Unip

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

@[expose] def Tm (A B : Matrix n n K) (a b : K) : Matrix n n K := 1 + a • A + b • B

variable {A B : Matrix n n K}

theorem Tm_mul (hAA : A * A = 0) (hAB : A * B = 0) (hBA : B * A = 0) (hBB : B * B = 0)
    (a b a' b' : K) : Tm A B a b * Tm A B a' b' = Tm A B (a + a') (b + b') := by
  simp only [Tm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, hAA, hAB, hBA, hBB, smul_zero, add_smul]
  abel_nf

omit [Fintype n] in
theorem Tm_zero : Tm A B 0 0 = 1 := by simp [Tm]

@[expose] def Tu (hAA : A * A = 0) (hAB : A * B = 0) (hBA : B * A = 0) (hBB : B * B = 0)
    (a b : K) : GL n K :=
  ⟨Tm A B a b, Tm A B (-a) (-b),
    by rw [Tm_mul hAA hAB hBA hBB, add_neg_cancel, add_neg_cancel, Tm_zero],
    by rw [Tm_mul hAA hAB hBA hBB, neg_add_cancel, neg_add_cancel, Tm_zero]⟩

theorem Tu_mul (hAA : A * A = 0) (hAB : A * B = 0) (hBA : B * A = 0) (hBB : B * B = 0)
    (a b a' b' : K) :
    Tu hAA hAB hBA hBB a b * Tu hAA hAB hBA hBB a' b' = Tu hAA hAB hBA hBB (a + a') (b + b') :=
  Units.ext (Tm_mul hAA hAB hBA hBB a b a' b')

theorem Tu_inv (hAA : A * A = 0) (hAB : A * B = 0) (hBA : B * A = 0) (hBB : B * B = 0)
    (a b : K) : (Tu hAA hAB hBA hBB a b)⁻¹ = Tu hAA hAB hBA hBB (-a) (-b) :=
  inv_eq_of_mul_eq_one_right
    (by rw [Tu_mul, add_neg_cancel, add_neg_cancel]; exact Units.ext Tm_zero)

theorem Tu_conj (hAA : A * A = 0) (hAB : A * B = 0) (hBA : B * A = 0) (hBB : B * B = 0)
    (Mu : GL n K) (hMA : (Mu : Matrix n n K) * A = -(A * Mu))
    (hMB : (Mu : Matrix n n K) * B = -(B * Mu)) (a b : K) :
    Mu * Tu hAA hAB hBA hBB a b * Mu⁻¹ = Tu hAA hAB hBA hBB (-a) (-b) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  have h1 : (Mu : Matrix n n K) * (a • A) = -(a • A) * Mu := by
    rw [Matrix.mul_smul, hMA, Matrix.neg_mul, Matrix.smul_mul, smul_neg]
  have h2 : (Mu : Matrix n n K) * (b • B) = -(b • B) * Mu := by
    rw [Matrix.mul_smul, hMB, Matrix.neg_mul, Matrix.smul_mul, smul_neg]
  simp only [Units.val_mul, Tu, Tm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    h1, h2, neg_smul]

end Unip

section Proj

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type} [Field K] [CharP K 5]
  {A B : Matrix n n K}

@[expose] noncomputable def zi (K : Type) [Field K] [CharP K 5] : ZMod 5 →+* K :=
  ZMod.castHom (dvd_refl 5) K

@[expose] noncomputable def Ehom (hAA : A * A = 0) (hAB : A * B = 0) (hBA : B * A = 0)
    (hBB : B * B = 0) : C55 →* GL n K :=
  MonoidHom.mk' (fun u => Tu hAA hAB hBA hBB (zi K (Multiplicative.toAdd u).1)
    (zi K (Multiplicative.toAdd u).2)) (by
    intro u v
    rw [Tu_mul, toAdd_mul, Prod.fst_add, Prod.snd_add, map_add, map_add])

theorem c55_pow_five (u : C55) : u ^ 5 = 1 := by
  obtain ⟨⟨i, j⟩, rfl⟩ : ∃ w, u = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd u, rfl⟩
  rw [← ofAdd_nsmul]
  have h5 : (5 : ℕ) • ((i, j) : ZMod 5 × ZMod 5) = 0 := by
    have h5' : (5 : ZMod 5) = 0 := by decide
    ext <;> simp [h5']
  rw [h5]
  rfl

theorem det_Ehom_eq_one (hAA : A * A = 0) (hAB : A * B = 0) (hBA : B * A = 0) (hBB : B * B = 0)
    (u : C55) : ((Ehom hAA hAB hBA hBB u : GL n K) : Matrix n n K).det = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : ExpChar K 5 := ExpChar.prime Nat.prime_five
  have h1 : (Ehom hAA hAB hBA hBB u) ^ 5 = 1 := by
    rw [← map_pow, c55_pow_five, map_one]
  have h2 : (((Ehom hAA hAB hBA hBB u : GL n K) : Matrix n n K).det) ^ 5 = 1 ^ 5 := by
    rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, h1]
    simp
  exact frobenius_inj K 5 h2

end Proj

section ProjScalar

open CFSG.Open

variable {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Field K]

theorem scalar_sq_of_mk_sq {H : Subgroup (GL n K)} (h : H)
    (h1 : (QuotientGroup.mk h : StatedProj H) * QuotientGroup.mk h = 1) :
    ∃ c : K, c ≠ 0 ∧ ((h : GL n K) : Matrix n n K) * ((h : GL n K) : Matrix n n K) = c • 1 := by
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp h1
  refine ⟨(s : K), s.ne_zero, ?_⟩
  have := congrArg (fun g : GL n K => (g : Matrix n n K)) hs
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Subgroup.coe_mul, Units.val_mul] at this
  rw [← this, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem nilp_eq_zero_of_add_one_scalar [Nonempty n] {N : Matrix n n K} (hN : N * N = 0) {s : K}
    (h : 1 + N = s • 1) : N = 0 := by
  have h1 : N = (s - 1) • 1 := by
    rw [sub_smul, one_smul]
    exact eq_sub_of_add_eq' h
  have h2 : (s - 1) * (s - 1) = 0 := by
    rw [h1, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul] at hN
    obtain ⟨i⟩ := ‹Nonempty n›
    have := congrFun (congrFun hN i) i
    simpa using this
  rw [h1, mul_self_eq_zero.mp h2, zero_smul]

theorem scalar_of_mk_eq_one {H : Subgroup (GL n K)} (g : H)
    (h1 : (QuotientGroup.mk g : StatedProj H) = 1) :
    ∃ s : K, ((g : GL n K) : Matrix n n K) = s • 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp h1
  refine ⟨(u : K), ?_⟩
  have := congrArg (fun g : GL n K => (g : Matrix n n K)) hu
  simp only [Matrix.GeneralLinearGroup.coe_scalar] at this
  rw [← this, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem not_scalar_of_mk_ne_one [Nonempty n] {H : Subgroup (GL n K)} (h : H)
    (h1 : (QuotientGroup.mk h : StatedProj H) ≠ 1) :
    ∀ a : K, ((h : GL n K) : Matrix n n K) ≠ a • 1 := by
  intro a ha
  apply h1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have ha0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨i⟩ := ‹Nonempty n›
    have h2 := congrArg (fun g : Matrix n n K => g i i) (Units.mul_inv (h : GL n K))
    simp [ha] at h2
  refine MonoidHom.mem_range.mpr ⟨Units.mk0 a ha0, Units.ext ?_⟩
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  rw [ha, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

end ProjScalar

section QLevel

open CFSG.Open

variable {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Field K] [CharP K 5]
  {A B : Matrix n n K}

theorem inverted_c55_proj [Nonempty n] (H : Subgroup (GL n K)) (Mu : GL n K) (hMH : Mu ∈ H)
    (hAA : A * A = 0) (hAB : A * B = 0) (hBA : B * A = 0) (hBB : B * B = 0)
    (hMA : (Mu : Matrix n n K) * A = -(A * Mu)) (hMB : (Mu : Matrix n n K) * B = -(B * Mu))
    (hH : ∀ a b : ZMod 5, Tu hAA hAB hBA hBB (zi K a) (zi K b) ∈ H)
    (hind : ∀ a b : ZMod 5, zi K a • A + zi K b • B = 0 → a = 0 ∧ b = 0) :
    ∃ Φ : C55 →* StatedProj H, Function.Injective Φ ∧
      ∀ u : C55, (QuotientGroup.mk (⟨Mu, hMH⟩ : H) : StatedProj H) * Φ u *
        (QuotientGroup.mk (⟨Mu, hMH⟩ : H) : StatedProj H)⁻¹ = (Φ u)⁻¹ := by
  classical
  have hmem : ∀ u : C55, Ehom hAA hAB hBA hBB u ∈ H := fun u => by
    obtain ⟨⟨a, b⟩, rfl⟩ : ∃ w, u = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd u, rfl⟩
    exact hH a b
  let E' : C55 →* H := (Ehom hAA hAB hBA hBB).codRestrict H hmem
  refine ⟨(QuotientGroup.mk' ((StatedScalars n K).subgroupOf H)).comp E', ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro u hu
    obtain ⟨⟨a, b⟩, rfl⟩ : ∃ w, u = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd u, rfl⟩
    have h1 : E' (Multiplicative.ofAdd (a, b)) ∈ (StatedScalars n K).subgroupOf H :=
      (QuotientGroup.eq_one_iff _).mp hu
    rw [Subgroup.mem_subgroupOf] at h1
    obtain ⟨s, hs⟩ := (MonoidHom.mem_range).mp h1
    have h2 : Matrix.scalar n (s : K) = 1 + (zi K a • A + zi K b • B) := by
      have := congrArg (fun g : GL n K => (g : Matrix n n K)) hs
      simp only [Matrix.GeneralLinearGroup.coe_scalar] at this
      rw [this]
      show (Tu hAA hAB hBA hBB (zi K a) (zi K b) : Matrix n n K) = _
      simp only [Tu, Tm, add_assoc]
    have h3 : (zi K a • A + zi K b • B) = Matrix.scalar n ((s : K) - 1) := by
      rw [map_sub, h2, map_one]
      abel
    have h4 : (zi K a • A + zi K b • B) * (zi K a • A + zi K b • B) = 0 := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hAA, hAB, hBA,
        hBB, smul_zero, add_zero]
    have h5 : ((s : K) - 1) * ((s : K) - 1) = 0 := by
      have h6 := h4
      rw [h3, ← map_mul] at h6
      obtain ⟨i⟩ := ‹Nonempty n›
      have := congrFun (congrFun h6 i) i
      simpa [Matrix.scalar_apply] using this
    have h7 : (s : K) - 1 = 0 := mul_self_eq_zero.mp h5
    rw [h7, map_zero] at h3
    obtain ⟨ha, hb⟩ := hind a b h3
    rw [ha, hb]
    rfl
  · intro u
    have hc : (⟨Mu, hMH⟩ : H) * E' u * (⟨Mu, hMH⟩ : H)⁻¹ = (E' u)⁻¹ := by
      apply Subtype.ext
      obtain ⟨⟨a, b⟩, rfl⟩ : ∃ w, u = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd u, rfl⟩
      show Mu * Tu hAA hAB hBA hBB (zi K a) (zi K b) * Mu⁻¹ =
        (Tu hAA hAB hBA hBB (zi K a) (zi K b))⁻¹
      rw [Tu_conj hAA hAB hBA hBB Mu hMA hMB, Tu_inv]
    show QuotientGroup.mk (⟨Mu, hMH⟩ : H) * QuotientGroup.mk (E' u) *
      (QuotientGroup.mk (⟨Mu, hMH⟩ : H))⁻¹ = (QuotientGroup.mk (E' u))⁻¹
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc,
      QuotientGroup.mk_inv]

end QLevel

section LA

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

theorem exists_linearIndependent_of_not_scalar (M : Matrix n n K) (hM : ∀ a : K, M ≠ a • 1) :
    ∃ v : n → K, LinearIndependent K ![v, M *ᵥ v] := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := Matrix.mulVecLin M) (fun v => hcon v)
  apply hM a
  ext i j
  have := congrArg (fun f : Module.End K (n → K) => f (Pi.single j 1) i) ha
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply,
    eq_comm] using this

theorem exists_two_annihilators (v u : Fin 4 → K) :
    ∃ w₁ w₂ : Fin 4 → K, LinearIndependent K ![w₁, w₂] ∧ w₁ ⬝ᵥ v = 0 ∧ w₁ ⬝ᵥ u = 0 ∧
      w₂ ⬝ᵥ v = 0 ∧ w₂ ⬝ᵥ u = 0 := by
  let N : Matrix (Fin 4) (Fin 2) K := Matrix.of fun i j => ![v, u] j i
  let Φ : (Fin 4 → K) →ₗ[K] (Fin 2 → K) := Matrix.vecMulLinear N
  have hrank := LinearMap.finrank_range_add_finrank_ker Φ
  have h1 : Module.finrank K (LinearMap.range Φ) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    simpa using this
  have h2 : 1 < Module.finrank K (LinearMap.ker Φ) := by
    simp only [Module.finrank_fin_fun] at hrank
    omega
  have hpos : 0 < Module.finrank K (LinearMap.ker Φ) := by omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank h2 hx
  have hker : ∀ w : LinearMap.ker Φ, (w : Fin 4 → K) ⬝ᵥ v = 0 ∧ (w : Fin 4 → K) ⬝ᵥ u = 0 := by
    intro w
    have hw : Φ (w : Fin 4 → K) = 0 := w.2
    have e0 := congrFun hw 0
    have e1 := congrFun hw 1
    simp only [Φ, Matrix.vecMulLinear_apply, N, Matrix.vecMul, dotProduct, Matrix.of_apply,
      Pi.zero_apply] at e0 e1
    exact ⟨by simpa [dotProduct] using e0, by simpa [dotProduct] using e1⟩
  refine ⟨(x : Fin 4 → K), (y : Fin 4 → K), ?_, (hker x).1, (hker x).2, (hker y).1, (hker y).2⟩
  rw [LinearIndependent.pair_iff] at hy ⊢
  intro s t hst
  apply hy s t
  apply Subtype.ext
  simpa using hst

end LA

end CFSG.CGT.PushingUpLit.CGT6M
