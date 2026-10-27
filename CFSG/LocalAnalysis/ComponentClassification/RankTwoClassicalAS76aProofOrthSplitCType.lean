module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplit
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open scoped Matrix

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] def sqZeroGL (T : Matrix ι ι K) (hT : T * T = 0) : GL ι K where
  val := 1 + T
  inv := 1 - T
  val_inv := by simp [add_mul, mul_sub, hT]
  inv_val := by simp [sub_mul, mul_add, hT]

theorem coe_sqZeroGL (T : Matrix ι ι K) (hT : T * T = 0) :
    (sqZeroGL T hT : Matrix ι ι K) = 1 + T := rfl

theorem sqZeroGL_mul {T T' : Matrix ι ι K} (hT : T * T = 0) (hT' : T' * T' = 0)
    (hTT : T * T' = 0) (hTT' : (T + T') * (T + T') = 0) :
    sqZeroGL T hT * sqZeroGL T' hT' = sqZeroGL (T + T') hTT' := by
  apply Units.ext
  simp only [Units.val_mul, coe_sqZeroGL]
  rw [add_mul, one_mul, mul_add, mul_one, hTT, add_zero]
  abel

theorem commRank_sqZeroGL (T : Matrix ι ι K) (hT : T * T = 0) :
    commRank (sqZeroGL T hT) = T.rank := by
  rw [commRank, coe_sqZeroGL, add_sub_cancel_left]

theorem sqZeroGL_sq [CharP K 2] (T : Matrix ι ι K) (hT : T * T = 0) :
    sqZeroGL T hT ^ 2 = 1 := by
  have hTT : T + T = 0 := by rw [← two_smul K T, CharTwo.two_eq_zero, zero_smul]
  apply Units.ext
  rw [pow_two, Units.val_mul, coe_sqZeroGL, Units.val_one, add_mul, one_mul, mul_add, mul_one, hT,
    add_zero, add_assoc, hTT, add_zero]

theorem sqZeroGL_ne_one {T : Matrix ι ι K} (hT : T * T = 0) (hT0 : T ≠ 0) :
    sqZeroGL T hT ≠ 1 := by
  intro h
  have h1 := congrArg (fun X : GL ι K => (X : Matrix ι ι K)) h
  simp only [coe_sqZeroGL, Units.val_one, add_eq_left] at h1
  exact hT0 h1

theorem orderOf_sqZeroGL [CharP K 2] {T : Matrix ι ι K} (hT : T * T = 0) (hT0 : T ≠ 0) :
    orderOf (sqZeroGL T hT) = 2 :=
  orderOf_eq_prime (sqZeroGL_sq T hT) (sqZeroGL_ne_one hT hT0)

@[expose] noncomputable def rankOneMat (φ : (ι → K) →ₗ[K] K) (w : ι → K) : Matrix ι ι K :=
  LinearMap.toMatrix' (φ.smulRight w)

theorem rankOneMat_mulVec (φ : (ι → K) →ₗ[K] K) (w v : ι → K) :
    rankOneMat φ w *ᵥ v = φ v • w := by
  rw [rankOneMat, LinearMap.toMatrix'_mulVec, LinearMap.smulRight_apply]

section Involution

variable (Q : QuadraticForm K (ι → K)) {N : Matrix ι ι K}

theorem polar_mulVec_add (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) (u v : ι → K) :
    Q.polarBilin u (N *ᵥ v) + Q.polarBilin (N *ᵥ u) v + Q.polarBilin (N *ᵥ u) (N *ᵥ v) = 0 := by
  have h := polarBilin_mulVec_of_isometry Q (D := 1 + N) (fun w => by
    rw [add_mulVec, one_mulVec]; exact hiso w) u v
  rw [add_mulVec, add_mulVec, one_mulVec, one_mulVec] at h
  simp only [map_add, LinearMap.add_apply] at h
  linear_combination h

theorem polar_mulVec_mulVec (hN : N * N = 0) (hiso : ∀ v, Q (v + N *ᵥ v) = Q v)
    (u v : ι → K) : Q.polarBilin (N *ᵥ u) (N *ᵥ v) = 0 := by
  have h := polar_mulVec_add Q hiso u (N *ᵥ v)
  rwa [mulVec_mulVec, hN, zero_mulVec, map_zero, map_zero, add_zero, zero_add] at h

theorem polar_mulVec_adj [CharP K 2] (hN : N * N = 0) (hiso : ∀ v, Q (v + N *ᵥ v) = Q v)
    (u v : ι → K) : Q.polarBilin (N *ᵥ u) v = Q.polarBilin u (N *ᵥ v) := by
  have h := polar_mulVec_add Q hiso u v
  rw [polar_mulVec_mulVec Q hN hiso, add_zero, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
  exact h.symm

omit [DecidableEq ι] in
theorem polar_self_mulVec [CharP K 2] (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) (v : ι → K) :
    Q.polarBilin v (N *ᵥ v) = Q (N *ᵥ v) := by
  have h := hiso v
  rw [quad_add, add_assoc, add_eq_left, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
  exact h.symm

variable [Finite K] [CharP K 2]

theorem exists_sqrt_vector (hQ : Q.polarBilin.Nondegenerate) (hN : N * N = 0)
    (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) :
    ∃ z : ι → K, ∀ v, Q.polarBilin v z ^ 2 = Q (N *ᵥ v) := by
  set s := (frobeniusEquiv K 2).symm with hs
  have hss : ∀ x : K, s x ^ 2 = x := fun x => by
    have h := frobenius_apply_frobeniusEquiv_symm K 2 x
    rwa [frobenius_def] at h
  have hsc : ∀ c : K, s (c * c) = c := fun c => by
    have h := frobeniusEquiv_symm_apply_frobenius K 2 c
    rwa [frobenius_def, pow_two] at h
  let lam : (ι → K) →ₗ[K] K :=
    { toFun := fun v => s (Q (N *ᵥ v))
      map_add' := fun u v => by
        rw [mulVec_add, quad_add, polar_mulVec_mulVec Q hN hiso, add_zero, map_add]
      map_smul' := fun c v => by
        rw [mulVec_smul, QuadraticMap.map_smul, smul_eq_mul, map_mul, hsc, RingHom.id_apply,
          smul_eq_mul] }
  refine ⟨(LinearMap.BilinForm.toDual Q.polarBilin hQ).symm lam, fun v => ?_⟩
  rw [polarBilin_comm, ← LinearMap.BilinForm.toDual_def hQ, LinearEquiv.apply_symm_apply]
  exact hss _

variable {Q}
variable (hQ : Q.polarBilin.Nondegenerate) (hN : N * N = 0)
  (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) {z : ι → K}
  (hz : ∀ v, Q.polarBilin v z ^ 2 = Q (N *ᵥ v))
include hN hiso hz

omit hQ hiso [DecidableEq ι] [Finite K] [CharP K 2] in
theorem polar_mulVec_sqrt_vector (w : ι → K) : Q.polarBilin (N *ᵥ w) z = 0 := by
  have h := hz (N *ᵥ w)
  rw [mulVec_mulVec, hN, zero_mulVec, map_zero] at h
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h

omit [Finite K] in
include hQ in
theorem mulVec_sqrt_vector : N *ᵥ z = 0 := by
  refine hQ.2 _ fun w => ?_
  rw [← polar_mulVec_adj Q hN hiso]
  exact polar_mulVec_sqrt_vector hN hz w

omit [Finite K] in
include hQ in
theorem exists_mulVec_eq_of_sqrt_vector : ∃ z' : ι → K, N *ᵥ z' = z := by
  have hmem : Q.polarBilin.flip z ∈ (LinearMap.ker N.mulVecLin).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    have h := hz v
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
    rw [hv, map_zero] at h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨μ, hμ⟩ := hmem
  set w₀ := (LinearMap.BilinForm.toDual Q.polarBilin hQ).symm μ with hw₀
  refine ⟨w₀, ?_⟩
  have hkey : ∀ v, Q.polarBilin v z = Q.polarBilin v (N *ᵥ w₀) := by
    intro v
    have h1 : μ (N *ᵥ v) = Q.polarBilin v z := by
      simpa using congrArg (fun f : Module.Dual K (ι → K) => f v) hμ
    rw [← h1, ← polar_mulVec_adj Q hN hiso, polarBilin_comm,
      ← LinearMap.BilinForm.toDual_def hQ, hw₀, LinearEquiv.apply_symm_apply]
  have h0 := hQ.2 (z - N *ᵥ w₀) fun v => by rw [map_sub, hkey, sub_self]
  exact (sub_eq_zero.mp h0).symm

omit [Finite K] in
include hQ in
theorem quad_sqrt_vector_sq : Q z ^ 2 = Q z := by
  obtain ⟨z', rfl⟩ := exists_mulVec_eq_of_sqrt_vector hQ hN hiso hz
  have h1 := hz z'
  rw [polar_self_mulVec Q hiso] at h1
  exact h1

end Involution

section Dickson

variable {Q : QuadraticForm K (ι → K)} [CharP K 2]

noncomputable abbrev glToLin : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))

omit [CharP K 2] in
theorem glToLin_apply (X : GL ι K) (v : ι → K) : glToLin X v = (X : Matrix ι ι K) *ᵥ v := rfl

omit [CharP K 2] in
theorem commSpace_glToLin (X : GL ι K) :
    commSpace (glToLin X) = LinearMap.range ((X : Matrix ι ι K) - 1).mulVecLin := by
  ext v
  simp

omit [CharP K 2] in
theorem finrank_commSpace_glToLin (X : GL ι K) :
    finrank K (commSpace (glToLin X)) = commRank X := by
  rw [commRank, Matrix.rank, ← commSpace_glToLin]

omit [CharP K 2] in
theorem glToLin_mem_orthogonalGroup {X : GL ι K} (hX : ∀ v, Q ((X : Matrix ι ι K) *ᵥ v) = Q v) :
    glToLin X ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by rw [glToLin_apply]; exact hX v

theorem quad_eq_zero_of_sqrt_vector (hQ : Q.polarBilin.Nondegenerate) {M : GL ι K}
    (hM : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v) (hN : ((M : Matrix ι ι K) - 1) *
      ((M : Matrix ι ι K) - 1) = 0) (hev : Even (commRank M)) {z : ι → K}
    (hz : ∀ v, Q.polarBilin v z ^ 2 = Q (((M : Matrix ι ι K) - 1) *ᵥ v)) : Q z = 0 := by
  set N := (M : Matrix ι ι K) - 1 with hNdef
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have hiso : ∀ v, Q (v + N *ᵥ v) = Q v := fun v => by
    have h1 : v + N *ᵥ v = (M : Matrix ι ι K) *ᵥ v := by rw [hMN, add_mulVec, one_mulVec]
    rw [h1]
    exact hM v
  have hsq := quad_sqrt_vector_sq hQ hN hiso hz
  by_contra hz0
  have hz1 : Q z = 1 := by
    have h := hsq
    rw [pow_two] at h
    exact (mul_eq_right₀ hz0).mp h
  have hzne : z ≠ 0 := fun h => by rw [h, QuadraticMap.map_zero] at hz1; exact zero_ne_one hz1
  have hBzz : Q.polarBilin z z = 0 := by
    rw [polarBilin_apply_apply]
    exact polar_self_eq_zero Q z
  have hNz := mulVec_sqrt_vector hQ hN hiso hz
  set Z := rankOneMat (Q.polarBilin.flip z) z with hZ
  have hZv : ∀ v, Z *ᵥ v = Q.polarBilin v z • z := fun v => by
    rw [hZ, rankOneMat_mulVec, LinearMap.flip_apply]
  have hZZ : Z * Z = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hZv (Z *ᵥ v), hZv v, map_smul, LinearMap.smul_apply, hBzz, smul_zero,
      zero_smul, zero_mulVec]
  have hNZ : N * Z = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hZv v, mulVec_smul, hNz, smul_zero, zero_mulVec]
  have hZN : Z * N = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hZv (N *ᵥ v), polar_mulVec_sqrt_vector hN hz, zero_smul, zero_mulVec]
  set r := sqZeroGL Z hZZ with hr
  have hriso : ∀ v, Q ((r : Matrix ι ι K) *ᵥ v) = Q v := fun v => by
    rw [hr, coe_sqZeroGL, add_mulVec, one_mulVec, hZv, quad_add, QuadraticMap.map_smul, hz1,
      map_smul, smul_eq_mul, smul_eq_mul, mul_one, polarBilin_comm Q v z, add_assoc,
      ← two_mul, CharTwo.two_eq_zero, zero_mul, add_zero]
  have hNZsq : (N + Z) * (N + Z) = 0 := by
    rw [add_mul, mul_add, mul_add, hN, hNZ, hZN, hZZ, add_zero, add_zero]
  have hMr : ((M * r : GL ι K) : Matrix ι ι K) = 1 + (N + Z) := by
    rw [Units.val_mul, hMN, hr, coe_sqZeroGL, add_mul, one_mul, mul_add, mul_one, hNZ, add_zero]
    abel
  have hMriso : ∀ v, Q (((M * r : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v := fun v => by
    rw [Units.val_mul, ← mulVec_mulVec, hM, hriso]
  have hsing : ∀ v, Q ((N + Z) *ᵥ v) = 0 := fun v => by
    rw [add_mulVec, hZv, quad_add, ← hz, QuadraticMap.map_smul, hz1, map_smul, smul_eq_mul,
      smul_eq_mul, mul_one, polar_mulVec_sqrt_vector hN hz, mul_zero, add_zero, ← pow_two,
      CharTwo.add_self_eq_zero]
  have hcomm : commSpace (glToLin (M * r)) ≤ LinearMap.range (N + Z).mulVecLin := by
    rw [commSpace_glToLin, hMr, add_sub_cancel_left]
  have hNZ2 : (N + Z) + (N + Z) = 0 := by
    rw [← two_smul K (N + Z), CharTwo.two_eq_zero, zero_smul]
  have hinv : glToLin (M * r) * glToLin (M * r) = 1 := by
    rw [← map_mul]
    have h1 : (M * r) * (M * r) = 1 := Units.ext (by
      rw [Units.val_mul, hMr, Units.val_one, add_mul, one_mul, mul_add, mul_one, hNZsq, add_zero,
        add_assoc, hNZ2, add_zero])
    rw [h1, map_one]
  have heven := even_finrank_commSpace_of_forall_eq_zero hQ (glToLin_mem_orthogonalGroup hMriso)
    hinv fun x hx => by
      obtain ⟨v, rfl⟩ := hcomm hx
      exact hsing v
  have hdick := natCast_finrank_commSpace_mul hQ (glToLin_mem_orthogonalGroup hM)
    (glToLin_mem_orthogonalGroup hriso)
  rw [← map_mul, finrank_commSpace_glToLin, finrank_commSpace_glToLin,
    finrank_commSpace_glToLin] at hdick
  rw [finrank_commSpace_glToLin] at heven
  have hrk : commRank r = 1 := by
    rw [hr, commRank_sqZeroGL, Matrix.rank]
    have hle : LinearMap.range Z.mulVecLin ≤ Submodule.span K {z} := by
      rintro _ ⟨v, rfl⟩
      rw [Matrix.mulVecLin_apply, hZv]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
    have hne : LinearMap.range Z.mulVecLin ≠ ⊥ := by
      intro hbot
      obtain ⟨v, hv⟩ : ∃ v, Q.polarBilin v z ≠ 0 := by
        by_contra! h
        exact hzne (hQ.2 z h)
      have h1 : Z *ᵥ v ∈ LinearMap.range Z.mulVecLin := ⟨v, rfl⟩
      rw [hbot, Submodule.mem_bot, hZv] at h1
      exact hv ((smul_eq_zero.mp h1).resolve_right hzne)
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hzne] at h1
    have h2 : 0 < finrank K (LinearMap.range Z.mulVecLin) :=
      Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h)
    omega
  rw [hrk, ZMod.natCast_eq_zero_iff_even.mpr hev, zero_add, Nat.cast_one,
    ZMod.natCast_eq_zero_iff_even.mpr heven] at hdick
  exact zero_ne_one hdick

end Dickson

@[expose] noncomputable def betaT (B : LinearMap.BilinForm K (ι → K)) (N : Matrix ι ι K)
    (z : ι → K) (d : K) : Matrix ι ι K :=
  d • N + (d ^ 2 + d) • rankOneMat (B.flip z) z

section Beta

variable {Q : QuadraticForm K (ι → K)} [CharP K 2] {N : Matrix ι ι K}
  (hN : N * N = 0) (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) {z : ι → K}
  (hz : ∀ v, Q.polarBilin v z ^ 2 = Q (N *ᵥ v)) (hNz : N *ᵥ z = 0) (hQz : Q z = 0)
include hN hz hNz

omit [CharP K 2] hN hz hNz in
theorem betaT_mulVec (d : K) (v : ι → K) :
    betaT Q.polarBilin N z d *ᵥ v = d • (N *ᵥ v) + ((d ^ 2 + d) * Q.polarBilin v z) • z := by
  rw [betaT, add_mulVec, smul_mulVec, smul_mulVec, rankOneMat_mulVec,
    LinearMap.BilinForm.flip_apply, smul_smul]

theorem betaT_mul (d d' : K) : betaT Q.polarBilin N z d * betaT Q.polarBilin N z d' = 0 := by
  have hBzz : Q.polarBilin z z = 0 := by
    rw [polarBilin_apply_apply]
    exact polar_self_eq_zero Q z
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [← mulVec_mulVec, betaT_mulVec (Q := Q) d, betaT_mulVec (Q := Q) d', zero_mulVec]
  have h1 : N *ᵥ (d' • (N *ᵥ v) + ((d' ^ 2 + d') * Q.polarBilin v z) • z) = 0 := by
    rw [mulVec_add, mulVec_smul, mulVec_smul, mulVec_mulVec, hN, zero_mulVec, hNz, smul_zero,
      smul_zero, add_zero]
  have h2 : Q.polarBilin (d' • (N *ᵥ v) + ((d' ^ 2 + d') * Q.polarBilin v z) • z) z = 0 := by
    rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, polar_mulVec_sqrt_vector hN hz, hBzz, smul_zero, smul_zero,
      add_zero]
  rw [h1, h2, smul_zero, mul_zero, zero_smul, add_zero]

omit hN hz hNz in
theorem betaT_add (d d' : K) :
    betaT Q.polarBilin N z d + betaT Q.polarBilin N z d' = betaT Q.polarBilin N z (d + d') := by
  simp only [betaT, CharTwo.add_sq, add_smul]
  abel

omit hNz in
theorem betaT_isometry (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) (hQz : Q z = 0) (d : K)
    (v : ι → K) : Q ((1 + betaT Q.polarBilin N z d) *ᵥ v) = Q v := by
  rw [add_mulVec, one_mulVec, betaT_mulVec, ← add_assoc, quad_add, quad_add,
    QuadraticMap.map_smul, QuadraticMap.map_smul, hQz]
  have e1 : Q.polarBilin v (d • (N *ᵥ v)) = d * Q (N *ᵥ v) := by
    rw [map_smul, smul_eq_mul, polar_self_mulVec Q hiso]
  have e2 : Q.polarBilin (v + d • (N *ᵥ v)) (((d ^ 2 + d) * Q.polarBilin v z) • z) =
      (d ^ 2 + d) * Q.polarBilin v z * Q.polarBilin v z := by
    rw [map_smul, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      polar_mulVec_sqrt_vector hN hz, smul_zero, add_zero, smul_eq_mul]
  rw [e1, e2, smul_eq_mul, smul_eq_mul]
  linear_combination (d ^ 2 + d) * hz v + (d ^ 2 + d) * Q (N *ᵥ v) * CharTwo.two_eq_zero (R := K)

omit hN hz hNz in
theorem betaT_mul_self (hN : N * N = 0) (hz : ∀ v, Q.polarBilin v z ^ 2 = Q (N *ᵥ v))
    (hNz : N *ᵥ z = 0) (d : K) :
    betaT Q.polarBilin N z d * betaT Q.polarBilin N z d = 0 :=
  betaT_mul hN hz hNz d d

omit hN hNz in
theorem mulVec_sqrt_vector_of_commute (hQ : Q.polarBilin.Nondegenerate) {X : GL ι K}
    (hX : ∀ v, Q ((X : Matrix ι ι K) *ᵥ v) = Q v) (hXN : (X : Matrix ι ι K) * N = N * X) :
    (X : Matrix ι ι K) *ᵥ z = z := by
  have hfrob : Function.Injective fun x : K => x ^ 2 := by
    intro a b hab
    simp only at hab
    have h : (a + b) ^ 2 = 0 := by rw [CharTwo.add_sq, hab, CharTwo.add_self_eq_zero]
    have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    rw [← CharTwo.sub_eq_add] at h'
    exact sub_eq_zero.mp h'
  have h1 : ∀ v, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) z = Q.polarBilin v z := fun v => by
    apply hfrob
    simp only
    rw [hz, hz, mulVec_mulVec, ← hXN, ← mulVec_mulVec, hX]
  have h2 : ∀ v, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) ((X : Matrix ι ι K) *ᵥ z) =
      Q.polarBilin v z := fun v => polarBilin_mulVec_of_isometry Q hX v z
  have hsurj : ∀ w, ∃ v, (X : Matrix ι ι K) *ᵥ v = w := fun w =>
    ⟨((X⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w, by rw [mulVec_mulVec, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_mulVec]⟩
  have h3 : ∀ w, Q.polarBilin w ((X : Matrix ι ι K) *ᵥ z - z) = 0 := fun w => by
    obtain ⟨v, rfl⟩ := hsurj w
    rw [map_sub, h2, h1, sub_self]
  have h4 := hQ.2 _ h3
  exact sub_eq_zero.mp h4

omit hN hNz in
theorem commute_betaT (hQ : Q.polarBilin.Nondegenerate) {X : GL ι K}
    (hX : ∀ v, Q ((X : Matrix ι ι K) *ᵥ v) = Q v) (hXN : (X : Matrix ι ι K) * N = N * X)
    (d : K) : (X : Matrix ι ι K) * betaT Q.polarBilin N z d =
      betaT Q.polarBilin N z d * X := by
  have hXz := mulVec_sqrt_vector_of_commute hz hQ hX hXN
  have hinv : ∀ v, Q.polarBilin ((X : Matrix ι ι K) *ᵥ v) z = Q.polarBilin v z := fun v => by
    conv_lhs => rw [← hXz]
    exact polarBilin_mulVec_of_isometry Q hX v z
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, betaT_mulVec, betaT_mulVec, mulVec_add, mulVec_smul,
    mulVec_smul, hXz, hinv, mulVec_mulVec, hXN, ← mulVec_mulVec]

omit hNz in
include hiso in
theorem betaT_mulVec_eq_zero_iff {z' : ι → K} (hz' : N *ᵥ z' = z) (hQz : Q z = 0) {d : K}
    (hd : d ≠ 0) (v : ι → K) : betaT Q.polarBilin N z d *ᵥ v = 0 ↔ N *ᵥ v = 0 := by
  have hz'z : Q.polarBilin z' z = 0 := by
    have h := hz z'
    rw [hz', hQz] at h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  rw [betaT_mulVec]
  constructor
  · intro h
    have h1 := congrArg (Q.polarBilin z') h
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hz'z, mul_zero, add_zero,
      map_zero, ← polar_mulVec_adj Q hN hiso, hz', mul_eq_zero] at h1
    have hv : Q.polarBilin v z = 0 := by
      rw [polarBilin_comm]
      exact h1.resolve_left hd
    rw [hv, mul_zero, zero_smul, add_zero] at h
    exact (smul_eq_zero.mp h).resolve_left hd
  · intro h
    have hv : Q.polarBilin v z = 0 := by
      have h1 := hz v
      rw [h, QuadraticMap.map_zero] at h1
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    rw [h, hv, mul_zero, zero_smul, smul_zero, add_zero]

omit hNz in
include hiso in
theorem rank_betaT {z' : ι → K} (hz' : N *ᵥ z' = z) (hQz : Q z = 0) {d : K} (hd : d ≠ 0) :
    (betaT Q.polarBilin N z d).rank = N.rank := by
  have hker : LinearMap.ker (betaT Q.polarBilin N z d).mulVecLin = LinearMap.ker N.mulVecLin := by
    ext v
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact betaT_mulVec_eq_zero_iff hN hiso hz hz' hQz hd v
  have h1 := LinearMap.finrank_range_add_finrank_ker (betaT Q.polarBilin N z d).mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [Matrix.rank, Matrix.rank]
  rw [hker] at h1
  omega

end Beta

end CFSG.ComponentClassification.RankTwoClassical
