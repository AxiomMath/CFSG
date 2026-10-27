module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpPerf
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalModelFactsSp

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin
open CFSG.Quasithin (perfectCore)
open scoped Matrix commutatorElement

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Q : QuadraticForm K (ι → K)}

omit [DecidableEq ι] in
theorem exists_ne_zero_polar_perp (Q : QuadraticForm K (ι → K)) {m : ℕ} (f : Fin m → ι → K)
    (hm : m < Fintype.card ι) : ∃ v, v ≠ 0 ∧ ∀ i, Q.polarBilin v (f i) = 0 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := LinearMap.pi fun i => Q.polarBilin.flip (f i))
      (by rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card]; exact hm))
  refine ⟨v, hv0, fun i => ?_⟩
  have h := congrFun (LinearMap.mem_ker.mp hv) i
  simpa using h

variable [CharP K 2]

omit [DecidableEq ι] in
theorem exists_singular_pair_perp [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hι : 7 ≤ Fintype.card ι) {u u'' : Fin 2 → ι → K} (hF : SpFrame Q u u'') :
    ∃ w w' : ι → K, Q w = 0 ∧ Q w' = 0 ∧ Q.polarBilin w w' = 1 ∧
      (∀ k, Q.polarBilin w (u k) = 0 ∧ Q.polarBilin w (u'' k) = 0) ∧
      ∀ k, Q.polarBilin w' (u k) = 0 ∧ Q.polarBilin w' (u'' k) = 0 := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_polar_perp Q ![u 0, u 1, u'' 0, u'' 1] (by omega)
  have hxu : ∀ k, Q.polarBilin x (u k) = 0 ∧ Q.polarBilin x (u'' k) = 0 := fun k => by
    fin_cases k
    · exact ⟨by simpa using hx 0, by simpa using hx 2⟩
    · exact ⟨by simpa using hx 1, by simpa using hx 3⟩
  obtain ⟨w, hw0, hQw, hwu⟩ : ∃ w, w ≠ 0 ∧ Q w = 0 ∧
      ∀ k, Q.polarBilin w (u k) = 0 ∧ Q.polarBilin w (u'' k) = 0 := by
    by_cases hQx : Q x = 0
    · exact ⟨x, hx0, hQx, hxu⟩
    obtain ⟨z, hz⟩ : ∃ z, Q.polarBilin x z ≠ 0 := by
      by_contra! h
      exact hx0 (hQ.1 x h)
    obtain ⟨y, hy0, hy⟩ := exists_ne_zero_polar_perp Q ![u 0, u 1, u'' 0, u'' 1, x, z]
      (by omega)
    have hyx : Q.polarBilin y x = 0 := by simpa using hy 4
    have hyz : Q.polarBilin y z = 0 := by simpa using hy 5
    obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q y / Q x)
    refine ⟨t • x + y, fun h => hy0 ?_, ?_, fun k => ?_⟩
    · have h1 := congrArg (fun v => Q.polarBilin v z) h
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hyz,
        add_zero, map_zero, LinearMap.zero_apply] at h1
      rw [(mul_eq_zero.mp h1).resolve_right hz, zero_smul, zero_add] at h
      exact h
    · rw [quad_add, QuadraticMap.map_smul, map_smul, LinearMap.smul_apply, hBs x y, hyx,
        smul_zero, add_zero, smul_eq_mul, ← ht, div_mul_cancel₀ _ hQx, CharTwo.add_self_eq_zero]
    · have h1 : Q.polarBilin y (u k) = 0 ∧ Q.polarBilin y (u'' k) = 0 := by
        fin_cases k
        · exact ⟨by simpa using hy 0, by simpa using hy 2⟩
        · exact ⟨by simpa using hy 1, by simpa using hy 3⟩
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        (hxu k).1, (hxu k).2, h1.1, h1.2, mul_zero, add_zero, and_self]
  obtain ⟨v, hv⟩ : ∃ v, Q.polarBilin w v = 1 := by
    obtain ⟨v, hv⟩ : ∃ v, Q.polarBilin w v ≠ 0 := by
      by_contra! h
      exact hw0 (hQ.1 w h)
    exact ⟨(Q.polarBilin w v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]⟩
  obtain ⟨p, hp⟩ : ∃ p, p = v - ∑ k, (Q.polarBilin v (u'' k) • u k +
      Q.polarBilin v (u k) • u'' k) := ⟨_, rfl⟩
  have hpu : ∀ k, Q.polarBilin p (u k) = 0 ∧ Q.polarBilin p (u'' k) = 0 := fun k => by
    rw [hp]
    simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, hF.uu, hF.vv, hF.uv, hF.vu, Fin.sum_univ_two]
    fin_cases k <;> simp
  have hwp : Q.polarBilin w p = 1 := by
    rw [hp]
    simp only [map_sub, map_sum, map_add, map_smul, smul_eq_mul, (hwu _).1, (hwu _).2, hv,
      mul_zero, add_zero, Finset.sum_const_zero, sub_zero]
  refine ⟨w, p + Q p • w, hQw, ?_, ?_, hwu, fun k => ?_⟩
  · rw [quad_add, QuadraticMap.map_smul, hQw, smul_zero, add_zero, map_smul, smul_eq_mul, hBs p w,
      hwp, mul_one, CharTwo.add_self_eq_zero]
  · rw [map_add, map_smul, smul_eq_mul, TypeCData.pol_self, mul_zero, add_zero, hwp]
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      (hpu k).1, (hpu k).2, (hwu k).1, (hwu k).2, mul_zero, add_zero, and_self]

section Levi

variable {u u'' : Fin 2 → ι → K}

omit [CharP K 2] in
theorem SpFrame.frD_mulVec_u (hF : SpFrame Q u u'') (a b : Matrix (Fin 2) (Fin 2) K)
    (m : Fin 2) : frD Q u u'' a b *ᵥ u m = u m + ∑ k, a k m • u k := by
  have h1 : frRow Q u'' *ᵥ u m = Pi.single m 1 := by
    rw [frRow_mulVec]
    ext i
    rw [hF.uv, Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  have h2 : frRow Q u *ᵥ u m = 0 := by
    rw [frRow_mulVec]
    ext i
    exact hF.uu m i
  rw [frD, add_mulVec, add_mulVec, one_mulVec, frP, frQ, ← mulVec_mulVec, ← mulVec_mulVec,
    ← mulVec_mulVec, ← mulVec_mulVec, h1, h2, mulVec_zero, mulVec_zero, add_zero, frCol_mulVec,
    mulVec_single_one]
  rfl

omit [CharP K 2] in
theorem frD_mulVec_of_perp (a b : Matrix (Fin 2) (Fin 2) K) {w : ι → K}
    (hw : ∀ k, Q.polarBilin w (u k) = 0 ∧ Q.polarBilin w (u'' k) = 0) :
    frD Q u u'' a b *ᵥ w = w := by
  have h1 : frRow Q u'' *ᵥ w = 0 := by
    rw [frRow_mulVec]
    ext i
    exact (hw i).2
  have h2 : frRow Q u *ᵥ w = 0 := by
    rw [frRow_mulVec]
    ext i
    exact (hw i).1
  rw [frD, add_mulVec, add_mulVec, one_mulVec, frP, frQ, ← mulVec_mulVec, ← mulVec_mulVec,
    ← mulVec_mulVec, ← mulVec_mulVec, h1, h2, mulVec_zero, mulVec_zero, mulVec_zero, mulVec_zero,
    add_zero, add_zero]

omit [CharP K 2] in
theorem SpFrame.quad_frD_mulVec (hF : SpFrame Q u u'') (hu : ∀ i, Q (u i) = 0)
    (hu'' : ∀ i, Q (u'' i) = 0) {a b : Matrix (Fin 2) (Fin 2) K} (hab : (1 + a)ᵀ * (1 + b) = 1)
    (v : ι → K) : Q (frD Q u u'' a b *ᵥ v) = Q v := by
  have hab' : aᵀ * b + aᵀ + b = 0 := by
    rw [transpose_add, transpose_one, add_mul, one_mul, mul_add, mul_one] at hab
    calc aᵀ * b + aᵀ + b = 1 + b + (aᵀ + aᵀ * b) - 1 := by abel
      _ = 0 := by rw [hab, sub_self]
  obtain ⟨c, hc⟩ : ∃ c, c = frRow Q u'' *ᵥ v := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = frRow Q u *ᵥ v := ⟨_, rfl⟩
  have hP : frP Q u u'' a *ᵥ v = frCol u *ᵥ (a *ᵥ c) := by
    rw [frP, ← mulVec_mulVec, ← mulVec_mulVec, hc]
  have hQ' : frQ Q u u'' b *ᵥ v = frCol u'' *ᵥ (b *ᵥ d) := by
    rw [frQ, ← mulVec_mulVec, ← mulVec_mulVec, hd]
  have hQu : ∀ e, Q (frCol u *ᵥ e) = 0 := fun e => by
    rw [frCol_mulVec]
    exact apply_sum_smul_eq_zero Q u hu hF.uu e
  have hQu'' : ∀ e, Q (frCol u'' *ᵥ e) = 0 := fun e => by
    rw [frCol_mulVec]
    exact apply_sum_smul_eq_zero Q u'' hu'' hF.vv e
  have hB1 : Q.polarBilin (frCol u *ᵥ (a *ᵥ c)) (frCol u'' *ᵥ (b *ᵥ d)) =
      (a *ᵥ c) ⬝ᵥ (b *ᵥ d) := by
    rw [polarBilin_frCol_mulVec_left, mulVec_mulVec, hF.frRow_mul_frCol_dual', one_mulVec]
  have hB2 : Q.polarBilin v (frCol u *ᵥ (a *ᵥ c)) = (a *ᵥ c) ⬝ᵥ d := by
    rw [polarBilin_frCol_mulVec_right, hd]
  have hB3 : Q.polarBilin v (frCol u'' *ᵥ (b *ᵥ d)) = (b *ᵥ d) ⬝ᵥ c := by
    rw [polarBilin_frCol_mulVec_right, hc]
  have key : (a *ᵥ c) ⬝ᵥ (b *ᵥ d) + (a *ᵥ c) ⬝ᵥ d + (b *ᵥ d) ⬝ᵥ c = 0 := by
    have e1 : c ⬝ᵥ ((aᵀ * b) *ᵥ d) = (a *ᵥ c) ⬝ᵥ (b *ᵥ d) := by
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    have e2 : c ⬝ᵥ (aᵀ *ᵥ d) = (a *ᵥ c) ⬝ᵥ d := by rw [dotProduct_mulVec, vecMul_transpose]
    have e : (a *ᵥ c) ⬝ᵥ (b *ᵥ d) + (a *ᵥ c) ⬝ᵥ d + (b *ᵥ d) ⬝ᵥ c =
        c ⬝ᵥ ((aᵀ * b + aᵀ + b) *ᵥ d) := by
      rw [add_mulVec, add_mulVec, dotProduct_add, dotProduct_add, e1, e2, dotProduct_comm c]
    rw [e, hab', zero_mulVec, dotProduct_zero]
  rw [frD, add_mulVec, add_mulVec, one_mulVec, hP, hQ', quad_add, quad_add, hQu, hQu'', map_add,
    LinearMap.add_apply, hB1, hB2, hB3]
  linear_combination key

omit [CharP K 2] in
theorem SpFrame.quad_frLevi_mulVec (hF : SpFrame Q u u'') (hu : ∀ i, Q (u i) = 0)
    (hu'' : ∀ i, Q (u'' i) = 0) (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : ι → K) :
    Q ((hF.frLevi g : Matrix ι ι K) *ᵥ v) = Q v := by
  rw [SpFrame.coe_frLevi, frLeviMat]
  refine hF.quad_frD_mulVec hu hu'' ?_ v
  rw [add_sub_cancel, add_sub_cancel, ← transpose_mul]
  simp only [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, transpose_one]

end Levi

section Siegel

@[expose] noncomputable def siegelGL (Q : QuadraticForm K (ι → K)) (a w : ι → K)
    (h : Q.polarBilin a w = 0) : GL ι K :=
  sqZeroGL (cTwoX Q a w) (cTwoX_mul_self h)

theorem coe_siegelGL (a w : ι → K) (h : Q.polarBilin a w = 0) :
    (siegelGL Q a w h : Matrix ι ι K) = 1 + cTwoX Q a w :=
  rfl

theorem coe_siegelGL_inv (a w : ι → K) (h : Q.polarBilin a w = 0) :
    ((siegelGL Q a w h)⁻¹ : GL ι K) = (1 - cTwoX Q a w : Matrix ι ι K) :=
  rfl

theorem quad_siegelGL_mulVec {a w : ι → K} (h : Q.polarBilin a w = 0) (hQa : Q a = 0)
    (hQw : Q w = 0) (v : ι → K) : Q ((siegelGL Q a w h : Matrix ι ι K) *ᵥ v) = Q v := by
  have h1 := cTwoX_isometry hQa hQw h 1 v
  rwa [one_smul] at h1

theorem conj_siegelGL {D : GL ι K} (hD : ∀ v, Q ((D : Matrix ι ι K) *ᵥ v) = Q v) {a w : ι → K}
    (h : Q.polarBilin a w = 0) :
    ((D * siegelGL Q a w h * D⁻¹ : GL ι K) : Matrix ι ι K) =
      1 + cTwoX Q ((D : Matrix ι ι K) *ᵥ a) ((D : Matrix ι ι K) *ᵥ w) := by
  have hDi : ∀ v, Q (((D⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v := fun v => by
    rw [← hD, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have h1 := conj_cTwoX hDi a w
  rw [inv_inv] at h1
  rw [Units.val_mul, Units.val_mul, coe_siegelGL, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
    Units.mul_inv, h1]

theorem commutatorElement_isometry_siegelGL {D : GL ι K}
    (hD : ∀ v, Q ((D : Matrix ι ι K) *ᵥ v) = Q v) {a b w : ι → K} (haw : Q.polarBilin a w = 0)
    (hbw : Q.polarBilin b w = 0) (hab : Q.polarBilin a b = 0)
    (hDa : (D : Matrix ι ι K) *ᵥ a = b + a) (hDw : (D : Matrix ι ι K) *ᵥ w = w) :
    ⁅D, siegelGL Q a w haw⁆ = siegelGL Q b w hbw := by
  apply Units.ext
  have hbaw : Q.polarBilin (b + a) w = 0 := by rw [map_add, LinearMap.add_apply, hbw, haw, add_zero]
  have hm : cTwoX Q (b + a) w * cTwoX Q a w = 0 := by
    rw [cTwoX_mul hbaw haw, map_add, hab, TypeCData.pol_self, add_zero, zero_smul]
  rw [commutatorElement_def, Units.val_mul, conj_siegelGL hD haw, hDa, hDw, coe_siegelGL_inv,
    Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hm, sub_zero, ← cTwoX_add,
    coe_siegelGL]
  abel

theorem commutatorElement_siegelGL {a₁ a₂ w w' : ι → K} (h₁ : Q.polarBilin a₁ w = 0)
    (h₂ : Q.polarBilin a₂ w' = 0) (h₁' : Q.polarBilin a₁ w' = 0) (h₂' : Q.polarBilin a₂ w = 0)
    (h₁₂ : Q.polarBilin a₁ a₂ = 0) :
    ((⁅siegelGL Q a₁ w h₁, siegelGL Q a₂ w' h₂⁆ : GL ι K) : Matrix ι ι K) =
      1 + Q.polarBilin w w' • cTwoX Q a₂ a₁ := by
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hXv : ∀ v, cTwoX Q a₁ w *ᵥ v = Q.polarBilin v a₁ • w + Q.polarBilin v w • a₁ :=
    fun v => cTwoX_mulVec a₁ w v
  have hYv : ∀ v, cTwoX Q a₂ w' *ᵥ v = Q.polarBilin v a₂ • w' + Q.polarBilin v w' • a₂ :=
    fun v => cTwoX_mulVec a₂ w' v
  have e1 : Q.polarBilin w' a₁ = 0 := by rw [hBs]; exact h₁'
  have e2 : Q.polarBilin a₂ a₁ = 0 := by rw [hBs]; exact h₁₂
  have e3 : Q.polarBilin w a₂ = 0 := by rw [hBs]; exact h₂'
  have hXY : cTwoX Q a₁ w * cTwoX Q a₂ w' = Q.polarBilin w w' • polMat Q a₂ a₁ :=
    Matrix.ext_iff_mulVec.mpr fun v => by
      rw [← mulVec_mulVec, smul_mulVec, polMat_mulVec]
      simp only [hYv, hXv, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, e1, e2, h₂', hBs w' w, zero_mul, add_zero, zero_smul, zero_add, smul_smul,
        mul_comm]
  have hYX : cTwoX Q a₂ w' * cTwoX Q a₁ w = Q.polarBilin w w' • polMat Q a₁ a₂ :=
    Matrix.ext_iff_mulVec.mpr fun v => by
      rw [← mulVec_mulVec, smul_mulVec, polMat_mulVec]
      simp only [hYv, hXv, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, e3, h₁₂, h₁', zero_mul, add_zero, zero_smul, zero_add, smul_smul, mul_comm]
  have hXYX : cTwoX Q a₁ w * cTwoX Q a₂ w' * cTwoX Q a₁ w = 0 :=
    Matrix.ext_iff_mulVec.mpr fun v => by
      rw [hXY, ← mulVec_mulVec, smul_mulVec, polMat_mulVec, zero_mulVec]
      simp only [hXv, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        e3, h₁₂, mul_zero, add_zero, zero_smul, smul_zero]
  have hYXY : cTwoX Q a₂ w' * cTwoX Q a₁ w * cTwoX Q a₂ w' = 0 :=
    Matrix.ext_iff_mulVec.mpr fun v => by
      rw [hYX, ← mulVec_mulVec, smul_mulVec, polMat_mulVec, zero_mulVec]
      simp only [hYv, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        e1, e2, mul_zero, add_zero, zero_smul, smul_zero]
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, coe_siegelGL,
    coe_siegelGL, coe_siegelGL_inv, coe_siegelGL_inv,
    commutator_expand_of_mul_self (cTwoX_mul_self h₁) (cTwoX_mul_self h₂), hXYX, hYXY,
    Matrix.zero_mul, hXY, hYX, cTwoX, sub_zero, add_zero, add_zero, sub_eq_add_neg, ← neg_smul,
    CharTwo.neg_eq, ← smul_add]

theorem siegelGL_commute {N : Matrix ι ι K} {a w : ι → K} (h : Q.polarBilin a w = 0)
    (hNa : N *ᵥ a = 0) (hNw : N *ᵥ w = 0)
    (hNv : ∀ v, Q.polarBilin (N *ᵥ v) a = 0 ∧ Q.polarBilin (N *ᵥ v) w = 0) :
    (siegelGL Q a w h : Matrix ι ι K) * (1 + N) = (1 + N) * siegelGL Q a w h := by
  have h1 : cTwoX Q a w * N = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, cTwoX_mulVec, (hNv v).1, (hNv v).2, zero_smul, zero_smul, add_zero,
      zero_mulVec]
  have h2 : N * cTwoX Q a w = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, cTwoX_mulVec, mulVec_add, mulVec_smul, mulVec_smul, hNa, hNw, smul_zero,
      smul_zero, add_zero, zero_mulVec]
  simp only [coe_siegelGL, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h1, h2,
    add_zero]
  abel

end Siegel

theorem mem_perfectCore_of_singular_two [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    (hK : ∃ s : Finset K, s.card = 4) (hι : 7 ≤ Fintype.card ι) {M : GL ι K}
    (hMQ : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v) (hM2 : orderOf M = 2) (hr : commRank M = 2)
    (hsing : ∀ v, Q (((M : Matrix ι ι K) - 1) *ᵥ v) = 0) :
    M ∈ perfectCore (StatedOmega ⇑Q ⊓ centralizer ({M} : Set (GL ι K))) := by
  classical
  have hBs : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  have hB0 : ∀ a, Q.polarBilin a a = 0 := fun a => TypeCData.pol_self a
  have hN := sub_one_mul_self_eq_zero hM2
  have hadj := polarBilin_sub_one_adj (polarBilin_mulVec_of_isometry Q hMQ) hM2
  obtain ⟨N, hNdef⟩ : ∃ N, N = (M : Matrix ι ι K) - 1 := ⟨_, rfl⟩
  rw [← hNdef] at hN hadj hsing
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have hr' : N.rank = 2 := by rw [hNdef]; exact hr
  have halt : ∀ v, Q.polarBilin v (N *ᵥ v) = 0 := fun v => by
    have h1 := hMQ v
    rw [hMN, add_mulVec, one_mulVec, quad_add, hsing, add_zero] at h1
    exact add_eq_left.mp h1
  have hNN : ∀ a b, Q.polarBilin (N *ᵥ a) (N *ᵥ b) = 0 := fun a b => by
    rw [hadj, mulVec_mulVec, hN, zero_mulVec, map_zero]
  have hNNv : ∀ a, N *ᵥ (N *ᵥ a) = 0 := fun a => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hN0 : N ≠ 0 := fun h => by
    rw [h, Matrix.rank_zero] at hr'
    exact absurd hr' (by norm_num)
  obtain ⟨y, hy⟩ : ∃ y, N *ᵥ y ≠ 0 := by
    by_contra! h
    exact hN0 (Matrix.ext_iff_mulVec.mpr fun v => by rw [h v, zero_mulVec])
  obtain ⟨x, hxy⟩ : ∃ x, Q.polarBilin x (N *ᵥ y) = 1 := by
    obtain ⟨x, hx⟩ : ∃ x, Q.polarBilin x (N *ᵥ y) ≠ 0 := by
      by_contra! h
      exact hy (hQ.2 _ h)
    exact ⟨(Q.polarBilin x (N *ᵥ y))⁻¹ • x, by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hx]⟩
  have hyx : Q.polarBilin y (N *ᵥ x) = 1 := by rw [← hadj, hBs, hxy]
  have hxx : Q.polarBilin x (N *ᵥ x) = 0 := halt x
  have hyy : Q.polarBilin y (N *ᵥ y) = 0 := halt y
  have hNE : N = cTwoX Q (N *ᵥ y) (N *ᵥ x) := by
    obtain ⟨-, -, -, -, -, hrk⟩ := sub_cTwoX_of_alt hN hadj halt hxy rfl
    rw [hr'] at hrk
    exact sub_eq_zero.mp (eq_zero_of_rank_eq_zero hrk)
  obtain ⟨a₁, ha₁⟩ : ∃ a₁, a₁ = N *ᵥ x := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a₂, a₂ = N *ᵥ y := ⟨_, rfl⟩
  obtain ⟨x', hx'⟩ : ∃ x', x' = x + Q.polarBilin y x • a₁ := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b₁, b₁ = y + Q y • a₁ := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ b₂, b₂ = x' + Q x' • a₂ := ⟨_, rfl⟩
  have h12 : Q.polarBilin a₁ a₂ = 0 := by rw [ha₁, ha₂, hNN]
  have h21 : Q.polarBilin a₂ a₁ = 0 := by rw [ha₁, ha₂, hNN]
  have hQa₁ : Q a₁ = 0 := by rw [ha₁]; exact hsing x
  have hQa₂ : Q a₂ = 0 := by rw [ha₂]; exact hsing y
  have ha₁y : Q.polarBilin a₁ y = 1 := by rw [ha₁, hadj, hxy]
  have ha₂y : Q.polarBilin a₂ y = 0 := by rw [ha₂, hadj, hyy]
  have hya₁ : Q.polarBilin y a₁ = 1 := by rw [hBs, ha₁y]
  have hya₂ : Q.polarBilin y a₂ = 0 := by rw [hBs, ha₂y]
  have ha₁x' : Q.polarBilin a₁ x' = 0 := by
    rw [hx', map_add, map_smul, smul_eq_mul, hB0, mul_zero, add_zero, ha₁, hadj, hxx]
  have ha₂x' : Q.polarBilin a₂ x' = 1 := by
    rw [hx', map_add, map_smul, smul_eq_mul, h21, mul_zero, add_zero, ha₂, hadj, hyx]
  have hyx' : Q.polarBilin y x' = 0 := by
    rw [hx', map_add, map_smul, smul_eq_mul, hya₁, mul_one, CharTwo.add_self_eq_zero]
  have ha₁b₁ : Q.polarBilin a₁ b₁ = 1 := by
    rw [hb₁, map_add, map_smul, smul_eq_mul, hB0, mul_zero, add_zero, ha₁y]
  have ha₂b₁ : Q.polarBilin a₂ b₁ = 0 := by
    rw [hb₁, map_add, map_smul, smul_eq_mul, h21, mul_zero, add_zero, ha₂y]
  have ha₁b₂ : Q.polarBilin a₁ b₂ = 0 := by
    rw [hb₂, map_add, map_smul, smul_eq_mul, h12, mul_zero, add_zero, ha₁x']
  have ha₂b₂ : Q.polarBilin a₂ b₂ = 1 := by
    rw [hb₂, map_add, map_smul, smul_eq_mul, hB0, mul_zero, add_zero, ha₂x']
  have hb₁b₂ : Q.polarBilin b₁ b₂ = 0 := by
    rw [hb₂, hb₁]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hyx',
      hya₂, ha₁x', h12, mul_zero, add_zero]
  have hQb₁ : Q b₁ = 0 := by
    rw [hb₁, quad_add, QuadraticMap.map_smul, hQa₁, smul_zero, add_zero, map_smul, smul_eq_mul,
      hya₁, mul_one, CharTwo.add_self_eq_zero]
  have hQb₂ : Q b₂ = 0 := by
    rw [hb₂, quad_add, QuadraticMap.map_smul, hQa₂, smul_zero, add_zero, map_smul, smul_eq_mul,
      hBs x' a₂, ha₂x', mul_one, CharTwo.add_self_eq_zero]
  obtain ⟨u, hu⟩ : ∃ u : Fin 2 → ι → K, u = ![a₁, a₂] := ⟨_, rfl⟩
  obtain ⟨u'', hu''⟩ : ∃ u'' : Fin 2 → ι → K, u'' = ![b₁, b₂] := ⟨_, rfl⟩
  have hF : SpFrame Q u u'' := by
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [hu]
      fin_cases i <;> fin_cases j <;> simp [hB0, h12, h21]
    · rw [hu'']
      fin_cases i <;> fin_cases j <;> simp [hB0, hb₁b₂, hBs b₂ b₁]
    · rw [hu, hu'']
      fin_cases i <;> fin_cases j <;> simp [ha₁b₁, ha₁b₂, ha₂b₁, ha₂b₂]
  have hQu : ∀ i, Q (u i) = 0 := fun i => by
    rw [hu]
    fin_cases i
    exacts [hQa₁, hQa₂]
  have hQu'' : ∀ i, Q (u'' i) = 0 := fun i => by
    rw [hu'']
    fin_cases i
    exacts [hQb₁, hQb₂]
  have hNa : N = cTwoX Q a₂ a₁ := by rw [ha₁, ha₂]; exact hNE
  have hNR : frR Q u (frH K) = N :=
    Matrix.ext_iff_mulVec.mpr fun v => by
      rw [hNa, frR, ← mulVec_mulVec, ← mulVec_mulVec, frRow_mulVec, frCol_mulVec, cTwoX_mulVec, hu]
      simp [frH, mulVec, dotProduct, Fin.sum_univ_two]
  have hNv : ∀ v, N *ᵥ v = Q.polarBilin v a₂ • a₁ + Q.polarBilin v a₁ • a₂ := fun v => by
    rw [hNa, cTwoX_mulVec]
  have hLQ : ∀ g v, Q ((hF.frLevi g : Matrix ι ι K) *ᵥ v) = Q v :=
    hF.quad_frLevi_mulVec hQu hQu''
  have hLM : ∀ g, hF.frLevi g * M = M * hF.frLevi g := fun g => by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hMN, ← hNR, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, hF.frLevi_mul_frR_frH]
  have hperf : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_two_perfect hK).commutator_eq_top
  have hLiso : hF.frLevi.range ≤ closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} := by
    rintro _ ⟨g, rfl⟩
    exact subset_closure fun v => hLQ g v
  have hLperf : ⁅hF.frLevi.range, hF.frLevi.range⁆ = hF.frLevi.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperf]
  have hLO : hF.frLevi.range ≤ StatedOmega ⇑Q := by
    rw [← hLperf, StatedOmega]
    exact commutator_mono hLiso hLiso
  have hLC : hF.frLevi.range ≤ StatedOmega ⇑Q ⊓ centralizer ({M} : Set (GL ι K)) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨hLO ⟨g, rfl⟩, mem_centralizer_singleton_iff.mpr (hLM g)⟩
  have hLcore : hF.frLevi.range ≤ perfectCore (StatedOmega ⇑Q ⊓ centralizer ({M} : Set (GL ι K))) :=
    CFSG.Quasithin.le_perfectCore_of_perfect hLC hLperf
  obtain ⟨w, w', hQw, hQw', hww', hwu, hw'u⟩ := exists_singular_pair_perp hQ hι hF
  have hwa : ∀ {a}, a = a₁ ∨ a = a₂ → Q.polarBilin a w = 0 ∧ Q.polarBilin a w' = 0 := by
    rintro a (rfl | rfl)
    · have h1 := (hwu 0).1
      have h2 := (hw'u 0).1
      rw [hu] at h1 h2
      exact ⟨by rw [hBs]; simpa using h1, by rw [hBs]; simpa using h2⟩
    · have h1 := (hwu 1).1
      have h2 := (hw'u 1).1
      rw [hu] at h1 h2
      exact ⟨by rw [hBs]; simpa using h1, by rw [hBs]; simpa using h2⟩
  have h₁w := (hwa (Or.inl rfl)).1
  have h₁w' := (hwa (Or.inl rfl)).2
  have h₂w := (hwa (Or.inr rfl)).1
  have h₂w' := (hwa (Or.inr rfl)).2
  have hiso : ∀ {a b : ι → K} (h : Q.polarBilin a b = 0), Q a = 0 → Q b = 0 →
      siegelGL Q a b h ∈ closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} :=
    fun h ha hb => subset_closure fun v => quad_siegelGL_mulVec h ha hb v
  have hNw : ∀ {b}, Q.polarBilin a₁ b = 0 → Q.polarBilin a₂ b = 0 → N *ᵥ b = 0 := fun h1 h2 => by
    rw [hNv, hBs, h2, hBs, h1, zero_smul, zero_smul, add_zero]
  have hNa₁ : N *ᵥ a₁ = 0 := by rw [ha₁, hNNv]
  have hNa₂ : N *ᵥ a₂ = 0 := by rw [ha₂, hNNv]
  have hcomm : ∀ {a b : ι → K} (h : Q.polarBilin a b = 0), (a = a₁ ∨ a = a₂) →
      Q.polarBilin a₁ b = 0 → Q.polarBilin a₂ b = 0 → siegelGL Q a b h ∈ centralizer {M} := by
    intro a b h ha h1 h2
    refine mem_centralizer_singleton_iff.mpr (Units.ext ?_)
    rw [Units.val_mul, Units.val_mul, hMN]
    refine siegelGL_commute h (by rcases ha with rfl | rfl; exacts [hNa₁, hNa₂]) (hNw h1 h2)
      fun v => ⟨?_, ?_⟩
    · rw [hNv]
      rcases ha with rfl | rfl <;> simp [hB0, h12, h21]
    · rw [hNv]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2,
        mul_zero, add_zero]
  let g : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩
  let g' : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩
  have hu0 : u 0 = a₁ := by rw [hu]; rfl
  have hu1 : u 1 = a₂ := by rw [hu]; rfl
  have hDg : (hF.frLevi g : Matrix ι ι K) *ᵥ a₂ = a₁ + a₂ := by
    have h1 := hF.frD_mulVec_u ((g : Matrix (Fin 2) (Fin 2) K) - 1)
      (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ - 1) 1
    rw [SpFrame.coe_frLevi, frLeviMat, ← hu1]
    simpa [g, Fin.sum_univ_two, hu0, hu1, add_comm] using h1
  have hDg' : (hF.frLevi g' : Matrix ι ι K) *ᵥ a₁ = a₂ + a₁ := by
    have h1 := hF.frD_mulVec_u ((g' : Matrix (Fin 2) (Fin 2) K) - 1)
      (((g'⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ - 1) 0
    rw [SpFrame.coe_frLevi, frLeviMat, ← hu0]
    simpa [g', Fin.sum_univ_two, hu0, hu1, add_comm] using h1
  have hDw : ∀ (h : Matrix.SpecialLinearGroup (Fin 2) K) {v : ι → K},
      (∀ k, Q.polarBilin v (u k) = 0 ∧ Q.polarBilin v (u'' k) = 0) →
      (hF.frLevi h : Matrix ι ι K) *ᵥ v = v := fun h v hv => by
    rw [SpFrame.coe_frLevi, frLeviMat]
    exact frD_mulVec_of_perp _ _ hv
  have hS₂w : ⁅hF.frLevi g', siegelGL Q a₁ w h₁w⁆ = siegelGL Q a₂ w h₂w :=
    commutatorElement_isometry_siegelGL (hLQ g') h₁w h₂w h12 hDg' (hDw g' hwu)
  have hS₂w' : ⁅hF.frLevi g', siegelGL Q a₁ w' h₁w'⁆ = siegelGL Q a₂ w' h₂w' :=
    commutatorElement_isometry_siegelGL (hLQ g') h₁w' h₂w' h12 hDg' (hDw g' hw'u)
  have hS₁w : ⁅hF.frLevi g, siegelGL Q a₂ w h₂w⁆ = siegelGL Q a₁ w h₁w :=
    commutatorElement_isometry_siegelGL (hLQ g) h₂w h₁w h21 hDg (hDw g hwu)
  have hΩ : ∀ {A B : GL ι K},
      A ∈ closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} →
      B ∈ closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} →
      ⁅A, B⁆ ∈ StatedOmega ⇑Q := fun hA hB => by
    rw [StatedOmega]
    exact commutator_mem_commutator hA hB
  have hS₂wC : siegelGL Q a₂ w h₂w ∈ StatedOmega ⇑Q ⊓ centralizer ({M} : Set (GL ι K)) :=
    ⟨hS₂w ▸ hΩ (hLiso ⟨g', rfl⟩) (hiso h₁w hQa₁ hQw), hcomm h₂w (Or.inr rfl) h₁w h₂w⟩
  have hS₂w'C : siegelGL Q a₂ w' h₂w' ∈ StatedOmega ⇑Q ⊓ centralizer ({M} : Set (GL ι K)) :=
    ⟨hS₂w' ▸ hΩ (hLiso ⟨g', rfl⟩) (hiso h₁w' hQa₁ hQw'), hcomm h₂w' (Or.inr rfl) h₁w' h₂w'⟩
  have hS₁wcore : siegelGL Q a₁ w h₁w ∈
      perfectCore (StatedOmega ⇑Q ⊓ centralizer ({M} : Set (GL ι K))) :=
    hS₁w ▸ commutatorElement_mem_perfectCore' hS₂wC (hLcore ⟨g, rfl⟩)
  have hMc : M = ⁅siegelGL Q a₁ w h₁w, siegelGL Q a₂ w' h₂w'⁆ := by
    apply Units.ext
    rw [commutatorElement_siegelGL h₁w h₂w' h₁w' h₂w h12, hww', one_smul, hMN, hNa]
  have h := commutatorElement_mem_perfectCore' hS₂w'C hS₁wcore
  rwa [← hMc] at h

theorem orthogonalSingularPerfect : OrthogonalSingularPerfect := by
  intro n K _ _ _ hn h4
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    have : Fintype K := Fintype.ofFinite K
    have h4' : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact h4
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4'
    exact ⟨t, ht⟩
  refine ⟨fun M hM hM2 hr hsing => ?_, fun b c hbc M hM hM2 hr hsing => ?_⟩
  · have h := mem_perfectCore_of_singular_two (Q := quadPlus n K)
      (nondegenerate_polarBilin_quadPlus n K) hK4 (by simp; omega)
      (fun v => by rw [coe_quadPlus]; exact statedOmega_isometry hM v) hM2 hr
      (fun v => by rw [coe_quadPlus]; exact hsing v)
    rwa [coe_quadPlus] at h
  · have h := mem_perfectCore_of_singular_two (Q := quadMinus n K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite n K hbc) hK4 (by simp; omega)
      (fun v => by rw [coe_quadMinus]; exact statedOmega_isometry hM v) hM2 hr
      (fun v => by rw [coe_quadMinus]; exact hsing v)
    rwa [coe_quadMinus] at h

end CFSG.ComponentClassification.RankTwoClassical
