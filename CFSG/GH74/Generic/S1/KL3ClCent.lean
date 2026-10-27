module

public import CFSG.GH74.Generic.S1.KL3ClRep
public import Mathlib.FieldTheory.Finite.Basic

public section

open Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

section LinAlg

variable {Ω : Type*} [Field Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem kl3clc_li (B : Matrix ι ι Ω) {n : ℕ} (lam : Fin n → Ω) (hlam : Function.Injective lam)
    (v : Fin n → ι → Ω) (hv : ∀ i, v i ≠ 0) (hBv : ∀ i, B *ᵥ v i = lam i • v i) :
    LinearIndependent Ω v := by
  refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' B) lam hlam v fun i => ?_
  refine ⟨?_, hv i⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact hBv i

omit [DecidableEq ι] in
theorem kl3clc_span (hι : Fintype.card ι = 4) (v : Fin 4 → ι → Ω) (hli : LinearIndependent Ω v) :
    Submodule.span Ω (Set.range v) = ⊤ := by
  refine hli.span_eq_top_of_card_eq_finrank' ?_
  rw [Module.finrank_fintype_fun_eq_card, hι, Fintype.card_fin]

theorem kl3clc_mat_eq_of_span {n : ℕ} (v : Fin n → ι → Ω)
    (hspan : Submodule.span Ω (Set.range v) = ⊤) (M N : Matrix ι ι Ω)
    (h : ∀ i, M *ᵥ v i = N *ᵥ v i) : M = N := by
  refine Matrix.toLin'.injective (LinearMap.ext_on_range hspan fun i => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact h i

omit [DecidableEq ι] in
theorem kl3clc_comm_eig (B : Matrix ι ι Ω) (lam : Fin 4 → Ω) (hlam : Function.Injective lam)
    (v : Fin 4 → ι → Ω) (hli : LinearIndependent Ω v)
    (hspan : Submodule.span Ω (Set.range v) = ⊤) (hBv : ∀ i, B *ᵥ v i = lam i • v i)
    (A : Matrix ι ι Ω) (hAB : A * B = B * A) (i : Fin 4) : ∃ a : Ω, A *ᵥ v i = a • v i := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1
    (hspan ▸ Submodule.mem_top : A *ᵥ v i ∈ Submodule.span Ω (Set.range v))
  have hB : B *ᵥ (A *ᵥ v i) = lam i • (A *ᵥ v i) := by
    rw [Matrix.mulVec_mulVec, ← hAB, ← Matrix.mulVec_mulVec, hBv, Matrix.mulVec_smul]
  have h1 : B *ᵥ (A *ᵥ v i) = ∑ j, (c j * lam j) • v j := by
    rw [← hc, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, hBv, smul_smul]
  have h2 : lam i • (A *ᵥ v i) = ∑ j, (c j * lam i) • v j := by
    rw [← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, mul_comm]
  have hsum : ∑ j, (c j * (lam j - lam i)) • v j = 0 := by
    simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
    rw [← h1, ← h2, hB, sub_self]
  have hcoef := Fintype.linearIndependent_iff.1 hli _ hsum
  refine ⟨c i, ?_⟩
  rw [← hc, Finset.sum_eq_single i]
  · intro j _ hji
    have hne : lam j - lam i ≠ 0 := sub_ne_zero.2 fun h => hji (hlam h)
    rw [(mul_eq_zero.1 (hcoef j)).resolve_right hne, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem kl3clc_conj_eig (B C : Matrix ι ι Ω) (hB : B ^ 13 = 1) (hCB : C * B = B ^ 3 * C) {ν : Ω}
    {w : ι → Ω} (hw : B *ᵥ w = ν • w) : B *ᵥ (C *ᵥ w) = ν ^ 9 • (C *ᵥ w) := by
  have hB27 : B ^ 27 = B := by
    calc B ^ 27 = (B ^ 13) ^ 2 * B := by rw [← pow_mul, ← pow_succ]
      _ = B := by rw [hB]; simp
  have h1 : B ^ 3 *ᵥ (C *ᵥ w) = ν • (C *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, ← hCB, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  have h2 : (B ^ 3) ^ 9 *ᵥ (C *ᵥ w) = ν ^ 9 • (C *ᵥ w) :=
    kl3cl_pow_mulVec_of_eig (B ^ 3) h1 9
  rwa [← pow_mul, show 3 * 9 = 27 by norm_num, hB27] at h2

theorem kl3clc_diag (hι : Fintype.card ι = 4) (B C A : Matrix ι ι Ω) (hB13 : B ^ 13 = 1)
    (hCB : C * B = B ^ 3 * C) (hCinj : ∀ v, C *ᵥ v = 0 → v = 0)
    (hAB : A * B = B * A) (hAC : A * C = C * A) {μ : Ω} (hμ1 : μ ≠ 1) (hμ13 : μ ^ 13 = 1)
    {w : ι → Ω} (hw : w ≠ 0) (hBw : B *ᵥ w = μ • w) {u : ι → Ω} (hu : u ≠ 0)
    (hBu : B *ᵥ u = u) :
    ∃ a α : Ω, A *ᵥ u = a • u ∧ A * (B - 1) = α • (B - 1) ∧
      (a ^ 2 = 1 → α ^ 2 = 1 → A * A = 1) := by
  have hFact : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hprim : IsPrimitiveRoot μ 13 := (orderOf_eq_prime hμ13 hμ1) ▸ IsPrimitiveRoot.orderOf μ
  let exps : Fin 4 → ℕ := ![0, 1, 9, 3]
  let lam : Fin 4 → Ω := fun i => μ ^ exps i
  have hlam : Function.Injective lam := by
    intro i j hij
    have hlt : ∀ k : Fin 4, exps k < 13 := by decide
    have hexps : ∀ i j : Fin 4, exps i = exps j → i = j := by decide
    exact hexps i j (hprim.pow_inj (hlt i) (hlt j) hij)
  have hw2 : C *ᵥ w ≠ 0 := fun h => hw (hCinj w h)
  have hw3 : C *ᵥ (C *ᵥ w) ≠ 0 := fun h => hw2 (hCinj _ h)
  have hBw2 : B *ᵥ (C *ᵥ w) = (μ ^ 9) • (C *ᵥ w) := kl3clc_conj_eig B C hB13 hCB hBw
  have hBw3 : B *ᵥ (C *ᵥ (C *ᵥ w)) = (μ ^ 3) • (C *ᵥ (C *ᵥ w)) := by
    have := kl3clc_conj_eig B C hB13 hCB hBw2
    rwa [← pow_mul, pow_eq_pow_mod _ hμ13] at this
  let v : Fin 4 → ι → Ω := ![u, w, C *ᵥ w, C *ᵥ (C *ᵥ w)]
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i
    fin_cases i
    · exact hu
    · exact hw
    · exact hw2
    · exact hw3
  have hBv : ∀ i, B *ᵥ v i = lam i • v i := by
    intro i
    fin_cases i
    · simpa [v, lam, exps] using hBu
    · simpa [v, lam, exps] using hBw
    · exact hBw2
    · exact hBw3
  have hli := kl3clc_li B lam hlam v hv0 hBv
  have hspan := kl3clc_span hι v hli
  choose a ha using fun i => kl3clc_comm_eig B lam hlam v hli hspan hBv A hAB i
  have ha1 : A *ᵥ w = a 1 • w := ha 1
  have ha2 : A *ᵥ (C *ᵥ w) = a 2 • (C *ᵥ w) := ha 2
  have ha3 : A *ᵥ (C *ᵥ (C *ᵥ w)) = a 3 • (C *ᵥ (C *ᵥ w)) := ha 3
  have ha21 : a 2 = a 1 := by
    have h : A *ᵥ (C *ᵥ w) = a 1 • (C *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, hAC, ← Matrix.mulVec_mulVec, ha1, Matrix.mulVec_smul]
    exact (smul_left_injective Ω hw2 (h.symm.trans ha2)).symm
  have ha32 : a 3 = a 2 := by
    have h : A *ᵥ (C *ᵥ (C *ᵥ w)) = a 2 • (C *ᵥ (C *ᵥ w)) := by
      rw [Matrix.mulVec_mulVec, hAC, ← Matrix.mulVec_mulVec, ha2, Matrix.mulVec_smul]
    exact (smul_left_injective Ω hw3 (h.symm.trans ha3)).symm
  have ha31 : a 3 = a 1 := ha32.trans ha21
  refine ⟨a 0, a 1, ha 0, ?_, ?_⟩
  · refine kl3clc_mat_eq_of_span v hspan _ _ fun i => ?_
    have hBm1 : (B - 1) *ᵥ v i = (lam i - 1) • v i := by
      rw [Matrix.sub_mulVec, hBv, Matrix.one_mulVec, sub_smul, one_smul]
    rw [← Matrix.mulVec_mulVec, hBm1, Matrix.mulVec_smul, ha i, smul_smul, Matrix.smul_mulVec,
      hBm1, smul_smul]
    congr 1
    fin_cases i
    · simp [lam, exps]
    · exact mul_comm _ _
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [ha21]
      exact mul_comm _ _
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [ha31]
      exact mul_comm _ _
  · intro h0 h1
    refine kl3clc_mat_eq_of_span v hspan _ _ fun i => ?_
    rw [← Matrix.mulVec_mulVec, ha i, Matrix.mulVec_smul, ha i, smul_smul, Matrix.one_mulVec]
    have : a i * a i = 1 := by
      fin_cases i
      · simpa [sq] using h0
      · simpa [sq] using h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [ha21]
        simpa [sq] using h1
      · simp only [Fin.reduceFinMk, Fin.isValue]
        rw [ha31]
        simpa [sq] using h1
    rw [this, one_smul]

end LinAlg

section FiniteField

theorem kl3clc_fixed {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {ι : Type} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι = 4) (B : Matrix ι ι K) (hB : B ^ 13 = 1) :
    ∃ u : ι → K, u ≠ 0 ∧ B *ᵥ u = u := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hFact : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let g : Function.End (ι → K) := fun x => B *ᵥ x
  have hiter : ∀ (n : ℕ) (x : ι → K), (g ^ n) x = B ^ n *ᵥ x := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [pow_zero, pow_zero, Matrix.one_mulVec]
      rfl
    | succ n ih =>
      intro x
      rw [pow_succ']
      show B *ᵥ ((g ^ n) x) = _
      rw [ih, Matrix.mulVec_mulVec, ← pow_succ']
  have hg : g ^ 13 ^ 1 = 1 := by
    funext x
    rw [pow_one, hiter, hB, Matrix.one_mulVec]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq hg
  by_contra hcon
  push Not at hcon
  have hcard1 : Fintype.card (Function.fixedPoints g) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, by simp [Function.IsFixedPt, g]⟩, fun y => ?_⟩
    obtain ⟨y, hy⟩ := y
    refine Subtype.ext ?_
    by_contra hne
    exact hcon y hne hy
  have hcard : Fintype.card (ι → K) = 81 := by
    rw [Fintype.card_fun, hcardK, hι]
    norm_num
  rw [hcard1, hcard] at hmod
  revert hmod
  decide

theorem kl3clc_map_mulVec {K Ω : Type*} [Field K] [Field Ω] (f : K →+* Ω) {ι : Type*} [Fintype ι]
    (M : Matrix ι ι K) (x : ι → K) :
    M.map f *ᵥ (fun i => f (x i)) = fun i => f ((M *ᵥ x) i) :=
  funext fun i => (RingHom.map_mulVec f M x i).symm

theorem kl3clc_rat_sq {K Ω : Type*} [Field K] [Fintype K] [Field Ω] (hK : Fintype.card K = 3)
    (f : K →+* Ω) {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K)
    (hAinj : ∀ v, A *ᵥ v = 0 → v = 0) {x : ι → K} (hx : x ≠ 0) {a : Ω}
    (h : A.map f *ᵥ (fun i => f (x i)) = a • fun i => f (x i)) : a ^ 2 = 1 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext hcon)
  have hcomp : ∀ i, f ((A *ᵥ x) i) = a * f (x i) := by
    intro i
    have h1 := congrFun (kl3clc_map_mulVec f A x) i
    rw [h] at h1
    simpa using h1.symm
  have hfx : f (x i₀) ≠ 0 := (map_ne_zero f).2 hi₀
  have hak : a = f ((A *ᵥ x) i₀ / x i₀) := by
    apply mul_right_cancel₀ hfx
    rw [← hcomp i₀, ← map_mul, div_mul_cancel₀ _ hi₀]
  have hk0 : (A *ᵥ x) i₀ / x i₀ ≠ 0 := by
    intro h0
    apply hx
    apply hAinj
    funext i
    apply f.injective
    rw [hcomp i, hak, h0, map_zero, zero_mul, Pi.zero_apply, map_zero]
  have hk2 : ((A *ᵥ x) i₀ / x i₀) ^ 2 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ((A *ᵥ x) i₀ / x i₀) hk0
    rwa [hK] at this
  rw [hak, ← map_pow, hk2, map_one]

theorem kl3clc_sq_mat {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {ι : Type}
    [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 4) (B C A : Matrix ι ι K)
    (hB13 : B ^ 13 = 1) (hBne : B ≠ 1) (hCB : C * B = B ^ 3 * C)
    (hCinj : ∀ v, C *ᵥ v = 0 → v = 0) (hAinj : ∀ v, A *ᵥ v = 0 → v = 0)
    (hAB : A * B = B * A) (hAC : A * C = C * A) : A * A = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK
  let Ω := AlgebraicClosure K
  let f : K →+* Ω := algebraMap K Ω
  let F : Matrix ι ι K →+* Matrix ι ι Ω := f.mapMatrix
  have hF : ∀ M, F M = M.map f := fun M => rfl
  have h13 : ((13 : ℕ) : Ω) ≠ 0 := by
    have h3K : ((3 : ℕ) : K) = 0 := by
      have := Nat.cast_card_eq_zero K
      rwa [hcardK] at this
    have h3Ω : ((3 : ℕ) : Ω) = 0 := by rw [← map_natCast f, h3K, map_zero]
    have : ((13 : ℕ) : Ω) = 4 * ((3 : ℕ) : Ω) + 1 := by norm_num
    rw [this, h3Ω, mul_zero, zero_add]
    exact one_ne_zero
  obtain ⟨u, hu0, hBu⟩ := kl3clc_fixed hK hι B hB13
  have hB'13 : B.map f ^ 13 = 1 := by rw [← hF, ← map_pow, hB13, map_one]
  have hB'ne : B.map f ≠ 1 := by
    intro h
    apply hBne
    rw [← hF, ← map_one F] at h
    exact (Matrix.map_injective f.injective) h
  have hCB' : C.map f * B.map f = B.map f ^ 3 * C.map f := by
    rw [← hF, ← hF, ← map_pow, ← map_mul, ← map_mul, hCB]
  have hAB' : A.map f * B.map f = B.map f * A.map f := by
    rw [← hF, ← hF, ← map_mul, ← map_mul, hAB]
  have hAC' : A.map f * C.map f = C.map f * A.map f := by
    rw [← hF, ← hF, ← map_mul, ← map_mul, hAC]
  have hC'inj : ∀ v : ι → Ω, C.map f *ᵥ v = 0 → v = 0 := by
    intro v hv
    by_contra hv0
    have hdet : (C.map f).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, hv⟩
    have hCdet : C.det = 0 := by
      apply f.injective
      rw [RingHom.map_det, map_zero]
      exact hdet
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hCdet
    exact hy0 (hCinj y hy)
  obtain ⟨μ, hμ1, hμ13, w, hw, hBw⟩ := kl3cl_exists_eig_ne_one h13 (B.map f) hB'13 hB'ne
  have hu' : (fun i => f (u i)) ≠ 0 := by
    intro h
    apply hu0
    funext i
    apply f.injective
    simpa using congrFun h i
  have hBu' : B.map f *ᵥ (fun i => f (u i)) = fun i => f (u i) := by
    rw [kl3clc_map_mulVec, hBu]
  obtain ⟨a, α, hau, hαB, hsq⟩ := kl3clc_diag hι (B.map f) (C.map f) (A.map f) hB'13 hCB' hC'inj
    hAB' hAC' hμ1 hμ13 hw hBw hu' hBu'
  have ha2 : a ^ 2 = 1 := kl3clc_rat_sq hcardK f A hAinj hu0 hau
  have hα2 : α ^ 2 = 1 := by
    obtain ⟨y, hy⟩ : ∃ y : ι → K, (B - 1) *ᵥ y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hBne
      ext i j
      have := congrFun (hcon (Pi.single j 1)) i
      simpa [Matrix.sub_mulVec, Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply,
        sub_eq_zero] using this
    refine kl3clc_rat_sq hcardK f A hAinj hy ?_
    have hsub : (B - 1).map f = B.map f - 1 := by rw [← hF, map_sub, map_one, hF]
    have hx : (B.map f - 1) *ᵥ (fun i => f (y i)) = fun i => f (((B - 1) *ᵥ y) i) := by
      rw [← hsub]
      exact kl3clc_map_mulVec f (B - 1) y
    have h1 := congrArg (fun M : Matrix ι ι Ω => M *ᵥ (fun i => f (y i))) hαB
    simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec] at h1
    rw [hx] at h1
    exact h1
  have hAA : (A * A).map f = (1 : Matrix ι ι K).map f := by
    rw [← hF, ← hF, map_mul, map_one, hF]
    exact hsq ha2 hα2
  exact Matrix.map_injective f.injective hAA

end FiniteField

theorem kl3clc_sq_eq_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {ι : Type}
    [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 4) (B C A : GL ι K)
    (hB13 : B ^ 13 = 1) (hBne : B ≠ 1) (hCB : C * B = B ^ 3 * C)
    (hAB : A * B = B * A) (hAC : A * C = C * A) : A * A = 1 := by
  have hm : (A : Matrix ι ι K) * (A : Matrix ι ι K) = 1 := by
    refine kl3clc_sq_mat hK hι (B : Matrix ι ι K) (C : Matrix ι ι K) (A : Matrix ι ι K) ?_ ?_ ?_
      (kl3cl_gl_mulVec_inj C) (kl3cl_gl_mulVec_inj A) ?_ ?_
    · rw [← Units.val_pow_eq_pow_val, hB13, Units.val_one]
    · intro h
      exact hBne (Units.ext (by simpa using h))
    · have := congrArg (fun u : GL ι K => (u : Matrix ι ι K)) hCB
      simpa [Units.val_mul, Units.val_pow_eq_pow_val] using this
    · have := congrArg (fun u : GL ι K => (u : Matrix ι ι K)) hAB
      simpa using this
    · have := congrArg (fun u : GL ι K => (u : Matrix ι ι K)) hAC
      simpa using this
  exact Units.ext (by simpa using hm)

end CFSG.GH74.Generic.S1
