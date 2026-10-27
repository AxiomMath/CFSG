module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport

public section

section Part1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

@[expose] noncomputable def st (M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := (M.map h.bar)ᵀ

@[expose] noncomputable def sv (x : Fin n → K) : Fin n → K := fun i => h.bar (x i)

@[expose] noncomputable def hf (x y : Fin n → K) : K := sv h x ⬝ᵥ y

theorem st_mul (M N : Matrix (Fin n) (Fin n) K) : st h (M * N) = st h N * st h M := by
  unfold st; rw [Matrix.map_mul, Matrix.transpose_mul]

theorem st_add (M N : Matrix (Fin n) (Fin n) K) : st h (M + N) = st h M + st h N := by
  ext i j; simp [st]

theorem st_sub (M N : Matrix (Fin n) (Fin n) K) : st h (M - N) = st h M - st h N := by
  ext i j; simp [st]

theorem st_smul (c : K) (M : Matrix (Fin n) (Fin n) K) : st h (c • M) = h.bar c • st h M := by
  ext i j; simp [st]

theorem st_st (M : Matrix (Fin n) (Fin n) K) : st h (st h M) = M := by
  ext i j; simp [st, h.bar_bar]

theorem st_one : st h (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [st]
  · simp [st, Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

theorem sv_sv (x : Fin n → K) : sv h (sv h x) = x := by
  funext i; simp [sv, h.bar_bar]

theorem sv_smul (c : K) (x : Fin n → K) : sv h (c • x) = h.bar c • sv h x := by
  funext i; simp [sv]

theorem sv_zero : sv h (0 : Fin n → K) = 0 := by
  funext i; simp [sv]

theorem sv_ne_zero {x : Fin n → K} (hx : x ≠ 0) : sv h x ≠ 0 := by
  intro h0
  apply hx
  rw [← sv_sv h x, h0, sv_zero]

theorem sv_st_mulVec (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    sv h (st h M *ᵥ x) = sv h x ᵥ* M := by
  funext j
  simp only [sv, st, Matrix.mulVec, dotProduct, Matrix.vecMul, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, h.bar_bar]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sv_mulVec (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    sv h (M *ᵥ x) = sv h x ᵥ* st h M := by
  conv_lhs => rw [← st_st h M]
  exact sv_st_mulVec h (st h M) x

theorem hf_mulVec (x y : Fin n → K) (M : Matrix (Fin n) (Fin n) K) :
    hf h x (M *ᵥ y) = hf h (st h M *ᵥ x) y := by
  unfold hf
  rw [sv_st_mulVec, Matrix.dotProduct_mulVec]

theorem bar_hf (x y : Fin n → K) : h.bar (hf h x y) = hf h y x := by
  simp only [hf, sv, dotProduct, map_sum, map_mul, h.bar_bar]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem bar_hf_self (x : Fin n → K) : h.bar (hf h x x) = hf h x x := bar_hf h x x

theorem st_vecMulVec (a b : Fin n → K) : st h (vecMulVec a b) = vecMulVec (sv h b) (sv h a) := by
  ext i j
  simp [st, vecMulVec_apply, sv, mul_comm]

theorem vecMulVec_mulVec_apply (a b x : Fin n → K) : vecMulVec a b *ᵥ x = (b ⬝ᵥ x) • a := by
  ext i
  simp only [vecMulVec_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part1

section Part2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

@[expose] def IsUni (N : Matrix (Fin n) (Fin n) K) : Prop := (1 + st h N) * (1 + N) = 1

variable {h} {N : Matrix (Fin n) (Fin n) K}

theorem IsUni.swap (hU : IsUni h N) : (1 + N) * (1 + st h N) = 1 := mul_eq_one_comm.1 hU

theorem IsUni.eq1 (hU : IsUni h N) : st h N + N + st h N * N = 0 := by
  have h2 : (1 : Matrix (Fin n) (Fin n) K) + (st h N + N + st h N * N) = 1 + 0 := by
    calc (1 : Matrix (Fin n) (Fin n) K) + (st h N + N + st h N * N)
        = (1 + st h N) * (1 + N) := by noncomm_ring
      _ = 1 + 0 := by rw [hU, add_zero]
  exact add_left_cancel h2

theorem IsUni.eq2 (hU : IsUni h N) : N + st h N + N * st h N = 0 := by
  have h2 : (1 : Matrix (Fin n) (Fin n) K) + (N + st h N + N * st h N) = 1 + 0 := by
    calc (1 : Matrix (Fin n) (Fin n) K) + (N + st h N + N * st h N)
        = (1 + N) * (1 + st h N) := by noncomm_ring
      _ = 1 + 0 := by rw [hU.swap, add_zero]
  exact add_left_cancel h2

theorem IsUni.comm (hU : IsUni h N) : N * st h N = st h N * N := by
  have h3 : (st h N + N) + st h N * N = (st h N + N) + N * st h N := by
    rw [hU.eq1, add_comm (st h N) N, hU.eq2]
  exact (add_left_cancel h3).symm

theorem IsUni.mulVec_ker {x : Fin n → K} (hU : IsUni h N) (hx : N *ᵥ x = 0) : st h N *ᵥ x = 0 := by
  have h1 := congrArg (fun M => M *ᵥ x) hU.eq1
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, Matrix.zero_mulVec,
    add_zero] at h1
  exact h1

theorem hf_zero_left (y : Fin n → K) : hf h (0 : Fin n → K) y = 0 := by
  simp [hf, sv_zero]

theorem IsUni.hf_im_ker (hU : IsUni h N) {y x : Fin n → K} (hx : N *ᵥ x = 0) :
    hf h (N *ᵥ y) x = 0 := by
  have h1 : hf h x (N *ᵥ y) = 0 := by
    rw [hf_mulVec, hU.mulVec_ker hx, hf_zero_left]
  rw [← bar_hf h, h1, map_zero]

theorem IsUni.hf_W_ker (hU : IsUni h N) {w x : Fin n → K} (hw : w ∈ Wsp N) (hx : N *ᵥ x = 0) :
    hf h w x = 0 := by
  obtain ⟨-, v, rfl⟩ := mem_Wsp.1 hw
  exact hU.hf_im_ker hx

theorem IsUni.hf_ker_W (hU : IsUni h N) {w x : Fin n → K} (hw : w ∈ Wsp N) (hx : N *ᵥ x = 0) :
    hf h x w = 0 := by
  rw [← bar_hf h, hU.hf_W_ker hw hx, map_zero]

@[expose] def Flag (N X : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ x, N *ᵥ (X *ᵥ x) = 0) ∧ (∀ x, N *ᵥ x = 0 → X *ᵥ x ∈ Wsp N) ∧ (∀ w ∈ Wsp N, X *ᵥ w = 0)

theorem Flag.add {X Y : Matrix (Fin n) (Fin n) K} (hX : Flag N X) (hY : Flag N Y) :
    Flag N (X + Y) := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun w hw => ?_⟩
  · rw [Matrix.add_mulVec, Matrix.mulVec_add, hX.1, hY.1, add_zero]
  · rw [Matrix.add_mulVec]; exact add_mem (hX.2.1 x hx) (hY.2.1 x hx)
  · rw [Matrix.add_mulVec, hX.2.2 w hw, hY.2.2 w hw, add_zero]

theorem Flag.neg {X : Matrix (Fin n) (Fin n) K} (hX : Flag N X) : Flag N (-X) := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun w hw => ?_⟩
  · rw [Matrix.neg_mulVec, Matrix.mulVec_neg, hX.1, neg_zero]
  · rw [Matrix.neg_mulVec]; exact neg_mem (hX.2.1 x hx)
  · rw [Matrix.neg_mulVec, hX.2.2 w hw, neg_zero]

theorem Flag.mul {X Y : Matrix (Fin n) (Fin n) K} (hX : Flag N X) (hY : Flag N Y) :
    Flag N (X * Y) := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun w hw => ?_⟩
  · rw [← Matrix.mulVec_mulVec, hX.1]
  · rw [← Matrix.mulVec_mulVec]
    have := hY.2.1 x hx
    rw [mem_Wsp] at this
    exact hX.2.1 _ this.1
  · rw [← Matrix.mulVec_mulVec, hY.2.2 w hw, Matrix.mulVec_zero]

theorem Flag.cube {X : Matrix (Fin n) (Fin n) K} (hX : Flag N X) : X * X * X = 0 := by
  apply matrix_eq_zero_of_mulVec
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h1 : N *ᵥ (X *ᵥ x) = 0 := hX.1 x
  have h2 := hX.2.1 _ h1
  rw [hX.2.2 _ h2]

theorem Flag.isNilpotent {X : Matrix (Fin n) (Fin n) K} (hX : Flag N X) : IsNilpotent X :=
  ⟨3, by rw [pow_succ, pow_two, hX.cube]⟩

theorem isUni_of_eq {X : Matrix (Fin n) (Fin n) K} (hX : X + st h X + st h X * X = 0) :
    IsUni h X := by
  unfold IsUni
  calc (1 + st h X) * (1 + X) = 1 + (X + st h X + st h X * X) := by noncomm_ring
    _ = 1 := by rw [hX, add_zero]

variable (h) in
@[expose] noncomputable def Tm (w : Fin n → K) (t : K) : Matrix (Fin n) (Fin n) K :=
  t • vecMulVec w (sv h w)

variable (h) in
@[expose] noncomputable def Em (v w : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  vecMulVec v (sv h w) - vecMulVec w (sv h v) - (hf h v v / 2) • vecMulVec w (sv h w)

theorem Tm_mulVec (w : Fin n → K) (t : K) (x : Fin n → K) :
    Tm h w t *ᵥ x = (t * hf h w x) • w := by
  unfold Tm
  rw [Matrix.smul_mulVec, vecMulVec_mulVec_apply, smul_smul]
  rfl

theorem Em_mulVec (v w : Fin n → K) (x : Fin n → K) :
    Em h v w *ᵥ x = hf h w x • v - hf h v x • w - (hf h v v / 2 * hf h w x) • w := by
  unfold Em
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec_apply,
    vecMulVec_mulVec_apply, vecMulVec_mulVec_apply, smul_smul]
  rfl

theorem sv_vecMul_N (hU : IsUni h N) {a : Fin n → K} (ha : N *ᵥ a = 0) : sv h a ᵥ* N = 0 := by
  rw [← sv_st_mulVec, hU.mulVec_ker ha, sv_zero]

theorem vecMulVec_sv_mul_N (hU : IsUni h N) {a : Fin n → K} (ha : N *ᵥ a = 0) (b : Fin n → K) :
    vecMulVec b (sv h a) * N = 0 := by
  rw [vecMulVec_mul, sv_vecMul_N hU ha]
  ext i j; simp [vecMulVec_apply]

theorem N_mul_vecMulVec (a : Fin n → K) (ha : N *ᵥ a = 0) (b : Fin n → K) :
    N * vecMulVec a b = 0 := by
  rw [mul_vecMulVec, ha]
  ext i j; simp [vecMulVec_apply]

theorem Tm_comm (hU : IsUni h N) {w : Fin n → K} (hw : w ∈ Wsp N) (t : K) : N * Tm h w t = 0 ∧ Tm h w t * N = 0 := by
  have hw0 := (mem_Wsp.1 hw).1
  refine ⟨?_, ?_⟩
  · unfold Tm; rw [Matrix.mul_smul, N_mul_vecMulVec w hw0, smul_zero]
  · unfold Tm; rw [Matrix.smul_mul, vecMulVec_sv_mul_N hU hw0, smul_zero]

theorem Em_comm (hU : IsUni h N) {v w : Fin n → K} (hw : w ∈ Wsp N) (hv : N *ᵥ v = 0) :
    N * Em h v w = 0 ∧ Em h v w * N = 0 := by
  have hw0 := (mem_Wsp.1 hw).1
  refine ⟨?_, ?_⟩
  · unfold Em
    simp only [Matrix.mul_sub, Matrix.mul_smul, N_mul_vecMulVec v hv, N_mul_vecMulVec w hw0,
      smul_zero, sub_zero]
  · unfold Em
    simp only [Matrix.sub_mul, Matrix.smul_mul, vecMulVec_sv_mul_N hU hw0,
      vecMulVec_sv_mul_N hU hv, smul_zero, sub_zero]

theorem Tm_flag (hU : IsUni h N) {w : Fin n → K} (hw : w ∈ Wsp N) (t : K) : Flag N (Tm h w t) := by
  have hw0 := (mem_Wsp.1 hw).1
  refine ⟨fun x => ?_, fun x hx => ?_, fun w' hw' => ?_⟩
  · rw [Tm_mulVec, Matrix.mulVec_smul, hw0, smul_zero]
  · rw [Tm_mulVec, hU.hf_W_ker hw hx, mul_zero, zero_smul]; exact zero_mem _
  · rw [Tm_mulVec, hU.hf_W_ker hw (mem_Wsp.1 hw').1, mul_zero, zero_smul]

theorem Em_flag (hU : IsUni h N) {v w : Fin n → K} (hw : w ∈ Wsp N) (hv : N *ᵥ v = 0) :
    Flag N (Em h v w) := by
  have hw0 := (mem_Wsp.1 hw).1
  refine ⟨fun x => ?_, fun x hx => ?_, fun w' hw' => ?_⟩
  · rw [Em_mulVec]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hw0, hv, smul_zero, sub_zero]
  · rw [Em_mulVec, hU.hf_W_ker hw hx]
    simp only [zero_smul, zero_sub, mul_zero, sub_zero]
    exact neg_mem (Submodule.smul_mem _ _ hw)
  · have hw'0 := (mem_Wsp.1 hw').1
    rw [Em_mulVec, hU.hf_W_ker hw hw'0, hU.hf_ker_W hw' hv]
    simp

theorem Tm_isUni (hU : IsUni h N) {w : Fin n → K} (hw : w ∈ Wsp N) {t : K} (ht : h.bar t = -t) :
    IsUni h (Tm h w t) := by
  have hww : sv h w ⬝ᵥ w = 0 := hU.hf_W_ker hw (mem_Wsp.1 hw).1
  have hst : st h (Tm h w t) = h.bar t • vecMulVec w (sv h w) := by
    unfold Tm; rw [st_smul, st_vecMulVec, sv_sv]
  have hZ : vecMulVec w (sv h w) * vecMulVec w (sv h w) = 0 := by
    rw [vecMulVec_mul_vecMulVec, hww, zero_smul, vecMulVec_zero]
  apply isUni_of_eq
  rw [hst]
  unfold Tm
  rw [Matrix.smul_mul, Matrix.mul_smul, hZ, smul_zero, smul_zero, add_zero, ht, neg_smul,
    add_neg_cancel]

theorem bar_two_inv : h.bar (2 : K)⁻¹ = (2 : K)⁻¹ := by
  rw [map_inv₀]; congr 1; exact map_ofNat h.bar 2

theorem Em_isUni (h2 : (2 : K) ≠ 0) (hU : IsUni h N) {v w : Fin n → K} (hw : w ∈ Wsp N)
    (hv : N *ᵥ v = 0) :
    IsUni h (Em h v w) := by
  have d_ww : sv h w ⬝ᵥ w = 0 := hU.hf_W_ker hw (mem_Wsp.1 hw).1
  have d_wv : sv h w ⬝ᵥ v = 0 := hU.hf_W_ker hw hv
  have d_vw : sv h v ⬝ᵥ w = 0 := hU.hf_ker_W hw hv
  have d_vv : sv h v ⬝ᵥ v = hf h v v := rfl
  have hbar : h.bar (hf h v v / 2) = hf h v v / 2 := by
    rw [div_eq_mul_inv, map_mul, bar_hf_self, bar_two_inv]
  have hst : st h (Em h v w) = vecMulVec w (sv h v) - vecMulVec v (sv h w) -
      (hf h v v / 2) • vecMulVec w (sv h w) := by
    unfold Em
    rw [st_sub, st_sub, st_smul, st_vecMulVec, st_vecMulVec, st_vecMulVec, sv_sv, sv_sv, hbar]
  apply isUni_of_eq
  rw [hst]
  unfold Em
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_mul_vecMulVec, d_ww, d_wv, d_vw, d_vv, zero_smul, smul_zero, sub_zero, zero_sub,
    add_zero, smul_smul, vecMulVec_zero, vecMulVec_smul]
  match_scalars <;> field_simp <;> ring

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part2

section Part3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

variable (A : Matrix (Fin n) (Fin n) K) (σ : K ≃+* K)

@[expose] noncomputable def cj (X : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  A * X.map σ * st h A

@[expose] noncomputable def th (x : Fin n → K) : Fin n → K := A *ᵥ (fun i => σ (x i))

variable {h A σ}

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

theorem cj_add (X Y : Matrix (Fin n) (Fin n) K) : cj h A σ (X + Y) = cj h A σ X + cj h A σ Y := by
  unfold cj
  have : (X + Y).map σ = X.map σ + Y.map σ := by ext i j; simp
  rw [this, Matrix.mul_add, Matrix.add_mul]

theorem cj_smul (c : K) (X : Matrix (Fin n) (Fin n) K) : cj h A σ (c • X) = σ c • cj h A σ X := by
  unfold cj
  have : (c • X).map σ = σ c • X.map σ := by ext i j; simp
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem cj_mul (hA : st h A * A = 1) (X Y : Matrix (Fin n) (Fin n) K) :
    cj h A σ (X * Y) = cj h A σ X * cj h A σ Y := by
  unfold cj
  calc A * (X * Y).map σ * st h A
      = A * X.map σ * (st h A * A) * Y.map σ * st h A := by
        rw [hA, Matrix.mul_one, Matrix.map_mul]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem cj_one (hA' : A * st h A = 1) : cj h A σ (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  unfold cj
  have : (1 : Matrix (Fin n) (Fin n) K).map σ = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [this, Matrix.mul_one, hA']

theorem cj_zero : cj h A σ (0 : Matrix (Fin n) (Fin n) K) = 0 := by
  unfold cj; simp

theorem cj_neg (X : Matrix (Fin n) (Fin n) K) : cj h A σ (-X) = -cj h A σ X := by
  unfold cj
  have : (-X).map σ = -(X.map σ) := by ext i j; simp
  rw [this]; simp

theorem cj_sub (X Y : Matrix (Fin n) (Fin n) K) : cj h A σ (X - Y) = cj h A σ X - cj h A σ Y := by
  rw [sub_eq_add_neg, cj_add, cj_neg, ← sub_eq_add_neg]

theorem cj_pow (hA : st h A * A = 1) (hA' : A * st h A = 1) (X : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    cj h A σ (X ^ k) = (cj h A σ X) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, cj_one hA']
  | succ k ih => rw [pow_succ, cj_mul hA, ih, pow_succ]

theorem cj_isNilpotent (hA : st h A * A = 1) (hA' : A * st h A = 1)
    {X : Matrix (Fin n) (Fin n) K} (hX : IsNilpotent X) :
    IsNilpotent (cj h A σ X) := by
  obtain ⟨k, hk⟩ := hX
  exact ⟨k, by rw [← cj_pow hA hA', hk, cj_zero]⟩

theorem th_smul (c : K) (x : Fin n → K) : th A σ (c • x) = σ c • th A σ x := by
  unfold th
  rw [← Matrix.mulVec_smul]; congr 1; ext i; simp

theorem th_ne_zero (hAinj : ∀ x, A *ᵥ x = 0 → x = 0) {x : Fin n → K} (hx : x ≠ 0) :
    th A σ x ≠ 0 := by
  intro h0
  apply hx
  have := hAinj _ h0
  ext i
  have := congrFun this i
  simpa using this

theorem sv_th (x : Fin n → K) : sv h (th A σ x) = (fun i => σ (sv h x i)) ᵥ* st h A := by
  unfold th
  rw [sv_mulVec]
  congr 1
  funext i
  simp [sv, map_bar_comm h σ]

theorem hf_th (hA : st h A * A = 1) (x y : Fin n → K) :
    hf h (th A σ x) (th A σ y) = σ (hf h x y) := by
  unfold th
  rw [hf_mulVec, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  simp only [hf, sv, dotProduct, map_sum, map_mul, map_bar_comm h σ]

theorem cj_vecMulVec_sv (x y : Fin n → K) :
    cj h A σ (vecMulVec x (sv h y)) = vecMulVec (th A σ x) (sv h (th A σ y)) := by
  unfold cj
  have : (vecMulVec x (sv h y)).map σ = vecMulVec (fun i => σ (x i)) (fun i => σ (sv h y i)) := by
    ext i j; simp [vecMulVec_apply]
  rw [this, mul_vecMulVec, vecMulVec_mul, sv_th]
  rfl

theorem cj_Tm (w : Fin n → K) (t : K) : cj h A σ (Tm h w t) = Tm h (th A σ w) (σ t) := by
  unfold Tm
  rw [cj_smul, cj_vecMulVec_sv]

theorem cj_Em (hA : st h A * A = 1) (v w : Fin n → K) :
    cj h A σ (Em h v w) = Em h (th A σ v) (th A σ w) := by
  unfold Em
  rw [cj_sub, cj_sub, cj_smul, cj_vecMulVec_sv, cj_vecMulVec_sv,
    cj_vecMulVec_sv, hf_th hA, map_div₀, map_ofNat]

theorem cj_st (X : Matrix (Fin n) (Fin n) K) : st h (cj h A σ X) = cj h A σ (st h X) := by
  unfold cj
  rw [st_mul, st_mul, st_st]
  have : st h (X.map σ) = (st h X).map σ := by
    ext i j; simp [st, map_bar_comm h σ]
  rw [this, mul_assoc]

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part3

section Part4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} {h : UnitaryFieldData p f K}

noncomputable def cayR {Y : Matrix (Fin n) (Fin n) K} (hY : IsNilpotent Y) : Matrix (Fin n) (Fin n) K :=
  ((hY.isUnit_one_sub.unit⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K)

theorem one_sub_mul_cayR {Y : Matrix (Fin n) (Fin n) K} (hY : IsNilpotent Y) :
    (1 - Y) * cayR hY = 1 := by
  have := hY.isUnit_one_sub.unit.mul_inv
  rwa [IsUnit.unit_spec] at this

theorem cayR_mul_one_sub {Y : Matrix (Fin n) (Fin n) K} (hY : IsNilpotent Y) :
    cayR hY * (1 - Y) = 1 := by
  have := hY.isUnit_one_sub.unit.inv_mul
  rwa [IsUnit.unit_spec] at this

theorem exists_cayley {Y N : Matrix (Fin n) (Fin n) K} (hY : IsNilpotent Y) (hsk : st h Y = -Y)
    (hYN : N * Y = Y * N) :
    ∃ X, IsNilpotent X ∧ IsUni h X ∧ N * X = X * N ∧ (1 + X) * (1 - Y) = 1 + Y := by
  set R := cayR hY with hRdef
  have hR1 : (1 - Y) * R = 1 := one_sub_mul_cayR hY
  have hR2 : R * (1 - Y) = 1 := cayR_mul_one_sub hY
  have hYR : Y * R = R * Y := by
    have e1 : R - Y * R = 1 := by rw [← hR1]; noncomm_ring
    have e2 : R - R * Y = 1 := by rw [← hR2]; noncomm_ring
    have : R - Y * R = R - R * Y := e1.trans e2.symm
    exact sub_right_injective this
  have hRN : R * N = N * R := by
    have hNY1 : N * (1 - Y) = (1 - Y) * N := by rw [mul_sub, sub_mul, hYN]; simp
    calc R * N = R * N * ((1 - Y) * R) := by rw [hR1, mul_one]
      _ = R * (N * (1 - Y)) * R := by simp only [mul_assoc]
      _ = R * ((1 - Y) * N) * R := by rw [hNY1]
      _ = (R * (1 - Y)) * N * R := by simp only [mul_assoc]
      _ = N * R := by rw [hR2, one_mul]
  have hS : (1 : Matrix (Fin n) (Fin n) K) + (2 : K) • (Y * R) = (1 + Y) * R := by
    have e1 : R = 1 + Y * R := by
      have : R - Y * R = 1 := by rw [← hR1]; noncomm_ring
      rw [← this]; abel
    calc (1 : Matrix (Fin n) (Fin n) K) + (2 : K) • (Y * R) = (1 + Y * R) + Y * R := by
          rw [two_smul]; abel
      _ = R + Y * R := by rw [← e1]
      _ = (1 + Y) * R := by rw [add_mul, one_mul]
  refine ⟨(2 : K) • (Y * R), ?_, ?_, ?_, ?_⟩
  · exact ((Commute.isNilpotent_mul_right hYR hY)).smul 2
  ·
    have hsr1 : st h R * (1 + Y) = 1 := by
      have := congrArg (st h) hR1
      rw [st_mul, st_sub, st_one, hsk, sub_neg_eq_add] at this
      exact this
    have e : 1 + st h ((2 : K) • (Y * R)) = st h R * (1 - Y) := by
      have h1 : (1 : Matrix (Fin n) (Fin n) K) + st h ((2 : K) • (Y * R)) =
          st h ((1 : Matrix (Fin n) (Fin n) K) + (2 : K) • (Y * R)) := by
        rw [st_add, st_one]
      rw [h1, hS, st_mul, st_add, st_one, hsk, ← sub_eq_add_neg]
    unfold IsUni
    rw [e, hS]
    calc st h R * (1 - Y) * ((1 + Y) * R) = st h R * ((1 + Y) * (1 - Y)) * R := by
          have : (1 - Y) * (1 + Y) = (1 + Y) * (1 - Y) := by noncomm_ring
          calc st h R * (1 - Y) * ((1 + Y) * R) = st h R * ((1 - Y) * (1 + Y)) * R := by
                simp only [mul_assoc]
            _ = _ := by rw [this]
      _ = (st h R * (1 + Y)) * ((1 - Y) * R) := by simp only [mul_assoc]
      _ = 1 := by rw [hsr1, hR1, one_mul]
  · rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [← mul_assoc, hYN, mul_assoc, ← hRN, ← mul_assoc]
  · rw [hS, mul_assoc, hR2, mul_one]

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part4

section Part5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} {h : UnitaryFieldData p f K}

theorem exists_traceZero_ne_zero (h : UnitaryFieldData p f K) : ∃ t : K, t ≠ 0 ∧ h.bar t = -t := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  refine ⟨c - h.bar c, sub_ne_zero.2 (Ne.symm hc), ?_⟩
  rw [map_sub, h.bar_bar]; abel

theorem exists_hf_eq_one (h : UnitaryFieldData p f K) {w : Fin n → K} (hw : w ≠ 0) :
    ∃ x : Fin n → K, hf h w x = 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h'; push Not at h'; exact hw (funext h')
  have hb : h.bar (w i) ≠ 0 := by
    intro h0
    apply hi
    have := congrArg h.bar h0
    rwa [h.bar_bar, map_zero] at this
  refine ⟨Pi.single i (h.bar (w i))⁻¹, ?_⟩
  simp [hf, sv, dotProduct, Pi.single_apply, hb]

theorem hf_smul_left (c : K) (x y : Fin n → K) : hf h (c • x) y = h.bar c * hf h x y := by
  simp [hf, sv_smul, smul_dotProduct]

theorem inj_of_unitary {A : Matrix (Fin n) (Fin n) K} (hA : st h A * A = 1) (x : Fin n → K)
    (hx : A *ᵥ x = 0) : x = 0 := by
  have := congrArg (fun y => st h A *ᵥ y) hx
  simpa [Matrix.mulVec_mulVec, hA] using this

structure KData (h : UnitaryFieldData p f K) (N A : Matrix (Fin n) (Fin n) K) (σ : K ≃+* K) :
    Prop where
  hA : st h A * A = 1
  hA' : A * st h A = 1
  fixN : cj h A σ N = N
  fixT : ∀ w ∈ Wsp N, ∀ t : K, h.bar t = -t → cj h A σ (Tm h w t) = Tm h w t
  fixE : ∀ w ∈ Wsp N, ∀ v : Fin n → K, N *ᵥ v = 0 → cj h A σ (Em h v w) = Em h v w

variable {N A : Matrix (Fin n) (Fin n) K} {σ : K ≃+* K}

theorem KData.th_eigen (hK : KData h N A σ) {w : Fin n → K} (hw : w ∈ Wsp N)
    (hw0 : w ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ th A σ w = c • w ∧ ∀ t : K, h.bar t = -t → σ t * (c * h.bar c) = t := by
  obtain ⟨t0, ht0, ht0b⟩ := exists_traceZero_ne_zero h
  have hθ : th A σ w ≠ 0 := th_ne_zero (inj_of_unitary hK.hA) hw0
  have e0 := hK.fixT w hw t0 ht0b
  rw [cj_Tm] at e0
  unfold Tm at e0
  have hσt0 : σ t0 ≠ 0 := fun h0 => ht0 (σ.injective (by rw [h0, map_zero]))
  obtain ⟨c1, hc1, -⟩ := rank_one_eq (a := σ t0 • th A σ w) (b := t0 • sv h w) hw0
    (sv_ne_zero h hθ) (by rw [smul_vecMulVec, vecMulVec_smul]; exact e0)
  have hc : th A σ w = ((σ t0)⁻¹ * c1) • w := by
    rw [mul_smul, ← hc1, smul_smul, inv_mul_cancel₀ hσt0, one_smul]
  refine ⟨(σ t0)⁻¹ * c1, ?_, hc, ?_⟩
  · intro h0
    rw [h0, zero_smul] at hc
    exact hθ hc
  · intro t ht
    have e1 := hK.fixT w hw t ht
    rw [cj_Tm] at e1
    unfold Tm at e1
    rw [hc, smul_vecMulVec, sv_smul, vecMulVec_smul, smul_smul, smul_smul] at e1
    have hZ : vecMulVec w (sv h w) ≠ 0 := vecMulVec_ne_zero hw0 (sv_ne_zero h hw0)
    exact smul_left_injective K hZ (by simpa [mul_comm, mul_assoc] using e1)

theorem KData.eichler (hK : KData h N A σ) {w : Fin n → K} (hw : w ∈ Wsp N) (hw0 : w ≠ 0)
    {c : K} (hc : th A σ w = c • w) {v : Fin n → K} (hv : N *ᵥ v = 0) :
    ∃ e : K, h.bar c • th A σ v = v + e • w := by
  obtain ⟨x0, hx0⟩ := exists_hf_eq_one h hw0
  have e0 := hK.fixE w hw v hv
  rw [cj_Em hK.hA, hc] at e0
  have e1 := congrArg (fun M => M *ᵥ x0) e0
  simp only [Em_mulVec, hf_smul_left, hx0, mul_one, one_smul] at e1
  refine ⟨hf h (th A σ v) x0 * c + (hf h (th A σ v) (th A σ v) / 2 * h.bar c) * c -
    hf h v x0 - hf h v v / 2, ?_⟩
  linear_combination (norm := module) e1

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part5

section Part6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} {h : UnitaryFieldData p f K}
variable {N A : Matrix (Fin n) (Fin n) K} {σ : K ≃+* K}

theorem KData.sigma_of_exists (hK : KData h N A σ) {w0 : Fin n → K} (hw : w0 ∈ Wsp N)
    (hw0 : w0 ≠ 0) {v : Fin n → K} (hv : N *ᵥ v = 0) (hvn : ∀ e : K, v ≠ e • w0) (x : K) :
    σ x = x := by
  obtain ⟨c, hc0, hc, -⟩ := hK.th_eigen hw hw0
  obtain ⟨e, he⟩ := hK.eichler hw hw0 hc hv
  have hv' : N *ᵥ (x • v) = 0 := by rw [Matrix.mulVec_smul, hv, smul_zero]
  obtain ⟨e', he'⟩ := hK.eichler hw hw0 hc hv'
  rw [th_smul, smul_comm, he, smul_add, smul_smul] at he'
  by_contra hne
  have hne' : σ x - x ≠ 0 := sub_ne_zero.2 hne
  apply hvn ((e' - σ x * e) / (σ x - x))
  have : (σ x - x) • v = (e' - σ x * e) • w0 := by
    rw [sub_smul, sub_smul]
    linear_combination (norm := module) he'
  have h3 : v = (σ x - x)⁻¹ • ((σ x - x) • v) := by rw [smul_smul, inv_mul_cancel₀ hne', one_smul]
  rw [h3, this, smul_smul, div_eq_mul_inv, mul_comm]

theorem sigma_id_of_traceZero (h2 : (2 : K) ≠ 0)
    (hσ : ∀ a : K, h.bar a = -a → σ a = a) (x : K) : σ x = x := by
  obtain ⟨t0, ht0, ht0b⟩ := exists_traceZero_ne_zero h
  set r : K := (x + h.bar x) / 2 with hr
  set s : K := (x - h.bar x) / 2 with hs
  have hbar2 : h.bar (2 : K)⁻¹ = (2 : K)⁻¹ := bar_two_inv
  have hrb : h.bar r = r := by
    rw [hr, div_eq_mul_inv, map_mul, map_add, h.bar_bar, bar_two_inv, add_comm]
  have hsb : h.bar s = -s := by
    rw [hs, div_eq_mul_inv, map_mul, map_sub, h.bar_bar, bar_two_inv]
    rw [← neg_mul, neg_sub]
  have hx : x = r + s := by rw [hr, hs]; field_simp; ring
  have hσs : σ s = s := hσ s hsb
  have hrt : h.bar (r * t0) = -(r * t0) := by rw [map_mul, hrb, ht0b, mul_neg]
  have hσrt : σ (r * t0) = r * t0 := hσ _ hrt
  have hσt0 : σ t0 = t0 := hσ t0 ht0b
  have hσr : σ r = r := by
    rw [map_mul, hσt0] at hσrt
    exact mul_right_cancel₀ ht0 hσrt
  rw [hx, map_add, hσr, hσs]

theorem IsUni.P_props (hU : IsUni h N) (hN : IsNilpotent N) :
    st h (N * st h N) = N * st h N ∧ IsNilpotent (N * st h N) ∧
      N * (N * st h N) = (N * st h N) * N := by
  refine ⟨by rw [st_mul, st_st], ?_, ?_⟩
  · exact (Commute.isNilpotent_mul_right (show Commute N (st h N) from hU.comm) hN)
  · calc N * (N * st h N) = N * (st h N * N) := by rw [hU.comm]
      _ = (N * st h N) * N := by rw [mul_assoc]

theorem IsUni.P_ne_zero (hU : IsUni h N) (hNN : N * N ≠ 0) : N * st h N ≠ 0 := by
  intro h0
  apply hNN
  have h1 := hU.eq2
  rw [h0, add_zero] at h1
  have : st h N = -N := eq_neg_of_add_eq_zero_right h1
  rw [this, mul_neg, neg_eq_zero] at h0
  exact h0

theorem KData.cj_P (hK : KData h N A σ) : cj h A σ (N * st h N) = N * st h N := by
  rw [cj_mul hK.hA, hK.fixN, ← cj_st, hK.fixN]

theorem KData.sigma_of_cayley (hK : KData h N A σ) (h2 : (2 : K) ≠ 0) (hU : IsUni h N)
    (hN : IsNilpotent N) (hNN : N * N ≠ 0)
    (hC : ∀ a : K, h.bar a = -a → ∀ X : Matrix (Fin n) (Fin n) K, IsNilpotent X → IsUni h X →
      N * X = X * N → (1 + X) * (1 - a • (N * st h N)) = 1 + a • (N * st h N) →
        cj h A σ X = X) (x : K) : σ x = x := by
  refine sigma_id_of_traceZero (h := h) h2 (fun a ha => ?_) x
  obtain ⟨hPs, hPn, hPc⟩ := hU.P_props hN
  have hP0 := hU.P_ne_zero hNN
  set P := N * st h N with hPdef
  have hsk : st h (a • P) = -(a • P) := by rw [st_smul, hPs, ha, neg_smul]
  have hYc : N * (a • P) = (a • P) * N := by rw [Matrix.mul_smul, Matrix.smul_mul, hPc]
  obtain ⟨X, hXn, hXu, hXc, hXr⟩ := exists_cayley (hPn.smul a) hsk hYc
  have hfix := hC a ha X hXn hXu hXc hXr
  have hr2 := congrArg (cj h A σ) hXr
  rw [cj_mul hK.hA, cj_add, cj_sub, cj_one hK.hA', cj_smul, hK.cj_P, hfix, cj_add, cj_one hK.hA',
    cj_smul, hK.cj_P] at hr2
  set b := σ a with hb
  have hcomm : (1 - b • P) * (1 - a • P) = (1 - a • P) * (1 - b • P) := by
    simp only [mul_sub, sub_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub,
      smul_smul]
    module
  have key : ((b - a) * 2) • P = 0 := by
    have e1 : (1 + b • P) * (1 - a • P) = (1 + a • P) * (1 - b • P) := by
      calc (1 + b • P) * (1 - a • P) = ((1 + X) * (1 - b • P)) * (1 - a • P) := by rw [hr2]
        _ = (1 + X) * ((1 - b • P) * (1 - a • P)) := by rw [mul_assoc]
        _ = (1 + X) * ((1 - a • P) * (1 - b • P)) := by rw [hcomm]
        _ = ((1 + X) * (1 - a • P)) * (1 - b • P) := by rw [mul_assoc]
        _ = (1 + a • P) * (1 - b • P) := by rw [hXr]
    simp only [mul_sub, sub_mul, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      smul_sub, smul_add, smul_smul] at e1
    linear_combination (norm := module) e1
  rcases smul_eq_zero.1 key with h0 | h0
  · rcases mul_eq_zero.1 h0 with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 h2
  · exact absurd h0 hP0

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part6

section Part7

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} {h : UnitaryFieldData p f K}
variable {N A : Matrix (Fin n) (Fin n) K} {σ : K ≃+* K}

theorem NN_ne_zero_of_ker_small (hn : 3 ≤ n) {w0 : Fin n → K} (hw0 : w0 ≠ 0)
    (hker : ∀ v, N *ᵥ v = 0 → ∃ e : K, v = e • w0) : N * N ≠ 0 := by
  intro hNN
  have hrange : LinearMap.range N.mulVecLin ≤ LinearMap.ker N.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hNN,
      Matrix.zero_mulVec]
  have hk : LinearMap.ker N.mulVecLin ≤ Submodule.span K {w0} := by
    intro v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
    obtain ⟨e, rfl⟩ := hker v hv
    exact Submodule.smul_mem _ e (Submodule.mem_span_singleton_self w0)
  have h1 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [Module.finrank_fin_fun] at h1
  have h2 : Module.finrank K (LinearMap.ker N.mulVecLin) ≤ 1 := by
    calc Module.finrank K (LinearMap.ker N.mulVecLin) ≤ Module.finrank K (Submodule.span K {w0}) :=
          Submodule.finrank_mono hk
      _ = 1 := finrank_span_singleton hw0
  have h3 : Module.finrank K (LinearMap.range N.mulVecLin) ≤
      Module.finrank K (LinearMap.ker N.mulVecLin) := Submodule.finrank_mono hrange
  omega

theorem KData.nil_of_id [NeZero n] (hK : KData h N A σ) (hσ : ∀ x, σ x = x) (hU : IsUni h N)
    (hN : IsNilpotent N) (hN0 : N ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ IsNilpotent (A - c • (1 : Matrix (Fin n) (Fin n) K)) := by
  have hth : ∀ x, th A σ x = A *ᵥ x := fun x => by
    unfold th; congr 1; funext i; exact hσ _
  have hmap : ∀ M : Matrix (Fin n) (Fin n) K, M.map σ = M := fun M => by
    ext i j; simp [hσ]
  have hAN : A * N = N * A := by
    have e := hK.fixN
    unfold cj at e
    rw [hmap] at e
    calc A * N = A * N * (st h A * A) := by rw [hK.hA, mul_one]
      _ = (A * N * st h A) * A := by simp only [mul_assoc]
      _ = N * A := by rw [e]
  obtain ⟨w0, hw0, hw0W⟩ := exists_ne_zero_mem_Wsp hN hN0
  obtain ⟨c, hc0, hcw, hct⟩ := hK.th_eigen hw0W hw0
  obtain ⟨t0, ht0, ht0b⟩ := exists_traceZero_ne_zero h
  have hcc : c * h.bar c = 1 := by
    have := hct t0 ht0b
    rw [hσ] at this
    have h2 : t0 * (c * h.bar c) = t0 * 1 := by rw [mul_one]; exact this
    exact mul_left_cancel₀ ht0 h2
  rw [hth] at hcw
  set B : Matrix (Fin n) (Fin n) K := A - c • 1 with hB
  have hBw : B *ᵥ w0 = 0 := by
    rw [hB, Matrix.sub_mulVec, hcw, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hBv : ∀ v, N *ᵥ v = 0 → ∃ κ : K, B *ᵥ v = κ • w0 := by
    intro v hv
    obtain ⟨e, he⟩ := hK.eichler hw0W hw0 (by rw [hth]; exact hcw) hv
    rw [hth] at he
    refine ⟨c * e, ?_⟩
    have h1 : A *ᵥ v = c • v + (c * e) • w0 := by
      have := congrArg (fun y => c • y) he
      simp only [smul_smul, hcc, one_smul, smul_add] at this
      exact this
    rw [hB, Matrix.sub_mulVec, h1, Matrix.smul_mulVec, Matrix.one_mulVec]
    abel
  have hBN : B * N = N * B := by
    rw [hB, sub_mul, mul_sub, hAN, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have key : ∀ j : ℕ, ∀ x, N ^ j *ᵥ x = 0 → B ^ (2 * j) *ᵥ x = 0 := by
    intro j
    induction j with
    | zero =>
      intro x hx
      simpa using hx
    | succ j ih =>
      intro x hx
      have h1 : N ^ j *ᵥ (N *ᵥ x) = 0 := by rw [Matrix.mulVec_mulVec, ← pow_succ]; exact hx
      have h2 := ih _ h1
      have h3 : N *ᵥ (B ^ (2 * j) *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, ← ((Commute.pow_left (show Commute B N from hBN) (2 * j)).eq),
          ← Matrix.mulVec_mulVec]
        exact h2
      obtain ⟨κ, hκ⟩ := hBv _ h3
      have : B ^ (2 * (j + 1)) = B * (B * B ^ (2 * j)) := by
        rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ', pow_succ']
      rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hκ, Matrix.mulVec_smul, hBw,
        smul_zero]
  refine ⟨c, hc0, ?_⟩
  obtain ⟨m, hm⟩ := hN
  refine ⟨2 * m, ?_⟩
  apply matrix_eq_zero_of_mulVec
  intro v
  exact key m v (by rw [hm]; simp)

@[expose] def CayFix (h : UnitaryFieldData p f K) (N A : Matrix (Fin n) (Fin n) K) (σ : K ≃+* K) : Prop :=
  ∀ a : K, h.bar a = -a → ∀ X : Matrix (Fin n) (Fin n) K, IsNilpotent X → IsUni h X →
    N * X = X * N → (1 + X) * (1 - a • (N * st h N)) = 1 + a • (N * st h N) → cj h A σ X = X

theorem KData.key [NeZero n] (hK : KData h N A σ) (hn : 3 ≤ n) (h2 : (2 : K) ≠ 0)
    (hU : IsUni h N) (hN : IsNilpotent N) (hN0 : N ≠ 0) (hC : CayFix h N A σ) :
    (∀ x, σ x = x) ∧ ∃ c : K, c ≠ 0 ∧ IsNilpotent (A - c • (1 : Matrix (Fin n) (Fin n) K)) := by
  have hσ : ∀ x, σ x = x := by
    obtain ⟨w0, hw0, hw0W⟩ := exists_ne_zero_mem_Wsp hN hN0
    by_cases hv : ∃ v, N *ᵥ v = 0 ∧ ∀ e : K, v ≠ e • w0
    · obtain ⟨v, hv0, hvn⟩ := hv
      exact hK.sigma_of_exists hw0W hw0 hv0 hvn
    · push Not at hv
      exact hK.sigma_of_cayley h2 hU hN (NN_ne_zero_of_ker_small hn hw0 hv) hC
  exact ⟨hσ, hK.nil_of_id hσ hU hN hN0⟩

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part7

section Part8

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

abbrev Cm (n : ℕ) (K : Type) [Field K] : Matrix (Fin n) (Fin n) K :=
  ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem Cm_eq : Cm n K = 1 := rfl

theorem mem_gramSU_one {g : GL (Fin n) K} :
    g ∈ gramSU h (Cm n K) ↔ st h (g : Matrix (Fin n) (Fin n) K) * g = 1 ∧
      (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [mem_gramSU, Cm_eq, Matrix.mul_one]; rfl

variable {h}

theorem SU_st_mul (g : gramSU h (Cm n K)) :
    st h ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
  ((mem_gramSU_one h).1 g.2).1

theorem SU_mul_st (g : gramSU h (Cm n K)) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * st h ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
  mul_eq_one_comm.1 (SU_st_mul g)

theorem SU_det (g : gramSU h (Cm n K)) : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
  ((mem_gramSU_one h).1 g.2).2

theorem coe_inv_SU (g : gramSU h (Cm n K)) :
    (((g : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      st h ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  Units.inv_eq_of_mul_eq_one_right (SU_mul_st g)

theorem det_one_add_nilpotent (h : UnitaryFieldData p f K) [NeZero n] {X : Matrix (Fin n) (Fin n) K}
    (hX : IsNilpotent X) : (1 + X).det = 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have := det_one_add_smul_of_isNilpotent (p := p) hX 1
  rwa [one_smul] at this

@[expose] noncomputable def mkSU [NeZero n] {X : Matrix (Fin n) (Fin n) K} (hX : IsNilpotent X) (hU : IsUni h X) :
    gramSU h (Cm n K) :=
  ⟨⟨1 + X, 1 + st h X, hU.swap, hU⟩, (mem_gramSU_one h).2 ⟨by
    show st h (1 + X) * (1 + X) = 1
    rw [st_add, st_one]; exact hU, det_one_add_nilpotent h hX⟩⟩

theorem coe_mkSU [NeZero n] {X : Matrix (Fin n) (Fin n) K} (hX : IsNilpotent X) (hU : IsUni h X) :
    (((mkSU hX hU : gramSU h (Cm n K)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + X := rfl

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part8

section Part9

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} {h : UnitaryFieldData p f K}

theorem mk_eq_scalar {g g' : gramSU h (Cm n K)}
    (hg : (g : primeFormP h (Cm n K)) = (g' : primeFormP h (Cm n K))) :
    ∃ c : K, ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨c, -, -, hc⟩ := QuotientGroup.eq.1 hg
  refine ⟨(c : K), ?_⟩
  have h2 : (g' : GL (Fin n) K) = (g : GL (Fin n) K) * ((g⁻¹ * g' : gramSU h (Cm n K)) : GL (Fin n) K) := by
    simp
  rw [h2, hc, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← smul_one_eq_diagonal, mul_smul_comm, mul_one]

theorem mk_eq_one_of_scalar [NeZero n] (s : gramSU h (Cm n K)) (c : K)
    (hs : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) :
    (s : primeFormP h (Cm n K)) = 1 := by
  rw [QuotientGroup.eq_one_iff]
  have h1 := SU_st_mul s
  rw [hs] at h1
  have hnorm : c * h.bar c = 1 := by
    have e : st h (c • (1 : Matrix (Fin n) (Fin n) K)) = h.bar c • 1 := by
      rw [st_smul, st_one]
    rw [e, Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul] at h1
    have := congrFun (congrFun h1 0) 0
    simpa [mul_comm] using this
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hnorm
  have hdet := SU_det s
  rw [hs, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  refine ⟨Units.mk0 c hc0, ?_, ?_, ?_⟩
  · exact hnorm
  · apply Units.ext; simpa using hdet
  · apply Units.ext
    rw [hs, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← smul_one_eq_diagonal]
    rfl

theorem commute_lift [NeZero n] {u σ : gramSU h (Cm n K)} {N : Matrix (Fin n) (Fin n) K} (hN : IsNilpotent N)
    (hu : ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + N)
    (hc : (σ : primeFormP h (Cm n K)) * (u : primeFormP h (Cm n K)) =
      (u : primeFormP h (Cm n K)) * (σ : primeFormP h (Cm n K))) :
    N * ((σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N := by
  have hc' : ((σ * u : gramSU h (Cm n K)) : primeFormP h (Cm n K)) =
      ((u * σ : gramSU h (Cm n K)) : primeFormP h (Cm n K)) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact hc
  obtain ⟨c, hcc⟩ := mk_eq_scalar hc'
  simp only [Subgroup.coe_mul, Units.val_mul, hu] at hcc
  set M := ((σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hMs : st h M * M = 1 := SU_st_mul σ
  have hsM : M * st h M = 1 := SU_mul_st σ
  have key : c • (1 + N) = 1 + st h M * N * M := by
    have e1 : st h M * ((1 + N) * M) = c • (1 + N) := by
      rw [hcc, Matrix.mul_smul, ← mul_assoc, hMs, one_mul]
    rw [← e1]
    calc st h M * ((1 + N) * M) = st h M * M + st h M * N * M := by noncomm_ring
      _ = 1 + st h M * N * M := by rw [hMs]
  have hnil : IsNilpotent (st h M * N * M) := isNilpotent_conj hMs hsM hN
  have hc1 : c = 1 := eq_one_of_smul_one_add_nilpotent hN hnil key
  rw [hc1, one_smul] at key
  have key2 := add_left_cancel key
  calc N * M = M * (st h M * N * M) := by
        rw [← mul_assoc, ← mul_assoc, hsM, one_mul]
    _ = M * N := by rw [← key2]

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part9

section Part10

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} {h : UnitaryFieldData p f K}

theorem eq_one_of_pow_char_eq_one [Fact p.Prime] [CharP K p] {x : K} (hx : x ^ p = 1) : x = 1 := by
  have h1 : (x - 1) ^ p = 0 := by rw [sub_pow_char, hx, one_pow, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 h1)

theorem exists_unipotent_lift [NeZero n] (g : primeFormP h (Cm n K)) (hg : orderOf g = p) :
    ∃ (u : gramSU h (Cm n K)) (N : Matrix (Fin n) (Fin n) K),
      (u : primeFormP h (Cm n K)) = g ∧ IsNilpotent N ∧ N ≠ 0 ∧ IsUni h N ∧
        ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + N := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have : Finite K := h.finite
  obtain ⟨s0, rfl⟩ := QuotientGroup.mk_surjective g
  have hpow : ((s0 ^ p : gramSU h (Cm n K)) : primeFormP h (Cm n K)) = 1 := by
    rw [QuotientGroup.mk_pow]
    have := pow_orderOf_eq_one (s0 : primeFormP h (Cm n K))
    rwa [hg] at this
  obtain ⟨c, hcN, hcn, hc⟩ := (QuotientGroup.eq_one_iff _).1 hpow
  set S : Matrix (Fin n) (Fin n) K := ((s0 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hS
  have hSst : st h S * S = 1 := SU_st_mul s0
  have hSp : S ^ p = (c : K) • 1 := by
    have := congrArg (fun z : GL (Fin n) K => (z : Matrix (Fin n) (Fin n) K)) hc
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← smul_one_eq_diagonal] at this
    exact this
  obtain ⟨d, hd⟩ : ∃ d : K, d ^ p = (c : K) := by
    have hsurj : Function.Surjective (frobenius K p) :=
      Finite.surjective_of_injective (frobenius_inj K p)
    obtain ⟨d, hd⟩ := hsurj (c : K)
    exact ⟨d, by simpa [frobenius_def] using hd⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow (Fact.out : p.Prime).ne_zero] at hd
    exact c.ne_zero hd.symm
  have hdn : d ^ n = 1 := by
    apply eq_one_of_pow_char_eq_one (p := p)
    rw [← pow_mul, mul_comm, pow_mul, hd, ← Units.val_pow_eq_pow_val, hcn, Units.val_one]
  have hdN : d * h.bar d = 1 := by
    apply eq_one_of_pow_char_eq_one (p := p)
    rw [mul_pow, ← map_pow, hd]
    exact hcN
  set N0 : Matrix (Fin n) (Fin n) K := S - d • 1 with hN0def
  have hN0 : IsNilpotent N0 := by
    refine ⟨p, ?_⟩
    rw [hN0def, sub_pow_char_of_commute p ((Commute.one_right _).smul_right d), hSp, ← hd,
      ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one, map_pow, sub_self]
  set N : Matrix (Fin n) (Fin n) K := d⁻¹ • N0 with hNdef
  have hNnil : IsNilpotent N := hN0.smul _
  have hmat : (1 : Matrix (Fin n) (Fin n) K) + N = d⁻¹ • S := by
    rw [hNdef, hN0def, smul_sub, smul_smul, inv_mul_cancel₀ hd0, one_smul]; abel
  have hbd : h.bar d⁻¹ * d⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, mul_comm, hdN, inv_one]
  have hUN : IsUni h N := by
    unfold IsUni
    have e : 1 + st h N = st h (d⁻¹ • S) := by rw [← hmat, st_add, st_one]
    rw [e, hmat, st_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hSst, hbd, one_smul]
  refine ⟨mkSU hNnil hUN, N, ?_, hNnil, ?_, hUN, rfl⟩
  · refine Eq.symm ?_
    rw [QuotientGroup.eq]
    refine ⟨Units.mk0 d⁻¹ (inv_ne_zero hd0), ?_, ?_, ?_⟩
    · show d⁻¹ * h.bar d⁻¹ = 1
      rw [map_inv₀, ← mul_inv, hdN, inv_one]
    · apply Units.ext
      simp [inv_pow, hdn]
    · apply Units.ext
      rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv, coe_inv_SU, coe_mkSU, hmat, ← hS, Matrix.mul_smul, hSst,
        GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← smul_one_eq_diagonal]
      rfl
  · intro hN
    have hu1 : mkSU hNnil hUN = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [coe_mkSU, hN]; simp
    have hmk : ((mkSU hNnil hUN : gramSU h (Cm n K)) : primeFormP h (Cm n K)) = (s0 : primeFormP h (Cm n K)) := by
      refine Eq.symm ?_
      rw [QuotientGroup.eq]
      refine ⟨Units.mk0 d⁻¹ (inv_ne_zero hd0), ?_, ?_, ?_⟩
      · show d⁻¹ * h.bar d⁻¹ = 1
        rw [map_inv₀, ← mul_inv, hdN, inv_one]
      · apply Units.ext
        simp [inv_pow, hdn]
      · apply Units.ext
        rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv, coe_inv_SU, coe_mkSU, hmat, ← hS, Matrix.mul_smul, hSst,
          GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← smul_one_eq_diagonal]
        rfl
    rw [hu1, QuotientGroup.mk_one] at hmk
    rw [← hmk, orderOf_one] at hg
    exact (Fact.out : p.Prime).one_lt.ne hg

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part10

section Part11

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} {h : UnitaryFieldData p f K}
  {N : Matrix (Fin n) (Fin n) K}

theorem Wsp_mulVec_mem {M : Matrix (Fin n) (Fin n) K} (hMN : N * M = M * N) {w : Fin n → K}
    (hw : w ∈ Wsp N) : M *ᵥ w ∈ Wsp N := by
  obtain ⟨h0, v, rfl⟩ := mem_Wsp.1 hw
  rw [mem_Wsp]
  refine ⟨?_, M *ᵥ v, ?_⟩
  · rw [Matrix.mulVec_mulVec, hMN, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  · rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMN]

theorem comm_inv {M Mi : Matrix (Fin n) (Fin n) K} (hMN : N * M = M * N)
    (hMi : M * Mi = 1) (hiM : Mi * M = 1) : N * Mi = Mi * N := by
  calc N * Mi = (Mi * M) * N * Mi := by rw [hiM, one_mul]
    _ = Mi * (M * N) * Mi := by simp only [mul_assoc]
    _ = Mi * (N * M) * Mi := by rw [hMN]
    _ = Mi * N * (M * Mi) := by simp only [mul_assoc]
    _ = Mi * N := by rw [hMi, mul_one]

theorem Flag.conj {X M Mi : Matrix (Fin n) (Fin n) K} (hX : Flag N X) (hMN : N * M = M * N)
    (hMi : M * Mi = 1) (hiM : Mi * M = 1) : Flag N (M * X * Mi) := by
  have hMiN : N * Mi = Mi * N := comm_inv hMN hMi hiM
  have cM : ∀ y, N *ᵥ (M *ᵥ y) = M *ᵥ (N *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMN]
  have cMi : ∀ y, N *ᵥ (Mi *ᵥ y) = Mi *ᵥ (N *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMiN]
  refine ⟨fun x => ?_, fun x hx => ?_, fun w hw => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cM, hX.1, Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    refine Wsp_mulVec_mem hMN (hX.2.1 _ ?_)
    rw [cMi, hx, Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have : Mi *ᵥ w ∈ Wsp N := Wsp_mulVec_mem hMiN hw
    rw [hX.2.2 _ this, Matrix.mulVec_zero]

abbrev smat (s : gramSU h (Cm n K)) : Matrix (Fin n) (Fin n) K :=
  ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

variable (h) in
@[expose] def GenSet (N : Matrix (Fin n) (Fin n) K) : Set (primeFormP h (Cm n K)) :=
  {q | ∃ s : gramSU h (Cm n K), (s : primeFormP h (Cm n K)) = q ∧ Flag N (smat s - 1) ∧
    N * smat s = smat s * N}

theorem st_eq_of_flag {X S Mi : Matrix (Fin n) (Fin n) K} (hX : Flag N X) (hS : S = 1 + X)
    (h2 : Mi * S = 1) : Mi = 1 - X + X * X := by
  have hR : S * (1 - X + X * X) = 1 := by
    have : S * (1 - X + X * X) = 1 + X * X * X := by rw [hS]; noncomm_ring
    rw [this, hX.cube, add_zero]
  calc Mi = Mi * (S * (1 - X + X * X)) := by rw [hR, mul_one]
    _ = (Mi * S) * (1 - X + X * X) := by rw [mul_assoc]
    _ = 1 - X + X * X := by rw [h2, one_mul]

theorem GenSet_comm {u : gramSU h (Cm n K)} (hu : smat u = 1 + N) {q : primeFormP h (Cm n K)}
    (hq : q ∈ GenSet h N) : (u : primeFormP h (Cm n K)) * q = q * (u : primeFormP h (Cm n K)) := by
  obtain ⟨s, rfl, -, hs⟩ := hq
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  change smat u * smat s = smat s * smat u
  rw [hu, add_mul, mul_add, one_mul, mul_one, hs]

theorem smat_conj (σ s : gramSU h (Cm n K)) :
    smat (σ * s * σ⁻¹) = smat σ * smat s * st h (smat σ) := by
  change ((σ * s * σ⁻¹ : gramSU h (Cm n K)) : GL (Fin n) K).val = _
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Subgroup.coe_inv,
    coe_inv_SU]

theorem GenSet_conj {σ : gramSU h (Cm n K)} (hσ : N * smat σ = smat σ * N)
    {q : primeFormP h (Cm n K)} (hq : q ∈ GenSet h N) :
    (σ : primeFormP h (Cm n K)) * q * (σ : primeFormP h (Cm n K))⁻¹ ∈ GenSet h N := by
  obtain ⟨s, rfl, hf, hs⟩ := hq
  refine ⟨σ * s * σ⁻¹, ?_, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  · have hmat : smat (σ * s * σ⁻¹) - 1 = smat σ * (smat s - 1) * st h (smat σ) := by
      rw [smat_conj, mul_sub, sub_mul, mul_one, SU_mul_st]
    rw [hmat]
    exact hf.conj hσ (SU_mul_st σ) (SU_st_mul σ)
  · rw [smat_conj]
    have hMiN : N * st h (smat σ) = st h (smat σ) * N := comm_inv hσ (SU_mul_st σ) (SU_st_mul σ)
    calc N * (smat σ * smat s * st h (smat σ))
        = (N * smat σ) * smat s * st h (smat σ) := by simp only [mul_assoc]
      _ = smat σ * (N * smat s) * st h (smat σ) := by rw [hσ]; simp only [mul_assoc]
      _ = smat σ * (smat s * N) * st h (smat σ) := by rw [hs]
      _ = smat σ * smat s * (N * st h (smat σ)) := by simp only [mul_assoc]
      _ = smat σ * smat s * (st h (smat σ) * N) := by rw [hMiN]
      _ = _ := by simp only [mul_assoc]

theorem GenSet_p3 [NeZero n] (hp2 : p ≠ 2) {q : primeFormP h (Cm n K)} (hq : q ∈ GenSet h N)
    {q' : primeFormP h (Cm n K)} (hq' : q' ∈ GenSet h N) : (q' * q⁻¹) ^ p = 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  obtain ⟨s, rfl, hf, -⟩ := hq
  obtain ⟨s', rfl, hf', -⟩ := hq'
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
  have key : (s' * s⁻¹ : gramSU h (Cm n K)) ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    have hmat : smat (s' * s⁻¹) = smat s' * st h (smat s) := by
      change ((s' * s⁻¹ : gramSU h (Cm n K)) : GL (Fin n) K).val = _
      rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv, coe_inv_SU]
    have hMi : st h (smat s) = 1 - (smat s - 1) + (smat s - 1) * (smat s - 1) :=
      st_eq_of_flag hf (S := smat s) (by abel) (SU_st_mul s)
    set X := smat s - 1 with hX
    set X' := smat s' - 1 with hX'
    have hZ : Flag N (X' + (-X + X * X) + X' * (-X + X * X)) :=
      (hf'.add (hf.neg.add (hf.mul hf))).add (hf'.mul (hf.neg.add (hf.mul hf)))
    have hprod : smat (s' * s⁻¹) = 1 + (X' + (-X + X * X) + X' * (-X + X * X)) := by
      rw [hmat, hMi]
      have : smat s' = 1 + X' := by rw [hX']; abel
      rw [this]; noncomm_ring
    set Z := X' + (-X + X * X) + X' * (-X + X * X)
    have hZ3 : Z ^ 3 = 0 := by rw [pow_succ, pow_two, hZ.cube]
    have hZp : Z ^ p = 0 := pow_eq_zero_of_le (by have := h.prime.two_le; omega) hZ3
    change (((s' * s⁻¹ : gramSU h (Cm n K)) ^ p : gramSU h (Cm n K)) : GL (Fin n) K).val = 1
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    change (smat (s' * s⁻¹)) ^ p = 1
    rw [hprod, add_pow_char_of_commute (R := Matrix (Fin n) (Fin n) K) p (Commute.one_left Z), hZp,
      one_pow, add_zero]
  rw [key, QuotientGroup.mk_one]

theorem Tm_mem_GenSet (hU : IsUni h N) {w : Fin n → K} (hw : w ∈ Wsp N) {t : K}
    (ht : h.bar t = -t) [NeZero n] :
    ((mkSU (Tm_flag hU hw t).isNilpotent (Tm_isUni hU hw ht) : gramSU h (Cm n K)) :
      primeFormP h (Cm n K)) ∈ GenSet h N := by
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [show smat (mkSU (Tm_flag hU hw t).isNilpotent (Tm_isUni hU hw ht)) = 1 + Tm h w t from rfl,
      add_sub_cancel_left]
    exact Tm_flag hU hw t
  · rw [show smat (mkSU (Tm_flag hU hw t).isNilpotent (Tm_isUni hU hw ht)) = 1 + Tm h w t from rfl,
      mul_add, add_mul, mul_one, one_mul, (Tm_comm hU hw t).1, (Tm_comm hU hw t).2]

theorem Em_mem_GenSet (h2 : (2 : K) ≠ 0) (hU : IsUni h N) {w v : Fin n → K} (hw : w ∈ Wsp N)
    (hv : N *ᵥ v = 0) [NeZero n] :
    ((mkSU (Em_flag hU hw hv).isNilpotent (Em_isUni h2 hU hw hv) : gramSU h (Cm n K)) :
      primeFormP h (Cm n K)) ∈ GenSet h N := by
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [show smat (mkSU (Em_flag hU hw hv).isNilpotent (Em_isUni h2 hU hw hv)) = 1 + Em h v w from rfl,
      add_sub_cancel_left]
    exact Em_flag hU hw hv
  · rw [show smat (mkSU (Em_flag hU hw hv).isNilpotent (Em_isUni h2 hU hw hv)) = 1 + Em h v w from rfl,
      mul_add, add_mul, mul_one, one_mul, (Em_comm hU hw hv).1, (Em_comm hU hw hv).2]

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part11

section Part12

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} {h : UnitaryFieldData p f K}
  {N : Matrix (Fin n) (Fin n) K}

theorem two_ne_zero_of_char (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have : CharP K p := h.charP
  intro h0
  have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
  rw [CharP.cast_eq_zero_iff K p] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)

theorem cj_of_commute {A X : Matrix (Fin n) (Fin n) K} (hA' : A * st h A = 1)
    (hAX : A * X = X * A) : cj h A (1 : K ≃+* K) X = X := by
  unfold cj
  have : X.map (1 : K ≃+* K) = X := by ext i j; rfl
  rw [this, hAX, mul_assoc, hA', mul_one]

theorem pow_eq_one_of_scalar (h : UnitaryFieldData p f K) [NeZero n] (hp2 : p ≠ 2) {M : Matrix (Fin n) (Fin n) K}
    (hM : ∃ c : K, c ≠ 0 ∧ IsNilpotent (M - c • (1 : Matrix (Fin n) (Fin n) K))) :
    ∃ (e : ℕ) (c : K), M ^ p ^ e = c • 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  obtain ⟨c, -, hB⟩ := hM
  obtain ⟨e, he⟩ := add_smul_one_pow_prime_pow (p := p) hB c
  refine ⟨e, c ^ p ^ e, ?_⟩
  rw [← he, add_sub_cancel]

theorem uniq_inner [NeZero n] (hn : 3 ≤ n) (hp2 : p ≠ 2) {u : gramSU h (Cm n K)}
    (hN : IsNilpotent N) (hN0 : N ≠ 0) (hU : IsUni h N) (hu : smat u = 1 + N)
    (σ : gramSU h (Cm n K))
    (hσu : (σ : primeFormP h (Cm n K)) * (u : primeFormP h (Cm n K)) =
      (u : primeFormP h (Cm n K)) * (σ : primeFormP h (Cm n K)))
    (hcop : (orderOf (σ : primeFormP h (Cm n K))).Coprime p)
    (hσGen : ∀ q ∈ GenSet h N, (σ : primeFormP h (Cm n K)) * q = q * (σ : primeFormP h (Cm n K))) :
    (σ : primeFormP h (Cm n K)) = 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have h2 := two_ne_zero_of_char h hp2
  have hσN : N * smat σ = smat σ * N := commute_lift hN hu hσu
  have hK : KData h N (smat σ) (1 : K ≃+* K) := by
    refine ⟨SU_st_mul σ, SU_mul_st σ, cj_of_commute (SU_mul_st σ) hσN.symm, ?_, ?_⟩
    · intro w hw t ht
      apply cj_of_commute (SU_mul_st σ)
      have hq := Tm_mem_GenSet hU hw ht
      have := commute_lift (u := mkSU (Tm_flag hU hw t).isNilpotent (Tm_isUni hU hw ht)) (σ := σ)
        (Tm_flag hU hw t).isNilpotent rfl (hσGen _ hq)
      exact this.symm
    · intro w hw v hv
      apply cj_of_commute (SU_mul_st σ)
      have hq := Em_mem_GenSet h2 hU hw hv
      have := commute_lift (u := mkSU (Em_flag hU hw hv).isNilpotent (Em_isUni h2 hU hw hv))
        (σ := σ) (Em_flag hU hw hv).isNilpotent rfl (hσGen _ hq)
      exact this.symm
  obtain ⟨c, hc0, hcn⟩ := hK.nil_of_id (fun _ => rfl) hU hN hN0
  obtain ⟨e, c', hpow⟩ := pow_eq_one_of_scalar h hp2 ⟨c, hc0, hcn⟩
  have hs : (((σ ^ p ^ e : gramSU h (Cm n K)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c' • 1 := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    exact hpow
  have h1 := mk_eq_one_of_scalar _ _ hs
  rw [QuotientGroup.mk_pow] at h1
  have hdvd : orderOf (σ : primeFormP h (Cm n K)) ∣ p ^ e := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (σ : primeFormP h (Cm n K)) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right e hcop) hdvd
  exact orderOf_eq_one_iff.1 h3

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part12

section Part13

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} {h : UnitaryFieldData p f K}
  {N : Matrix (Fin n) (Fin n) K}

theorem unit_st_mul (A : primeFormUnitary h (Cm n K)) :
    st h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  have := mem_primeFormUnitary.mp A.2
  have h1 : st h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := this
  rwa [Matrix.mul_one] at h1

theorem unit_mul_st (A : primeFormUnitary h (Cm n K)) :
    ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * st h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
  mul_eq_one_comm.1 (unit_st_mul A)

theorem coe_inv_unit (A : primeFormUnitary h (Cm n K)) :
    (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      st h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  Units.inv_eq_of_mul_eq_one_right (unit_mul_st A)

theorem apply_mk (hC : IsPrimeFormGram (1 : GL (Fin n) K)) (A : primeFormUnitary h (Cm n K))
    (φ : K ≃+* K) (s : gramSU h (Cm n K)) :
    ∃ s' : gramSU h (Cm n K),
      (primeFormConjHom h (Cm n K) A * primeFormFieldHom h hC φ) (s : primeFormP h (Cm n K)) =
        (s' : primeFormP h (Cm n K)) ∧
      smat s' = cj h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) φ (smat s) := by
  refine ⟨⟨(A : GL (Fin n) K) * glAut φ (s : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹,
    conj_mem_gramSU h _ A.2 (glAut_mem_gramSU h hC φ s.2)⟩, ?_, ?_⟩
  · rw [MulAut.mul_apply]
    change primeFormConjAut h _ A (primeFormFieldAut h hC φ (s : primeFormP h _)) = _
    rw [primeFormFieldAut_mk, primeFormConjAut_mk]
    rfl
  · change ((A : GL (Fin n) K) * glAut φ (s : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ : GL (Fin n) K).val = _
    rw [Units.val_mul, Units.val_mul, coe_glAut, coe_inv_unit A]
    rfl

theorem fix_cj [NeZero n] (hC : IsPrimeFormGram (1 : GL (Fin n) K)) (A : primeFormUnitary h (Cm n K))
    (φ : K ≃+* K) {s : gramSU h (Cm n K)} {X : Matrix (Fin n) (Fin n) K} (hX : IsNilpotent X)
    (hs : smat s = 1 + X)
    (hfix : (primeFormConjHom h (Cm n K) A * primeFormFieldHom h hC φ) (s : primeFormP h (Cm n K)) =
      (s : primeFormP h (Cm n K))) :
    cj h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) φ X = X := by
  obtain ⟨s', h1, h2⟩ := apply_mk hC A φ s
  rw [hfix] at h1
  obtain ⟨c, hc0⟩ := mk_eq_scalar h1
  have hc : smat s' = c • smat s := hc0
  rw [h2, hs, cj_add, cj_one (unit_mul_st A)] at hc
  have hnil : IsNilpotent (cj h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) φ X) :=
    cj_isNilpotent (unit_st_mul A) (unit_mul_st A) hX
  have hc1 : c = 1 := eq_one_of_smul_one_add_nilpotent hX hnil hc.symm
  rw [hc1, one_smul] at hc
  exact add_left_cancel hc

theorem conjHom_scalar (A : primeFormUnitary h (Cm n K)) (c : K)
    (hA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) :
    primeFormConjHom h (Cm n K) A = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk]
  change _ = (g : primeFormP h (Cm n K))
  congr 1
  apply Subtype.ext
  change (A : GL (Fin n) K) * (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = g
  have : (A : GL (Fin n) K) * (g : GL (Fin n) K) = (g : GL (Fin n) K) * (A : GL (Fin n) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hA, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  rw [this, mul_inv_cancel_right]

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part13

section Part14

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} {h : UnitaryFieldData p f K}
  {N : Matrix (Fin n) (Fin n) K}

theorem uniq_out [NeZero n] (hn : 3 ≤ n) (hp2 : p ≠ 2) {u : gramSU h (Cm n K)}
    (hN : IsNilpotent N) (hN0 : N ≠ 0) (hU : IsUni h N) (hu : smat u = 1 + N)
    (α : MulAut (primeFormP h (Cm n K))) (hcop : (orderOf α).Coprime p)
    (hfix : ∀ q, q * (u : primeFormP h (Cm n K)) = (u : primeFormP h (Cm n K)) * q → α q = q) :
    α = 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have h2 := two_ne_zero_of_char h hp2
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hq : ¬(n = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2'⟩
    have hf0 : f ≠ 0 := by have := h.one_le; omega
    have : p ∣ 2 := h2' ▸ dvd_pow_self p hf0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)
  obtain ⟨-, -, -, -, hex, -⟩ := unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨φ, ⟨A, hα⟩, -⟩ := hex α
  have fixmk : ∀ s : gramSU h (Cm n K),
      (s : primeFormP h (Cm n K)) * (u : primeFormP h (Cm n K)) =
        (u : primeFormP h (Cm n K)) * (s : primeFormP h (Cm n K)) →
      (primeFormConjHom h (Cm n K) A * primeFormFieldHom h hC φ) (s : primeFormP h (Cm n K)) =
        (s : primeFormP h (Cm n K)) := by
    intro s hs
    rw [← hα]
    exact hfix _ hs
  have hK : KData h N ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) φ := by
    refine ⟨unit_st_mul A, unit_mul_st A, ?_, ?_, ?_⟩
    · exact fix_cj hC A φ hN hu (fixmk u rfl)
    · intro w hw t ht
      exact fix_cj hC A φ (Tm_flag hU hw t).isNilpotent
        (s := mkSU (Tm_flag hU hw t).isNilpotent (Tm_isUni hU hw ht)) rfl
        (fixmk _ (GenSet_comm hu (Tm_mem_GenSet hU hw ht)).symm)
    · intro w hw v hv
      exact fix_cj hC A φ (Em_flag hU hw hv).isNilpotent
        (s := mkSU (Em_flag hU hw hv).isNilpotent (Em_isUni h2 hU hw hv)) rfl
        (fixmk _ (GenSet_comm hu (Em_mem_GenSet h2 hU hw hv)).symm)
  have hCay : CayFix h N ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) φ := by
    intro a ha X hXn hXu hXc hXr
    refine fix_cj hC A φ hXn (s := mkSU hXn hXu) rfl (fixmk _ ?_)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
    change smat (mkSU hXn hXu) * smat u = smat u * smat (mkSU hXn hXu)
    rw [hu, show smat (mkSU hXn hXu) = 1 + X from rfl]
    rw [show (1 + X) * (1 + N) = 1 + X + N + X * N by noncomm_ring,
      show (1 + N) * (1 + X) = 1 + N + X + N * X by noncomm_ring, hXc]
    abel
  obtain ⟨hσ, c, hc0, hcn⟩ := hK.key hn h2 hU hN hN0 hCay
  have hφ : φ = 1 := RingEquiv.ext hσ
  obtain ⟨e, c', hpow⟩ := pow_eq_one_of_scalar h hp2
    (M := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⟨c, hc0, hcn⟩
  have hAe : primeFormConjHom h (Cm n K) (A ^ p ^ e) = 1 := by
    apply conjHom_scalar _ c'
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    exact hpow
  have hα1 : α = primeFormConjHom h (Cm n K) A := by
    rw [hα, hφ, map_one, mul_one]
  have hpowα : α ^ p ^ e = 1 := by rw [hα1, ← map_pow, hAe]
  have hdvd : orderOf α ∣ p ^ e := orderOf_dvd_of_pow_eq_one hpowα
  have h1 : orderOf α = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right e hcop) hdvd
  exact orderOf_eq_one_iff.1 h1

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part14

section Part15

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

namespace CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section Abstract

variable {G : Type*} [Group G] [Finite G]

theorem gLAPPrimeCoreOf_eq_bot_of_framework' (hZ : Subgroup.center G = ⊥) {p : ℕ} (hp : p.Prime)
    (g : G) (Gen : Set G)
    (h1 : ∀ q ∈ Gen, g * q = q * g)
    (hGen : ∀ s q, s * g = g * s → q ∈ Gen → s * q * s⁻¹ ∈ Gen)
    (hp3 : ∀ q ∈ Gen, ∀ q' ∈ Gen, (q' * q⁻¹) ^ p = 1)
    (huniqInn : ∀ s : G, s * g = g * s → (orderOf s).Coprime p → (∀ q ∈ Gen, s * q = q * s) →
      s = 1)
    (huniq : ∀ α : MulAut G, (orderOf α).Coprime p → (∀ q, q * g = g * q → α q = q) → α = 1)
    (H : Subgroup (MulAut G)) (hH : innerAut G ≤ H) (x : MulAut G) (hx : x = MulAut.conj g) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut G))) = ⊥ := by
  have hinj := conj_injective_of_center_eq_bot hZ
  set X := H ⊓ Subgroup.centralizer ({x} : Set (MulAut G)) with hX
  have hmemX : ∀ q, q * g = g * q → (MulAut.conj q : MulAut G) ∈ X := by
    intro q hq
    refine ⟨hH ⟨q, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [hx, ← map_mul, ← map_mul, hq]
  have hcop : ∀ d ∈ GLAPPrimeCoreOf p X, (orderOf d).Coprime p := fun d hd =>
    CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf hp hd
  have stageA : ∀ s : G, (MulAut.conj s : MulAut G) ∈ GLAPPrimeCoreOf p X →
      (MulAut.conj s : MulAut G) = 1 := by
    intro s hs
    have hsX : (MulAut.conj s : MulAut G) ∈ X := by
      obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 hs
      rw [← hy]; exact y.2
    have hsg : s * g = g * s := by
      have h := (Subgroup.mem_centralizer_singleton_iff.1 hsX.2)
      rw [hx, ← map_mul, ← map_mul] at h
      exact hinj h
    have hfix : ∀ q ∈ Gen, s * q = q * s := by
      intro q hq
      have hq' : s * q * s⁻¹ ∈ Gen := hGen s q hsg hq
      have hcq := hmemX q (h1 q hq).symm
      have h2 : (MulAut.conj q : MulAut G) * (MulAut.conj s)⁻¹ * (MulAut.conj q)⁻¹ ∈
          GLAPPrimeCoreOf p X := by
        have := conj_mem_gLAPPrimeCoreOf (inv_mem hs) hcq
        simpa [mul_assoc] using this
      have h3 := mul_mem hs h2
      have he : (MulAut.conj s : MulAut G) * ((MulAut.conj q : MulAut G) *
          (MulAut.conj s)⁻¹ * (MulAut.conj q)⁻¹) = MulAut.conj ((s * q * s⁻¹) * q⁻¹) := by
        simp only [map_mul, map_inv, mul_assoc]
      rw [he] at h3
      have hord := hcop _ h3
      have hpow : ((MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G)) ^ p = 1 := by
        rw [← map_pow, hp3 q hq _ hq', map_one]
      have hdvd : orderOf (MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G) ∣ p :=
        orderOf_dvd_of_pow_eq_one hpow
      have h1' : orderOf (MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G) = 1 :=
        Nat.Coprime.eq_one_of_dvd hord hdvd
      have h4 : (MulAut.conj ((s * q * s⁻¹) * q⁻¹) : MulAut G) = 1 := orderOf_eq_one_iff.1 h1'
      have h5 : (s * q * s⁻¹) * q⁻¹ = 1 := hinj (by rw [h4, map_one])
      have h6 : s * q * s⁻¹ = q := by simpa [mul_inv_eq_one] using h5
      rw [mul_inv_eq_iff_eq_mul] at h6
      exact h6
    have hcs : (orderOf s).Coprime p := by
      rw [← orderOf_injective (MulAut.conj : G →* MulAut G) hinj s]
      exact hcop _ hs
    rw [huniqInn s hsg hcs hfix, map_one]
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  refine huniq α (hcop α hα) ?_
  intro q hq
  have hcq := hmemX q hq
  have h2 : (MulAut.conj q : MulAut G) * α⁻¹ * (MulAut.conj q)⁻¹ ∈ GLAPPrimeCoreOf p X := by
    have := conj_mem_gLAPPrimeCoreOf (inv_mem hα) hcq
    simpa [mul_assoc] using this
  have h3 := mul_mem hα h2
  have he : α * ((MulAut.conj q : MulAut G) * α⁻¹ * (MulAut.conj q)⁻¹) =
      MulAut.conj (α q * q⁻¹) := by
    have := mul_conj_mul_inv_eq α q
    rw [map_mul, map_inv, ← this]
    group
  rw [he] at h3
  have h4 := stageA _ h3
  have h5 : α q * q⁻¹ = 1 := hinj (by rw [h4, map_one])
  simpa [mul_inv_eq_one] using h5

end Abstract

end CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

end Part15

section Part16

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.DefChar.TwA

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

theorem defCharInnerCoreFreeFamTwistedA : DefCharInnerCoreFreeFam .twistedA := by
  intro S _ _ hS hnab idx hidx hSL p hp hp2 hch x hx hxo H hH
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hSL
  have hpq : p = q.p := by simpa using hch.symm
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e0
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := r + 1) (K := K))
  let e : S ≃* primeFormP h (Cm (r + 1) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  subst hpq
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple hS hnab
  obtain ⟨g, rfl⟩ := hx
  have hord : orderOf g = q.p := by
    rw [← orderOf_injective (MulAut.conj : S →* MulAut S) (conj_injective_of_center_eq_bot hZ) g]
    exact hxo
  have hord0 : orderOf (e g) = q.p := by rw [MulEquiv.orderOf_eq e g]; exact hord
  have hn3 : 3 ≤ r + 1 := by omega
  have : NeZero (r + 1) := ⟨by omega⟩
  obtain ⟨u, N, hu1, hN, hN0, hUN, hu⟩ := exists_unipotent_lift (h := h) (e g) hord0
  refine gLAPPrimeCoreOf_eq_bot_of_framework' hZ hp g {q' | e q' ∈ GenSet h N} ?_ ?_ ?_ ?_ ?_ H hH
    _ rfl
  · intro q' hq'
    apply e.injective
    rw [map_mul, map_mul, ← hu1]
    exact GenSet_comm hu hq'
  · intro s q' hs hq'
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (e s)
    have hs' : (σ : primeFormP h (Cm (r + 1) K)) * (u : primeFormP h (Cm (r + 1) K)) =
        (u : primeFormP h (Cm (r + 1) K)) * (σ : primeFormP h (Cm (r + 1) K)) := by
      rw [hσ, hu1, ← map_mul, ← map_mul, hs]
    have hσN := commute_lift hN hu hs'
    have := GenSet_conj hσN hq'
    show e (s * q' * s⁻¹) ∈ GenSet h N
    rw [map_mul, map_mul, map_inv, ← hσ]
    exact this
  · intro q' hq' q'' hq''
    apply e.injective
    rw [map_pow, map_mul, map_inv, map_one]
    exact GenSet_p3 hp2 hq' hq''
  · intro s hs hcop hGen
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (e s)
    have hs' : (σ : primeFormP h (Cm (r + 1) K)) * (u : primeFormP h (Cm (r + 1) K)) =
        (u : primeFormP h (Cm (r + 1) K)) * (σ : primeFormP h (Cm (r + 1) K)) := by
      rw [hσ, hu1, ← map_mul, ← map_mul, hs]
    have hcop' : (orderOf (σ : primeFormP h (Cm (r + 1) K))).Coprime q.p := by
      rw [hσ, MulEquiv.orderOf_eq e s]; exact hcop
    have h1 := uniq_inner hn3 hp2 hN hN0 hUN hu σ hs' hcop' (by
      intro q0 hq0
      have hmem : e.symm q0 ∈ {q' | e q' ∈ GenSet h N} := by simpa using hq0
      have h2 := congrArg e (hGen _ hmem)
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      rw [hσ]; exact h2)
    rw [hσ] at h1
    exact e.injective (by rw [h1, map_one])
  · intro α hα hfix
    have hcop' : (orderOf (MulAut.congr e α)).Coprime q.p := by
      rw [MulEquiv.orderOf_eq (MulAut.congr e) α]; exact hα
    have h1 : MulAut.congr e α = 1 := by
      refine uniq_out hn3 hp2 hN hN0 hUN hu _ hcop' ?_
      intro q' hq'
      have hc : e.symm q' * g = g * e.symm q' := by
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hu1]
        exact hq'
      have := hfix _ hc
      change e (α (e.symm q')) = q'
      rw [this]; simp
    exact (MulAut.congr e).injective (by rw [h1, map_one])

end CFSG.HardMathSupport.Timmesfeld.DefChar

end Part16

