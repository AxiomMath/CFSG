module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4QSu4
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Basic
public import CFSG.GH74.Generic.BProg.B2.GenLocU4GenBase

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups
open GenLocU4Basic GenLocU4Gen CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

namespace GenLocU4Eich

section Generic

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def rk (x y : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K := vecMulVec x (fun i => σ (y i))

@[expose] def eichS (u w : Fin 4 → K) (a : K) : Matrix (Fin 4) (Fin 4) K := 1 + a • (rk σ u w - rk σ w u)

@[expose] def tvS (v : Fin 4 → K) (c : K) : Matrix (Fin 4) (Fin 4) K := 1 + c • rk σ v v

theorem rk_mul (x y z t : Fin 4 → K) : rk σ x y * rk σ z t = herm σ y z • rk σ x t := by
  unfold rk
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  rfl

theorem rk_add_left (x x' y : Fin 4 → K) : rk σ (x + x') y = rk σ x y + rk σ x' y := by
  unfold rk
  exact Matrix.add_vecMulVec _ _ _

theorem rk_add_right (x y y' : Fin 4 → K) : rk σ x (y + y') = rk σ x y + rk σ x y' := by
  unfold rk
  rw [← Matrix.vecMulVec_add]
  congr 1
  funext i
  simp

theorem comm4 {R : Type*} [Ring R] (A B : R) (hAA : A * A = 0) (hBB : B * B = 0) (hABA : A * B * A = 0)
    (hBAB : B * A * B = 0) : (1 + A) * (1 + B) * (1 - A) * (1 - B) = 1 + (A * B - B * A) := by
  have e : (1 + A) * (1 + B) * (1 - A) * (1 - B) =
      1 + A * B - B * A - A * A - B * B + A * A * B + B * A * B - A * B * A - A * B * B + A * B * A * B := by
    noncomm_ring
  have h1 : A * A * B = 0 := by rw [hAA, zero_mul]
  have h2 : A * B * B = 0 := by rw [mul_assoc, hBB, mul_zero]
  have h3 : A * B * A * B = 0 := by rw [hABA, zero_mul]
  rw [e, h1, h2, h3, hAA, hBB, hBAB, hABA]
  abel

theorem eichS_comm_gen (hinv : ∀ x, σ (σ x) = x) (u w r r' : Fin 4 → K) (a b : K)
    (huu : herm σ u u = 0) (hww : herm σ w w = 0) (hrr : herm σ r r = 0) (hr'r' : herm σ r' r' = 0)
    (huw : herm σ u w = 0) (hrr' : herm σ r r' = 0) (hv : u + w = r + r') :
    eichS σ u w a * eichS σ r r' b * eichS σ u w (-a) * eichS σ r r' (-b) =
      tvS σ (u + w) (-(a * b * (herm σ u r - σ (herm σ u r)))) := by
  have hwu : herm σ w u = 0 := herm_eq_zero_comm σ hinv huw
  have hr'r : herm σ r' r = 0 := herm_eq_zero_comm σ hinv hrr'
  set γ := herm σ u r with hγ
  have hw : w = r + r' - u := by linear_combination hv
  have hr' : r' = u + w - r := by linear_combination -hv
  have h_ur' : herm σ u r' = -γ := by
    rw [hr', herm_sub_right, herm_add_right, huu, huw]; simp [hγ]
  have h_wr : herm σ w r = -γ := by
    rw [hw, herm_sub_left, herm_add_left, hrr, hr'r]; simp [hγ]
  have h_wr' : herm σ w r' = γ := by
    rw [hw, herm_sub_left, herm_add_left, hrr', hr'r', h_ur']; ring
  have h_r'u : herm σ r' u = -σ γ := by rw [herm_conj σ hinv u r', h_ur', map_neg]
  have h_rw : herm σ r w = -σ γ := by rw [herm_conj σ hinv w r, h_wr, map_neg]
  have h_r'w : herm σ r' w = σ γ := by rw [herm_conj σ hinv w r', h_wr']
  have h_ru : herm σ r u = σ γ := by rw [herm_conj σ hinv u r]
  have hTa0 : rk σ (u + w) (u + w) = rk σ (u + w) (r + r') := congrArg (fun z => rk σ (u + w) z) hv
  have hTb0 : rk σ (u + w) (u + w) = rk σ (r + r') (u + w) := congrArg (fun z => rk σ z (u + w)) hv
  have hTc : rk σ (u + w) (u + w) = rk σ (r + r') (r + r') := by rw [hv]
  have hTa : rk σ (u + w) (u + w) = rk σ u r + rk σ u r' + rk σ w r + rk σ w r' := by
    rw [hTa0, rk_add_left, rk_add_right, rk_add_right]; abel
  have hTb : rk σ (u + w) (u + w) = rk σ r u + rk σ r w + rk σ r' u + rk σ r' w := by
    rw [hTb0, rk_add_left, rk_add_right, rk_add_right]; abel
  have hNAA : (a • (rk σ u w - rk σ w u)) * (a • (rk σ u w - rk σ w u)) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [Matrix.sub_mul, Matrix.mul_sub, rk_mul, hwu, hww, huu, huw, zero_smul, sub_self, smul_zero]
  have hNBB : (b • (rk σ r r' - rk σ r' r)) * (b • (rk σ r r' - rk σ r' r)) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [Matrix.sub_mul, Matrix.mul_sub, rk_mul, hr'r, hrr, hr'r', hrr', zero_smul, sub_self, smul_zero]
  have hNAB : (a • (rk σ u w - rk σ w u)) * (b • (rk σ r r' - rk σ r' r)) =
      (-(a * b * γ)) • rk σ (u + w) (u + w) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hTa]
    simp only [Matrix.sub_mul, Matrix.mul_sub, rk_mul, h_wr, h_wr', h_ur', ← hγ]
    module
  have hNBA : (b • (rk σ r r' - rk σ r' r)) * (a • (rk σ u w - rk σ w u)) =
      (-(a * b * σ γ)) • rk σ (u + w) (u + w) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hTb]
    simp only [Matrix.sub_mul, Matrix.mul_sub, rk_mul, h_r'u, h_r'w, h_ru, h_rw]
    module
  have hTNA : rk σ (u + w) (u + w) * (a • (rk σ u w - rk σ w u)) = 0 := by
    rw [Matrix.mul_smul]
    simp only [Matrix.mul_sub, rk_mul, herm_add_left, huu, hwu, huw, hww, zero_smul, sub_self, smul_zero, add_zero]
  have hTNB : rk σ (u + w) (u + w) * (b • (rk σ r r' - rk σ r' r)) = 0 := by
    rw [hTc, Matrix.mul_smul]
    simp only [Matrix.mul_sub, rk_mul, herm_add_left, hrr, hr'r, hrr', hr'r', zero_smul, sub_self, smul_zero, add_zero]
  have e3 : eichS σ u w (-a) = 1 - a • (rk σ u w - rk σ w u) := by
    simp only [eichS, neg_smul, sub_eq_add_neg]
  have e4 : eichS σ r r' (-b) = 1 - b • (rk σ r r' - rk σ r' r) := by
    simp only [eichS, neg_smul, sub_eq_add_neg]
  have hABA : (a • (rk σ u w - rk σ w u)) * (b • (rk σ r r' - rk σ r' r)) * (a • (rk σ u w - rk σ w u)) = 0 := by
    rw [hNAB, Matrix.smul_mul, hTNA, smul_zero]
  have hBAB : (b • (rk σ r r' - rk σ r' r)) * (a • (rk σ u w - rk σ w u)) * (b • (rk σ r r' - rk σ r' r)) = 0 := by
    rw [hNBA, Matrix.smul_mul, hTNB, smul_zero]
  rw [show eichS σ u w a = 1 + a • (rk σ u w - rk σ w u) from rfl,
    show eichS σ r r' b = 1 + b • (rk σ r r' - rk σ r' r) from rfl, e3, e4,
    comm4 _ _ hNAA hNBB hABA hBAB, hNAB, hNBA, tvS, ← sub_smul]
  congr 2
  ring

theorem eich_nil (u w : Fin 4 → K) (a : K) (huu : herm σ u u = 0) (hww : herm σ w w = 0) (huw : herm σ u w = 0)
    (hwu : herm σ w u = 0) :
    (a • (rk σ u w - rk σ w u)) * (a • (rk σ u w - rk σ w u)) = 0 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.sub_mul, Matrix.mul_sub, rk_mul, hwu, hww, huu, huw, zero_smul, sub_self, smul_zero]

theorem eichS_star (hinv : ∀ x, σ (σ x) = x) (u w : Fin 4 → K) (a : K) (ha : σ a = a) :
    ((eichS σ u w a).map σ)ᵀ = 1 - a • (rk σ u w - rk σ w u) := by
  ext i j
  simp only [eichS, rk, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Matrix.one_apply, map_add, map_mul, map_sub, ha, hinv]
  by_cases h : i = j
  · subst h; simp; ring
  · have h' : ¬ j = i := fun e => h e.symm
    simp [h, h']
    ring

theorem eichS_unitary (hinv : ∀ x, σ (σ x) = x) (u w : Fin 4 → K) (a : K) (ha : σ a = a)
    (huu : herm σ u u = 0) (hww : herm σ w w = 0) (huw : herm σ u w = 0) :
    ((eichS σ u w a).map σ)ᵀ * eichS σ u w a = 1 := by
  have hwu : herm σ w u = 0 := herm_eq_zero_comm σ hinv huw
  rw [eichS_star σ hinv u w a ha]
  have hN := eich_nil σ u w a huu hww huw hwu
  show (1 - a • (rk σ u w - rk σ w u)) * (1 + a • (rk σ u w - rk σ w u)) = 1
  generalize a • (rk σ u w - rk σ w u) = N at hN ⊢
  calc (1 - N) * (1 + N) = 1 - N * N := by noncomm_ring
    _ = 1 := by rw [hN, sub_zero]

theorem eichS_det (u w : Fin 4 → K) (a : K) (huu : herm σ u u = 0) (hww : herm σ w w = 0) (huw : herm σ u w = 0)
    (hwu : herm σ w u = 0) : (eichS σ u w a).det = 1 := by
  let A₁ : Matrix (Fin 4) (Fin 2) K := Matrix.of fun i j => ![u i, w i] j
  let B₁ : Matrix (Fin 2) (Fin 4) K := Matrix.of fun j i => ![a * σ (w i), -(a * σ (u i))] j
  have h1 : A₁ * B₁ = a • (rk σ u w - rk σ w u) := by
    ext i k
    simp only [A₁, B₁, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, rk, Matrix.smul_apply,
      Matrix.sub_apply, vecMulVec_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hs : ∀ (c : K) (x y : Fin 4 → K), ∑ i, c * σ (x i) * y i = c * herm σ x y := by
    intro c x y
    simp only [herm, Finset.mul_sum, mul_assoc]
  have h2 : B₁ * A₁ = 0 := by
    ext j l
    fin_cases j <;> fin_cases l <;>
      simp [A₁, B₁, Matrix.mul_apply, hs, huu, hww, huw, hwu, neg_mul, Finset.sum_neg_distrib]
  have h3 := Matrix.det_one_add_mul_comm A₁ B₁
  rw [h1, h2] at h3
  simp only [eichS]
  rw [h3]
  simp

theorem eichS_comm_sq (hinv : ∀ x, σ (σ x) = x) (x : Matrix (Fin 4) (Fin 4) K) (u w : Fin 4 → K) (a ι : K)
    (hι : ι * ι = -1) (hιs : σ ι = ι) (hx : (x.map σ)ᵀ * x = 1) (hxu : x *ᵥ u = ι • u)
    (hxw : x *ᵥ w = (-ι) • w) : eichS σ u w a * x = x * eichS σ u w a := by
  have hu : (x.map σ)ᵀ *ᵥ u = (-ι) • u := by
    have h0 : u = ι • ((x.map σ)ᵀ *ᵥ u) := by
      calc u = (1 : Matrix (Fin 4) (Fin 4) K) *ᵥ u := (Matrix.one_mulVec u).symm
        _ = ((x.map σ)ᵀ * x) *ᵥ u := by rw [hx]
        _ = (x.map σ)ᵀ *ᵥ (x *ᵥ u) := (Matrix.mulVec_mulVec _ _ _).symm
        _ = ι • ((x.map σ)ᵀ *ᵥ u) := by rw [hxu, Matrix.mulVec_smul]
    calc (x.map σ)ᵀ *ᵥ u = (-ι * ι) • ((x.map σ)ᵀ *ᵥ u) := by rw [neg_mul, hι]; simp
      _ = (-ι) • (ι • ((x.map σ)ᵀ *ᵥ u)) := by rw [smul_smul]
      _ = (-ι) • u := by rw [← h0]
  have hw : (x.map σ)ᵀ *ᵥ w = ι • w := by
    have h0 : w = (-ι) • ((x.map σ)ᵀ *ᵥ w) := by
      calc w = (1 : Matrix (Fin 4) (Fin 4) K) *ᵥ w := (Matrix.one_mulVec w).symm
        _ = ((x.map σ)ᵀ * x) *ᵥ w := by rw [hx]
        _ = (x.map σ)ᵀ *ᵥ (x *ᵥ w) := (Matrix.mulVec_mulVec _ _ _).symm
        _ = (-ι) • ((x.map σ)ᵀ *ᵥ w) := by rw [hxw, Matrix.mulVec_smul]
    calc (x.map σ)ᵀ *ᵥ w = (ι * -ι) • ((x.map σ)ᵀ *ᵥ w) := by
          rw [mul_neg, hι]; simp
      _ = ι • ((-ι) • ((x.map σ)ᵀ *ᵥ w)) := by rw [smul_smul]
      _ = ι • w := by rw [← h0]
  have hvec : ∀ z : Fin 4 → K, (fun i => σ (z i)) ᵥ* x = fun j => σ (((x.map σ)ᵀ *ᵥ z) j) := by
    intro z
    funext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, hinv, mul_comm]
  have hw' : (fun i => σ (w i)) ᵥ* x = ι • (fun i => σ (w i)) := by
    rw [hvec, hw]; funext j; simp [hιs]
  have hu' : (fun i => σ (u i)) ᵥ* x = (-ι) • (fun i => σ (u i)) := by
    rw [hvec, hu]; funext j; simp [hιs]
  have e1 : rk σ u w * x = ι • rk σ u w := by
    unfold rk; rw [Matrix.vecMulVec_mul, hw', Matrix.vecMulVec_smul]
  have e2 : rk σ w u * x = (-ι) • rk σ w u := by
    unfold rk; rw [Matrix.vecMulVec_mul, hu', Matrix.vecMulVec_smul]
  have e3 : x * rk σ u w = ι • rk σ u w := by
    unfold rk; rw [Matrix.mul_vecMulVec, hxu, Matrix.smul_vecMulVec]
  have e4 : x * rk σ w u = (-ι) • rk σ w u := by
    unfold rk; rw [Matrix.mul_vecMulVec, hxw, Matrix.smul_vecMulVec]
  have hN : (rk σ u w - rk σ w u) * x = x * (rk σ u w - rk σ w u) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, e1, e2, e3, e4]
  unfold eichS
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hN]

end Generic

variable {K : Type} [Field K]

abbrev gM {q : ℕ} (g : ↥(StatedSU 4 q K)) : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

@[expose] def hU (q : ℕ) (u v : Fin 4 → K) : K := ∑ i, (u i) ^ q * v i

@[expose] def eichM (q : ℕ) (u w : Fin 4 → K) (a : K) : Matrix (Fin 4) (Fin 4) K :=
  1 + a • (vecMulVec u (fun i => (w i) ^ q) - vecMulVec w (fun i => (u i) ^ q))

@[expose] def tvM (q : ℕ) (v : Fin 4 → K) (c : K) : Matrix (Fin 4) (Fin 4) K :=
  1 + c • vecMulVec v (fun i => (v i) ^ q)

variable [Finite K] {p f : ℕ}

section Bridge

variable [Fact p.Prime] [CharP K p]

theorem hU_eq (u v : Fin 4 → K) : hU (p ^ f) u v = herm (unitaryInvolution K p f) u v := by
  simp only [hU, herm, unitaryInvolution_apply]

theorem eichM_eq (u w : Fin 4 → K) (a : K) : eichM (p ^ f) u w a = eichS (unitaryInvolution K p f) u w a := by
  simp only [eichM, eichS, rk, unitaryInvolution_apply]

theorem tvM_eq (v : Fin 4 → K) (c : K) : tvM (p ^ f) v c = tvS (unitaryInvolution K p f) v c := by
  simp only [tvM, tvS, rk, unitaryInvolution_apply]

end Bridge

theorem eich_comm (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) (u w r r' : Fin 4 → K) (a b : K)
    (_ha : a ^ (p ^ f) = a) (_hb : b ^ (p ^ f) = b)
    (huu : hU (p ^ f) u u = 0) (hww : hU (p ^ f) w w = 0) (hrr : hU (p ^ f) r r = 0)
    (hr'r' : hU (p ^ f) r' r' = 0) (huw : hU (p ^ f) u w = 0) (hrr' : hU (p ^ f) r r' = 0) (hv : u + w = r + r') :
    eichM (p ^ f) u w a * eichM (p ^ f) r r' b * eichM (p ^ f) u w (-a) * eichM (p ^ f) r r' (-b) =
      tvM (p ^ f) (u + w) (-(a * b * (hU (p ^ f) u r - (hU (p ^ f) u r) ^ (p ^ f)))) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have hinv := (isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK).invol
  simp only [hU_eq] at huu hww hrr hr'r' huw hrr'
  simp only [eichM_eq, tvM_eq, hU_eq, ← unitaryInvolution_apply K p f]
  exact eichS_comm_gen _ hinv u w r r' a b huu hww hrr hr'r' huw hrr' hv

theorem eichM_mem (hp : p.Prime) (_hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (u w : Fin 4 → K) (a : K)
    (ha : a ^ (p ^ f) = a) (huu : hU (p ^ f) u u = 0) (hww : hU (p ^ f) w w = 0) (huw : hU (p ^ f) u w = 0) :
    IsUnitaryU (p ^ f) (eichM (p ^ f) u w a) ∧ (eichM (p ^ f) u w a).det = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have hinv := (isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK).invol
  have hf : (fun x : K => x ^ (p ^ f)) = ⇑(unitaryInvolution K p f) :=
    funext fun x => (unitaryInvolution_apply K p f x).symm
  simp only [hU_eq] at huu hww huw
  have hwu : herm (unitaryInvolution K p f) w u = 0 := herm_eq_zero_comm _ hinv huw
  refine ⟨?_, ?_⟩
  · show ((eichM (p ^ f) u w a).map (fun x : K => x ^ (p ^ f)))ᵀ * eichM (p ^ f) u w a = 1
    rw [hf, eichM_eq]
    exact eichS_unitary _ hinv u w a (by rw [unitaryInvolution_apply]; exact ha) huu hww huw
  · rw [eichM_eq]
    exact eichS_det _ u w a huu hww huw hwu

theorem eichM_comm_sq (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) (x : Matrix (Fin 4) (Fin 4) K) (u w : Fin 4 → K)
    (a ι : K) (hι : ι * ι = -1) (hιq : ι ^ (p ^ f) = ι) (hx : (x.map (· ^ (p ^ f)))ᵀ * x = 1)
    (hxu : x *ᵥ u = ι • u) (hxw : x *ᵥ w = (-ι) • w) :
    eichM (p ^ f) u w a * x = x * eichM (p ^ f) u w a := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have hinv := (isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK).invol
  have hf : (fun x : K => x ^ (p ^ f)) = ⇑(unitaryInvolution K p f) :=
    funext fun x => (unitaryInvolution_apply K p f x).symm
  rw [hf] at hx
  rw [eichM_eq]
  exact eichS_comm_sq _ hinv x u w a ι hι (by rw [unitaryInvolution_apply]; exact hιq) hx hxu hxw

section Blocks

variable [Fact p.Prime] [CharP K p]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem herm_v0 {σ : K ≃+* K} {β : K} (hβ : σ β * β = -1) :
    herm σ (![1, β, 0, 0] : Fin 4 → K) ![1, β, 0, 0] = 0 := by
  rw [herm_def, Fin.sum_univ_four]
  simp
  linear_combination hβ

theorem block0_gen (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) (h2 : (2 : K) ≠ 0) {β : K}
    (hβ : unitaryInvolution K p f β * β = -1) (Γ : Subgroup (Su K p f 4))
    (hP : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0), tv hσ.invol (herm_v0 hβ) hc ∈ Γ)
    (hM : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0),
      tv hσ.invol (herm_v0 (β := -β) (by rw [map_neg, neg_mul_neg]; exact hβ)) hc ∈ Γ) :
    ∀ B : Su K p f 2, blockEmb2 K p f 3 0 B ∈ Γ := by
  set σ := unitaryInvolution K p f with hσdef
  have hβ0 : β ≠ 0 := by
    rintro rfl
    simp at hβ
  have hσ2 : σ ((2 : K)⁻¹) = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]
  obtain ⟨a, ha_def⟩ : ∃ a : Fin 2 → K, a = ![(2 : K)⁻¹, β * (2 : K)⁻¹] := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : Fin 2 → K, b = ![1, -β] := ⟨_, rfl⟩
  have ha : herm σ a a = 0 := by
    rw [ha_def, herm_def, Fin.sum_univ_two]
    simp [hσ2]
    field_simp
    linear_combination hβ
  have hb : herm σ b b = 0 := by
    rw [hb_def, herm_def, Fin.sum_univ_two]
    simp
    linear_combination hβ
  have hab : herm σ a b = 1 := by
    rw [ha_def, hb_def, herm_def, Fin.sum_univ_two]
    simp [hσ2]
    field_simp
    linear_combination -hβ
  have hexp : ∀ v, v = herm σ b v • a + herm σ a v • b := by
    intro v
    rw [ha_def, hb_def]
    simp only [herm_def, Fin.sum_univ_two]
    funext j
    fin_cases j <;> simp [hσ2] <;> field_simp
    · ring
    · linear_combination (2 * v 1) * hβ
  have hPab : a 0 * b 1 - b 0 * a 1 ≠ 0 := by
    rw [ha_def, hb_def]
    show (2 : K)⁻¹ * (-β) - 1 * (β * (2 : K)⁻¹) ≠ 0
    intro h
    apply hβ0
    linear_combination (-1 : K) * h - β * mul_inv_cancel₀ h2
  have ha4 : herm σ ![a 0, a 1, 0, 0] ![a 0, a 1, 0, 0] = 0 := by
    rw [herm_def, Fin.sum_univ_four]
    have := ha
    rw [herm_def, Fin.sum_univ_two] at this
    simp [this]
  have hΓa : ∀ (c : K) (hc : c + σ c = 0), tv hσ.invol ha hc ∈ Γ.comap (blockEmb2 K p f 3 0) := by
    intro c hc
    show blockEmb2 K p f 3 0 (tv hσ.invol ha hc) ∈ Γ
    rw [GenLocU4QSu4.blockEmb2_zero_eq_tv hσ.invol (tv hσ.invol ha hc) a c hc (fun y => tv_smul hσ.invol ha hc y) ha4]
    refine GenLocU4Aux.tv_mem_of_scalar hσ.invol Γ (u := ![1, β, 0, 0]) (a := ![a 0, a 1, 0, 0]) 2 h2 ?_
      (fun _ c hc => hP c hc) ha4 c hc
    rw [ha_def]
    funext j
    fin_cases j <;> simp <;> field_simp
  have hΓb : ∀ (c : K) (hc : c + σ c = 0), tv hσ.invol hb hc ∈ Γ.comap (blockEmb2 K p f 3 0) := by
    intro c hc
    show blockEmb2 K p f 3 0 (tv hσ.invol hb hc) ∈ Γ
    have hb4 : herm σ ![b 0, b 1, 0, 0] ![b 0, b 1, 0, 0] = 0 := by
      rw [herm_def, Fin.sum_univ_four]
      have := hb
      rw [herm_def, Fin.sum_univ_two] at this
      simp [this]
    rw [GenLocU4QSu4.blockEmb2_zero_eq_tv hσ.invol (tv hσ.invol hb hc) b c hc (fun y => tv_smul hσ.invol hb hc y) hb4]
    have hbv : (![b 0, b 1, 0, 0] : Fin 4 → K) = ![1, -β, 0, 0] := by rw [hb_def]; rfl
    have := hM c hc
    simpa [hbv] using this
  intro B
  exact GenLocU4QSu4.mem_of_two_tv hσ ha hb hab hexp hPab (Γ.comap (blockEmb2 K p f 3 0)) hΓa hΓb B

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem herm_v2 {σ : K ≃+* K} {β : K} (hβ : σ β * β = -1) :
    herm σ (![0, 0, 1, β] : Fin 4 → K) ![0, 0, 1, β] = 0 := by
  rw [herm_def, Fin.sum_univ_four]
  simp
  linear_combination hβ

theorem block2_gen (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) (h2 : (2 : K) ≠ 0) {β : K}
    (hβ : unitaryInvolution K p f β * β = -1) (Γ : Subgroup (Su K p f 4))
    (hP : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0), tv hσ.invol (herm_v2 hβ) hc ∈ Γ)
    (hM : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0),
      tv hσ.invol (herm_v2 (β := -β) (by rw [map_neg, neg_mul_neg]; exact hβ)) hc ∈ Γ) :
    ∀ B : Su K p f 2, blockEmb2 K p f 3 2 B ∈ Γ := by
  set σ := unitaryInvolution K p f with hσdef
  have hβ0 : β ≠ 0 := by
    rintro rfl
    simp at hβ
  have hσ2 : σ ((2 : K)⁻¹) = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]
  obtain ⟨a, ha_def⟩ : ∃ a : Fin 2 → K, a = ![(2 : K)⁻¹, β * (2 : K)⁻¹] := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : Fin 2 → K, b = ![1, -β] := ⟨_, rfl⟩
  have ha : herm σ a a = 0 := by
    rw [ha_def, herm_def, Fin.sum_univ_two]
    simp [hσ2]
    field_simp
    linear_combination hβ
  have hb : herm σ b b = 0 := by
    rw [hb_def, herm_def, Fin.sum_univ_two]
    simp
    linear_combination hβ
  have hab : herm σ a b = 1 := by
    rw [ha_def, hb_def, herm_def, Fin.sum_univ_two]
    simp [hσ2]
    field_simp
    linear_combination -hβ
  have hexp : ∀ v, v = herm σ b v • a + herm σ a v • b := by
    intro v
    rw [ha_def, hb_def]
    simp only [herm_def, Fin.sum_univ_two]
    funext j
    fin_cases j <;> simp [hσ2] <;> field_simp
    · ring
    · linear_combination (2 * v 1) * hβ
  have hPab : a 0 * b 1 - b 0 * a 1 ≠ 0 := by
    rw [ha_def, hb_def]
    show (2 : K)⁻¹ * (-β) - 1 * (β * (2 : K)⁻¹) ≠ 0
    intro h
    apply hβ0
    linear_combination (-1 : K) * h - β * mul_inv_cancel₀ h2
  have ha4 : herm σ ![0, 0, a 0, a 1] ![0, 0, a 0, a 1] = 0 := by
    rw [herm_def, Fin.sum_univ_four]
    have := ha
    rw [herm_def, Fin.sum_univ_two] at this
    simp [this]
  have hΓa : ∀ (c : K) (hc : c + σ c = 0), tv hσ.invol ha hc ∈ Γ.comap (blockEmb2 K p f 3 2) := by
    intro c hc
    show blockEmb2 K p f 3 2 (tv hσ.invol ha hc) ∈ Γ
    rw [GenLocU4QSu4.blockEmb2_two_eq_tv hσ.invol (tv hσ.invol ha hc) a c hc (fun y => tv_smul hσ.invol ha hc y) ha4]
    refine GenLocU4Aux.tv_mem_of_scalar hσ.invol Γ (u := ![0, 0, 1, β]) (a := ![0, 0, a 0, a 1]) 2 h2 ?_
      (fun _ c hc => hP c hc) ha4 c hc
    rw [ha_def]
    funext j
    fin_cases j <;> simp <;> field_simp
  have hΓb : ∀ (c : K) (hc : c + σ c = 0), tv hσ.invol hb hc ∈ Γ.comap (blockEmb2 K p f 3 2) := by
    intro c hc
    show blockEmb2 K p f 3 2 (tv hσ.invol hb hc) ∈ Γ
    have hb4 : herm σ ![0, 0, b 0, b 1] ![0, 0, b 0, b 1] = 0 := by
      rw [herm_def, Fin.sum_univ_four]
      have := hb
      rw [herm_def, Fin.sum_univ_two] at this
      simp [this]
    rw [GenLocU4QSu4.blockEmb2_two_eq_tv hσ.invol (tv hσ.invol hb hc) b c hc (fun y => tv_smul hσ.invol hb hc y) hb4]
    have hbv : (![0, 0, b 0, b 1] : Fin 4 → K) = ![0, 0, 1, -β] := by rw [hb_def]; rfl
    have := hM c hc
    simpa [hbv] using this
  intro B
  exact GenLocU4QSu4.mem_of_two_tv hσ ha hb hab hexp hPab (Γ.comap (blockEmb2 K p f 3 2)) hΓa hΓb B

end Blocks

theorem su4_eq_top_of_tv_frame (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (P : GL (Fin 4) K) (hP : IsUnitaryU (p ^ f) (P : Matrix (Fin 4) (Fin 4) K))
    (β γ : K) (hβ : β ^ (p ^ f) * β = -1) (hγ : γ ^ (p ^ f) * γ = -1)
    (hT : ∀ w : Fin 4 → K, (w = ![1, β, 0, 0] ∨ w = ![1, -β, 0, 0] ∨ w = ![0, 0, 1, γ] ∨ w = ![0, 0, 1, -γ]) →
      ∀ g, IsTransvU (p ^ f) ((P : Matrix (Fin 4) (Fin 4) K) *ᵥ w) g → g ∈ Γ)
    (v : Fin 4 → K) (hv : ∑ i, (v i) ^ (p ^ f) * v i = 0)
    (hv01 : (v 0) ^ (p ^ f) * v 0 + (v 1) ^ (p ^ f) * v 1 ≠ 0)
    (hTv : ∀ g, IsTransvU (p ^ f) ((P : Matrix (Fin 4) (Fin 4) K) *ᵥ v) g → g ∈ Γ) : Γ = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have hσ := isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rwa [ringChar.eq K p])
  have hsig : ∀ x : K, unitaryInvolution K p f x = x ^ (p ^ f) := fun x => unitaryInvolution_apply K p f x
  have hβ' : unitaryInvolution K p f β * β = -1 := by rw [hsig]; exact hβ
  have hγ' : unitaryInvolution K p f γ * γ = -1 := by rw [hsig]; exact hγ
  let Ψ := frameConj (fieldData hK) P hP
  have hTv' : ∀ (w : Fin 4 → K) (hw : herm (unitaryInvolution K p f) w w = 0),
      (w = ![1, β, 0, 0] ∨ w = ![1, -β, 0, 0] ∨ w = ![0, 0, 1, γ] ∨ w = ![0, 0, 1, -γ]) →
      ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0), tv hσ.invol hw hc ∈ Γ.comap Ψ := by
    intro w hw hwc c hc
    show Ψ (tv hσ.invol hw hc) ∈ Γ
    by_cases hc0 : c = 0
    · subst hc0
      have h1 : tv hσ.invol hw hc = 1 := by
        apply ext_smul
        intro x
        rw [tv_smul, one_smul]
        simp
      rw [h1, map_one]
      exact Γ.one_mem
    · exact hT w hwc _ ⟨c, by rwa [hsig] at hc, hc0, coe_frameConj_tv hK P hP w hw c hc⟩
  have h01 : ∀ g, InBlock (p ^ f) P 0 g → g ∈ Γ := by
    intro g hg
    obtain ⟨x, rfl⟩ := exists_frameBlock_of_inBlock hK P hP 0 g hg
    exact block0_gen hσ h2 hβ' (Γ.comap Ψ)
      (fun c hc => hTv' _ (herm_v0 hβ') (Or.inl rfl) c hc)
      (fun c hc => hTv' _ (herm_v0 (β := -β) (by rw [map_neg, neg_mul_neg]; exact hβ')) (Or.inr (Or.inl rfl)) c hc) x
  have h23 : ∀ g, InBlock (p ^ f) P 2 g → g ∈ Γ := by
    intro g hg
    obtain ⟨x, rfl⟩ := exists_frameBlock_of_inBlock hK P hP 2 g hg
    exact block2_gen hσ h2 hγ' (Γ.comap Ψ)
      (fun c hc => hTv' _ (herm_v2 hγ') (Or.inr (Or.inr (Or.inl rfl))) c hc)
      (fun c hc => hTv' _ (herm_v2 (β := -γ) (by rw [map_neg, neg_mul_neg]; exact hγ')) (Or.inr (Or.inr (Or.inr rfl))) c hc) x
  exact su4_eq_top_of_link_raw hp hp2 hK Γ P hP h01 h23 v hv hv01 hTv

end GenLocU4Eich

end CFSG.GH74.Generic.BProg.B2
