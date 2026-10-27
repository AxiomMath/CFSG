module

public import CFSG.HardMathSupport.U4FF.ClassTmod
public import CFSG.HardMathSupport.U4FF.ClassLocLow
public import CFSG.HardMathSupport.U4FF.ClassUminusB
public import CFSG.HardMathSupport.U4FF.ClassDigits

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

section Aux

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]

theorem dotProduct_pureTensor [DecidableEq ι] (u v : (i : ι) → κ i → k) :
    pureTensor κ u ⬝ᵥ pureTensor κ v = ∏ i, (u i ⬝ᵥ v i) := by
  have := Finset.prod_univ_sum (fun i => (Finset.univ : Finset (κ i)))
    (fun i b => u i b * v i b)
  simp only [Fintype.piFinset_univ] at this
  calc pureTensor κ u ⬝ᵥ pureTensor κ v = ∑ x : (i : ι) → κ i, ∏ i, u i (x i) * v i (x i) := by
        unfold dotProduct pureTensor
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ j, u i j * v i j := this.symm
    _ = ∏ i, (u i ⬝ᵥ v i) := rfl

end Aux

section SUInv

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem su_inv_apply (g : SU4 K n) (i j : Fin 4) :
    (((g⁻¹ : SU4 K n) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j =
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) (Fin.rev j) (Fin.rev i)) ^ 2 ^ n := by
  set A := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hA
  set B := (((g⁻¹ : SU4 K n) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← Units.val_mul]
    have : ((g : GL (Fin 4) K)) * ((g⁻¹ : SU4 K n) : GL (Fin 4) K) = 1 := by
      rw [← Subgroup.coe_mul, mul_inv_cancel]
      rfl
    rw [this, Units.val_one]
  have hU : conjTr (unitaryInvolution K 2 n) A * antidiag 4 * A = antidiag 4 := g.2.2
  have h1 : conjTr (unitaryInvolution K 2 n) A * antidiag 4 = antidiag 4 * B := by
    calc conjTr (unitaryInvolution K 2 n) A * antidiag 4
        = conjTr (unitaryInvolution K 2 n) A * antidiag 4 * (A * B) := by rw [hAB, Matrix.mul_one]
      _ = (conjTr (unitaryInvolution K 2 n) A * antidiag 4 * A) * B := by
          simp only [Matrix.mul_assoc]
      _ = antidiag 4 * B := by rw [hU]
  have h2 : B = antidiag 4 * conjTr (unitaryInvolution K 2 n) A * antidiag 4 := by
    calc B = (antidiag 4 * antidiag 4 : Matrix (Fin 4) (Fin 4) K) * B := by rw [J_mul_J, Matrix.one_mul]
      _ = antidiag 4 * (antidiag 4 * B) := by rw [Matrix.mul_assoc]
      _ = antidiag 4 * (conjTr (unitaryInvolution K 2 n) A * antidiag 4) := by rw [h1]
      _ = antidiag 4 * conjTr (unitaryInvolution K 2 n) A * antidiag 4 := by
          rw [Matrix.mul_assoc]
  rw [h2, J_mul_mul_J_apply]
  simp [conjTr, unitaryInvolution_apply, iterateFrobenius_def]

end SUInv

section Norm


variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {k : Type} [Field k] [CharP k 2]

theorem Efun_twist (φ : K →+* k) (u : ↥(LowerU K n)) :
    Efun (twistHom n φ (u : SU4 K n)) = φ (Eu n u) := by
  unfold Efun Eu
  have hv : ∀ i j, ((twistHom n φ (u : SU4 K n) : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) i j =
      φ (loMat u i j) := fun i j => rfl
  have hinv : (((twistHom n φ (u : SU4 K n))⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) 3 0 =
      φ (loMat u 3 0 ^ 2 ^ n) := by
    rw [← map_inv]
    have := su_inv_apply (u : SU4 K n) 3 0
    change φ (((((u : SU4 K n)⁻¹ : SU4 K n) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 0) = _
    rw [this]
    rfl
  simp only [hv]
  rw [hinv]
  simp [map_mul, map_add, map_pow, CharTwo.sub_eq_add]

@[expose] noncomputable def lamR (k : Type*) [Field k] [CharP k 2] : Fin (locM true true true) → k :=
  fun x => (locSpec true true true (locValid true true true).1).Bk k
    (ambEq (fsOf true true true) (lowIdx (fsOf true true true))) x

theorem lamR_locR_ylocC (g : SL(4, k)) :
    lamR k ⬝ᵥ (locR true true true k g *ᵥ ylocC true true true k) = Efun g :=
  lam_locMat_y (locValid true true true).1 g

@[expose] noncomputable def LamT (n : ℕ) (k : Type) [Field k] [CharP k 2] :
    (TIdx (rhoL n) → k) → k :=
  fun w => pureTensor (fun _ : Fin n => Fin (locM true true true)) (fun _ => lamR k) ⬝ᵥ w

theorem LamT_sum {ι : Type*} (s : Finset ι) (f : ι → (TIdx (rhoL n) → k)) :
    LamT n k (∑ i ∈ s, f i) = ∑ i ∈ s, LamT n k (f i) := by
  unfold LamT
  exact dotProduct_sum _ s f

theorem LamT_orbit (φ : Fin n → K →+* k) (u : ↥(LowerU K n)) :
    LamT n k (TmodΦ (rhoL n) φ (u : SU4 K n) *ᵥ hwv (rhoL n) k) =
      ∏ i : Fin n, φ i (Eu n u) := by
  have h := kronDep_mulVec_pure (κ := fun _ : Fin n => Fin (locM true true true))
    (fun i => locR true true true k (twistHom n (φ i) (u : SU4 K n)))
    (fun _ => ylocC true true true k)
  unfold LamT
  have h' : TmodΦ (rhoL n) φ (u : SU4 K n) *ᵥ hwv (rhoL n) k = pureTensor
      (fun _ : Fin n => Fin (locM true true true))
      (fun i => locR true true true k (twistHom n (φ i) (u : SU4 K n)) *ᵥ
        ylocC true true true k) := h
  rw [h', dotProduct_pureTensor]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lamR_locR_ylocC, Efun_twist]

theorem prod_frobTw [Algebra K k] (x : K) :
    ∏ i : Fin n, frobTw K k i x = (algebraMap K k x) ^ (2 ^ n - 1) := by
  have h1 : ∀ i : Fin n, frobTw K k i x = (algebraMap K k x) ^ 2 ^ (i : ℕ) := fun i => by
    rw [frobTw_apply, map_pow]
  simp only [h1]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have := digits_sum_range_add_one n
  rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) n]
  omega

theorem norm_hwv_ne_zero [Algebra K k] (hK : Nat.card K = (2 ^ n) ^ 2) [Fintype ↥(LowerU K n)] :
    ∑ u : ↥(LowerU K n), TmodΦ (rhoL n) (fun i => frobTw K k i) (u : SU4 K n) *ᵥ
      hwv (rhoL n) k ≠ 0 := by
  intro h
  have h1 := congrArg (LamT n k) h
  rw [LamT_sum] at h1
  have h2 : LamT n k (0 : TIdx (rhoL n) → k) = 0 := by
    unfold LamT
    exact dotProduct_zero _
  rw [h2] at h1
  simp only [LamT_orbit, prod_frobTw] at h1
  rw [sum_Eu_pow_eq_one hK] at h1
  exact one_ne_zero h1

end Norm

end CFSG.HardMathSupport.U4FF
