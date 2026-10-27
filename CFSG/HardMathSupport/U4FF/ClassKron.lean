module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bInvol

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open CFSG.QuasithinUnique.Setup.X7 (permMat)
open CFSG.QuasithinUnique.Setup.X7b
  (exists_perm_conj rank_permMat_sub_one rank_conj_eq two_mul_rank_le)

@[expose] def kronDep {k : Type*} [Field k] {ι : Type*} [Fintype ι] (κ : ι → Type*)
    [∀ i, Fintype (κ i)] (z : (i : ι) → Matrix (κ i) (κ i) k) :
    Matrix ((i : ι) → κ i) ((i : ι) → κ i) k :=
  Matrix.of fun x y => ∏ i, z i (x i) (y i)

section Kron

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]

theorem kronDep_apply (z : (i : ι) → Matrix (κ i) (κ i) k) (x y : (i : ι) → κ i) :
    kronDep κ z x y = ∏ i, z i (x i) (y i) := rfl

theorem kronDep_mul [DecidableEq ι] (A B : (i : ι) → Matrix (κ i) (κ i) k) :
    kronDep κ (fun i => A i * B i) = kronDep κ A * kronDep κ B :=
  CFSG.QuasithinUnique.Setup.X7a.kron_mul A B

theorem kronDep_one [DecidableEq ι] [∀ i, DecidableEq (κ i)] :
    kronDep κ (fun i => (1 : Matrix (κ i) (κ i) k)) = 1 := by
  ext x y
  simp only [kronDep_apply, Matrix.one_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

theorem kronDep_permMat [DecidableEq ι] [∀ i, DecidableEq (κ i)]
    (σ : (i : ι) → Equiv.Perm (κ i)) :
    kronDep κ (fun i => permMat k (σ i)) = permMat k (Equiv.piCongrRight σ) := by
  ext y x
  simp only [kronDep_apply, permMat, Matrix.of_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

end Kron

section Rank

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]

theorem rank_kronDep_sub_one [CharP k 2] [∀ i, Nonempty (κ i)] [DecidableEq ι]
    [∀ i, DecidableEq (κ i)] (z : (i : ι) → Matrix (κ i) (κ i) k) (hz : ∀ i, z i * z i = 1) :
    (kronDep κ z - 1).rank * 2 + ∏ i, (Fintype.card (κ i) - 2 * (z i - 1).rank) =
      ∏ i, Fintype.card (κ i) := by
  classical
  choose σ P Q hσ hPQ hQP hzP using fun i => exists_perm_conj (hz i)
  have hz' : ∀ i, z i - 1 = P i * (permMat k (σ i) - 1) * Q i := fun i => by
    have h1 : z i = P i * permMat k (σ i) * Q i := by
      calc z i = z i * (P i * Q i) := by rw [hPQ, Matrix.mul_one]
        _ = (z i * P i) * Q i := by rw [Matrix.mul_assoc]
        _ = P i * permMat k (σ i) * Q i := by rw [hzP]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ, ← h1]
  have hfix : ∀ i, Fintype.card {y // σ i y = y} = Fintype.card (κ i) - 2 * (z i - 1).rank :=
    fun i => by
      have h1 := rank_permMat_sub_one (k := k) (σ i) (hσ i)
      rw [hz' i, rank_conj_eq _ _ _ (hQP i)]
      omega
  have hPk : kronDep κ P * kronDep κ Q = 1 := by
    rw [← kronDep_mul]
    simp only [hPQ]
    exact kronDep_one
  have hQk : kronDep κ Q * kronDep κ P = 1 := by
    rw [← kronDep_mul]
    simp only [hQP]
    exact kronDep_one
  have hzk : kronDep κ z * kronDep κ P = kronDep κ P * permMat k (Equiv.piCongrRight σ) := by
    rw [← kronDep_permMat, ← kronDep_mul, ← kronDep_mul]
    exact congrArg (kronDep κ) (funext hzP)
  have hz'' : kronDep κ z - 1 =
      kronDep κ P * (permMat k (Equiv.piCongrRight σ) - 1) * kronDep κ Q := by
    have h1 : kronDep κ z = kronDep κ P * permMat k (Equiv.piCongrRight σ) * kronDep κ Q := by
      calc kronDep κ z = kronDep κ z * (kronDep κ P * kronDep κ Q) := by
            rw [hPk, Matrix.mul_one]
        _ = (kronDep κ z * kronDep κ P) * kronDep κ Q := by rw [Matrix.mul_assoc]
        _ = kronDep κ P * permMat k (Equiv.piCongrRight σ) * kronDep κ Q := by rw [hzk]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPk, ← h1]
  have hσk : Equiv.piCongrRight σ * Equiv.piCongrRight σ = 1 := by
    ext x i
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Equiv.piCongrRight_apply]
    have := congrArg (fun p : Equiv.Perm (κ i) => p (x i)) (hσ i)
    simpa [Equiv.Perm.mul_apply] using this
  have h2 := rank_permMat_sub_one (k := k) (Equiv.piCongrRight σ) hσk
  have hcardfix : Fintype.card {x : (i : ι) → κ i // Equiv.piCongrRight σ x = x} =
      ∏ i, Fintype.card {y // σ i y = y} := by
    rw [← Fintype.card_pi]
    refine Fintype.card_congr ?_
    refine (Equiv.subtypeEquivRight fun x => ?_).trans
      (Equiv.subtypePiEquivPi (p := fun i y => σ i y = y))
    simp [funext_iff]
  rw [hcardfix] at h2
  simp only [hfix] at h2
  rw [hz'', rank_conj_eq _ _ _ hQk]
  rw [Fintype.card_pi] at h2
  exact h2

end Rank

section Binary

universe u

@[expose] def kronBoolFam (κ μ : Type u) : Bool → Type u := fun b => cond b κ μ

instance kronBoolFam_fintype {κ μ : Type u} [Fintype κ] [Fintype μ] (b : Bool) :
    Fintype (kronBoolFam κ μ b) := by
  cases b
  exacts [inferInstanceAs (Fintype μ), inferInstanceAs (Fintype κ)]

instance kronBoolFam_decidableEq {κ μ : Type u} [DecidableEq κ] [DecidableEq μ] (b : Bool) :
    DecidableEq (kronBoolFam κ μ b) := by
  cases b
  exacts [inferInstanceAs (DecidableEq μ), inferInstanceAs (DecidableEq κ)]

instance kronBoolFam_nonempty {κ μ : Type u} [Nonempty κ] [Nonempty μ] (b : Bool) :
    Nonempty (kronBoolFam κ μ b) := by
  cases b
  exacts [inferInstanceAs (Nonempty μ), inferInstanceAs (Nonempty κ)]

end Binary

end CFSG.HardMathSupport.U4FF
