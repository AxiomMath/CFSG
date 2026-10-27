module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInLULift
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniMat
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenTypeOne
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.GLTheoremA.T156.Uni

variable {K : Type} [Field K] {n d p : ℕ}

theorem norm_scalar_of_pow_eq_scalar (h : UnitaryFieldData 2 n K) [Finite K]
    (hd : 1 ≤ d) {M : GL (Fin d) K} {p : ℕ} (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    {c : Kˣ} (hc : M ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) c) :
    ∃ μ : Kˣ, c ^ (2 ^ n + 1) = μ ^ p := by
  classical
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hM
  haveI : CharP K 2 := h.charP
  set A : Matrix (Fin d) (Fin d) K := (M : Matrix (Fin d) (Fin d) K) with hA
  have huB : uAdj n A = (μ : K) • ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    have h1 : uAdj n A * A = (μ : K) • (1 : Matrix (Fin d) (Fin d) K) := by
      simpa only [uAdj_def, hA] using hμ
    calc uAdj n A = uAdj n A * (A * ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = (uAdj n A * A) * ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
          rw [Matrix.mul_assoc]
      _ = (μ : K) • ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
          rw [h1, Matrix.smul_mul, Matrix.one_mul]
  have hpow : ∀ k : ℕ, uAdj n (((M ^ k : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) =
      (uAdj n A) ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Units.val_one, uAdj_one]
    | succ k ih =>
      rw [pow_succ, Units.val_mul, uAdj_mul, ih, ← hA, pow_succ']
  have hscal : uAdj n (((Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K)) :
      Matrix (Fin d) (Fin d) K) =
      ((c : K) ^ 2 ^ n) • (1 : Matrix (Fin d) (Fin d) K) := by
    ext i j
    rw [uAdj_def, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_apply, Matrix.one_apply]
    by_cases hij : i = j
    · rw [hij]
      simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply, Matrix.diagonal, hij, Ne.symm hij]
  have hsmulpow : ∀ k : ℕ, (((μ : K) • ((M⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K)) ^ k) =
      (((μ : K) ^ k) • (((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ^ k)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ, pow_succ]
  have hinvpow : ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ^ p *
      (((M ^ p : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) = 1 := by
    have hc := (((Commute.refl (M : GL (Fin d) K)).inv_left).mul_pow p)
    rw [inv_mul_cancel, one_pow] at hc
    have hmat : ((M⁻¹ : GL (Fin d) K) ^ p * M ^ p : GL (Fin d) K) = 1 := hc.symm
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg Units.val hmat
  have hother : uAdj n (((M ^ p : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) *
      (((M ^ p : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) =
      ((μ : K) ^ p) • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [hpow p, huB, hsmulpow, Matrix.smul_mul, hinvpow]
  have hmain : uAdj n (((M ^ p : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) *
      (((M ^ p : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) =
      ((c : K) ^ (2 ^ n + 1)) • (1 : Matrix (Fin d) (Fin d) K) := by
    have hsc : (Matrix.scalar (Fin d) (c : K) : Matrix (Fin d) (Fin d) K) =
        (c : K) • (1 : Matrix (Fin d) (Fin d) K) := by
      ext i j
      by_cases hij : i = j
      · rw [hij]
        simp [Matrix.scalar_apply, Matrix.one_apply]
      · simp [Matrix.scalar_apply, Matrix.one_apply, hij]
    rw [hc, hscal, Matrix.GeneralLinearGroup.coe_scalar, hsc]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
    ext i j
    by_cases hij : i = j
    · rw [hij]
      simp [Matrix.smul_apply, Matrix.one_apply, pow_succ]
    · simp [Matrix.smul_apply, Matrix.one_apply, hij]
  have hEq : ((c : K) ^ (2 ^ n + 1)) • (1 : Matrix (Fin d) (Fin d) K) =
      ((μ : K) ^ p) • (1 : Matrix (Fin d) (Fin d) K) := hmain.symm.trans hother
  have hval : (c : K) ^ (2 ^ n + 1) = (μ : K) ^ p := by
    have h1 := congrFun (congrFun hEq ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h1
  exact ⟨Units.mk0 μ hμ0, Units.ext hval⟩

theorem exists_scalar_of_projConj_pow_eq_one (h : UnitaryFieldData 2 n K) [Finite K]
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime)
    {B : GL (Fin d) K} (hB : B ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hBN : B ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hBp : (TableB.projConj (unitarySU 2 n K d) ⟨B, hBN⟩) ^ p = 1) :
    ∃ c : Kˣ, B ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
  classical
  haveI := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := unitarySU 2 n K d with hH
  have hcard : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, show 2 * n = n * 2 by omega, ← pow_mul]
  have hperf : Group.IsPerfect H := isPerfect_statedSU (p := 2) (f := n) hcard hd hdq
  have hker : (LargeEvenProjMk H).ker ≤ Subgroup.center H :=
    TableBUE.ker_projMk_le_center
  let Bp : Subgroup.normalizer (H : Set (GL (Fin d) K)) :=
    ⟨B ^ p, Subgroup.pow_mem _ hBN p⟩
  have hproj : TableB.projConj H Bp = 1 := by
    change TableB.projConj H ((⟨B, hBN⟩ : Subgroup.normalizer (H : Set (GL (Fin d) K))) ^ p) = 1
    rw [map_pow, hBp]
  have hcomm : ∀ g ∈ H, B ^ p * g = g * B ^ p := by
    intro g hg
    have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq (LargeEvenProjMk H) hker
      hperf (H.normalizerMonoidHom Bp).toMonoidHom (MonoidHom.id H) (fun u => by
        have h1 := congrArg (fun ψ : MulAut (LargeEvenProj H) => ψ (LargeEvenProjMk H u)) hproj
        exact h1) ⟨g, hg⟩
    have h2 := congrArg Subtype.val key
    change (B ^ p * g * (B ^ p)⁻¹ : GL (Fin d) K) = g at h2
    calc B ^ p * g = B ^ p * g * (B ^ p)⁻¹ * B ^ p := by group
      _ = g * B ^ p := by rw [h2]
  obtain ⟨p', hp', hpq'⟩ := Nat.exists_prime_and_dvd (by
    have h1 : 1 ≤ n := h.one_le
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1
    omega : 2 ^ n + 1 ≠ 1)
  have hmem := TableBUE.mem_scalars_of_commute (n := n) (d := d) (K := K) h hp' hpq' hcomm
  rw [largeEvenScalars_def] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

theorem mem_scalars_of_projConj_eq_one (h : UnitaryFieldData 2 n K) [Finite K]
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    {X : GL (Fin d) K}
    (hXN : X ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hX : TableB.projConj (unitarySU 2 n K d) ⟨X, hXN⟩ = 1) :
    X ∈ LargeEvenScalars (Fin d) K := by
  classical
  haveI := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := unitarySU 2 n K d with hH
  have hcard : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, show 2 * n = n * 2 by omega, ← pow_mul]
  have hperf : Group.IsPerfect H := isPerfect_statedSU (p := 2) (f := n) hcard hd hdq
  have hker : (LargeEvenProjMk H).ker ≤ Subgroup.center H :=
    TableBUE.ker_projMk_le_center
  have hXcomm : ∀ g ∈ H, X * g = g * X := by
    intro g hg
    have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq (LargeEvenProjMk H) hker
      hperf (H.normalizerMonoidHom ⟨X, hXN⟩).toMonoidHom (MonoidHom.id H) (fun u => by
        have h1 := congrArg (fun ψ : MulAut (LargeEvenProj H) => ψ (LargeEvenProjMk H u)) hX
        exact h1) ⟨g, hg⟩
    have h2 := congrArg Subtype.val key
    change (X * g * X⁻¹ : GL (Fin d) K) = g at h2
    calc X * g = X * g * X⁻¹ * X := by group
      _ = g * X := by rw [h2]
  obtain ⟨p', hp', hpq'⟩ := Nat.exists_prime_and_dvd (by
    have h1 : 1 ≤ n := h.one_le
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1
    omega : 2 ^ n + 1 ≠ 1)
  exact TableBUE.mem_scalars_of_commute (n := n) (d := d) (K := K) h hp' hpq' hXcomm

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
