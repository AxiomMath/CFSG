module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODUnitaryMono
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291NilpTwist

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N

open Polynomial Matrix CFSG.ClassicalGroups.Unitary TorusU CFSG.Open
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid)
open CFSG.LieType.Universal.Unitary (conjTr SUid)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LocalAnalysis.RankFourTheoremC.I294OD

theorem exists_orbit_basis {K : Type} [Field K] [Finite K] {r e0 p : ℕ} [Fact r.Prime] [CharP K r]
    [hpf : Fact p.Prime] {c : K} [hirr : Fact (Irreducible (X ^ p - C c : K[X]))]
    {σ : K ≃+* K} {B : GL (Fin p) K} (S : OdSetup r e0 p c σ B) (hσ : IsUnitaryInvolution σ) :
    ∃ b : Fin p → Fin p → K, (∀ a a', herm σ (b a) (b a') = if a = a' then 1 else 0) ∧
      ∀ a : Fin p, ((B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *ᵥ b a =
        (if (a : ℕ) + 1 < p then (1 : K) else c) • b (a + 1) := by
  obtain ⟨w, hw⟩ := od_exists_orbit_family S hσ 1 (Nat.mul_one p)
  refine ⟨fun a => odBv B ((a : ℕ) : ℤ) (w 0), fun a a' => ?_, fun a => ?_⟩
  · rw [hw 0 0 a a']
    simp
  · have hval : ((a + 1 : Fin p) : ℕ) = ((a : ℕ) + 1) % p := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hpf.out.one_lt]
    by_cases hj : (a : ℕ) + 1 < p
    · simp only
      rw [if_pos hj, one_smul, hval, Nat.mod_eq_of_lt hj, odBv_succ]
    · have hjp : (a : ℕ) + 1 = p := by have := a.2; omega
      simp only
      rw [if_neg hj, hval, hjp, Nat.mod_self, Nat.cast_zero, odBv_zero, ← odBv_succ, hjp,
        odBv_p S.hBp]

theorem exists_twist_uni {K : Type} [Field K] {p : ℕ} [NeZero p] (hp : p.Prime) (hodd : Odd p)
    {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c) {B : Matrix (Fin p) (Fin p) K}
    {b : Fin p → Fin p → K} {u : Fin p → K}
    (hb : ∀ a a', herm σ (b a) (b a') = if a = a' then 1 else 0)
    (hBb : ∀ a, B *ᵥ b a = u a • b (a + 1)) {τ : K} (hτ : τ ^ p = 1) (hστ : σ τ * τ = 1) :
    ∃ Φ : Matrix (Fin p) (Fin p) K, conjTr σ Φ * Φ = 1 ∧ Φ.det = 1 ∧ Φ ^ p = 1 ∧
      B * Φ = τ⁻¹ • (Φ * B) := by
  set π : Equiv.Perm (Fin p) := Equiv.addRight (1 : Fin p) with hπ
  set P := colMatrix b with hPdef
  have hP : conjTr σ P * P = 1 := conjTr_colMatrix_mul_self hb
  have hPQ : P * conjTr σ P = 1 := mul_conjTr_self hP
  have hBP : B * P = P * (Matrix.of fun i j => if i = π j then u j else 0) :=
    od_mul_colMatrix_mono (π := π) hBb
  have hNd := od_monomial_diag u π
  set d : Fin p → K := fun j => τ ^ (j : ℕ) with hd
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hτ
    exact zero_ne_one hτ
  have hdsucc : ∀ j : Fin p, d (j + 1) = τ * d j := by
    intro j
    simp only [hd]
    have hval : ((j + 1 : Fin p) : ℕ) = ((j : ℕ) + 1) % p := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hp.one_lt]
    rw [hval]
    by_cases h : (j : ℕ) + 1 < p
    · rw [Nat.mod_eq_of_lt h, pow_succ']
    · have h1 : (j : ℕ) + 1 = p := by have := j.2; omega
      rw [← pow_succ', h1, Nat.mod_self, pow_zero, hτ]
  have hdπ : (fun i => d (π.symm i)) = τ⁻¹ • d := by
    funext i
    have h1 := hdsucc (π.symm i)
    have h2 : (π.symm i) + 1 = i := by simp [hπ]
    rw [h2] at h1
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1, ← mul_assoc, inv_mul_cancel₀ hτ0, one_mul]
  have hT : ∀ j, σ (d j) * d j = 1 := fun j => by
    simp only [hd]
    rw [map_pow, ← mul_pow, hστ, one_pow]
  refine ⟨conjDiag σ P d, conjTr_conjDiag_mul_self hσ hP hT, ?_, ?_, ?_⟩
  · rw [det_conjDiag hP]
    exact prod_pow_fin_eq_one hodd hτ
  · have h1 : ∀ k : ℕ, conjDiag σ P d ^ k = conjDiag σ P (d ^ k) := by
      intro k
      induction k with
      | zero => rw [pow_zero, pow_zero, conjDiag_one hP]
      | succ k ih => rw [pow_succ, ih, conjDiag_mul hP, ← pow_succ]
    have h2 : d ^ p = 1 := by
      funext j
      simp only [hd, Pi.pow_apply, Pi.one_apply]
      rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow]
    rw [h1, h2, conjDiag_one hP]
  · have h := od_mono_conj hPQ hP hBP hNd d
    change B * conjDiag σ P d = conjDiag σ P (fun i => d (π.symm i)) * B at h
    rw [hdπ] at h
    have h3 : conjDiag σ P (τ⁻¹ • d) = τ⁻¹ • conjDiag σ P d := by
      unfold conjDiag
      rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
    rw [h3, Matrix.smul_mul] at h
    exact h

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N
