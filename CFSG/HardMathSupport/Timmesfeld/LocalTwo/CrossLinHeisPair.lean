module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisRed
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo

variable {n : ℕ} {F : Type} [Field F] [Finite F]

local notation "sc" => GeneralLinearGroup.scalar (Fin n)

theorem exists_split_pair (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A B : GL (Fin n) F} {z a b : Fˣ} (hAB : A * B = sc z * (B * A)) (hzp : z ^ p = 1)
    (hz1 : z ≠ 1) (hA : A ^ p = sc a) (hB : B ^ p = sc b) :
    ∃ (S T : GL (Fin n) F) (c w : Fˣ), S ^ p = 1 ∧ T ^ p = sc c ∧ S * T = sc w * (T * S) ∧
      w ^ p = 1 ∧ w ≠ 1 ∧
      conjAut n F S ∈ Subgroup.closure {conjAut n F A, conjAut n F B} ∧
      conjAut n F T ∈ Subgroup.closure {conjAut n F A, conjAut n F B} := by
  have hcen : ∀ (u : Fˣ) (g : GL (Fin n) F), sc u * g = g * sc u := fun u g =>
    GeneralLinearGroup.scalar_commute u g
  have hc : ∀ (u : Fˣ) (g : GL (Fin n) F), Commute (sc u) g := fun u g => hcen u g
  have hsc : ∀ u v : Fˣ, Commute (sc u) (sc v) := fun u v => (Commute.all u v).map _
  have hcA : conjAut n F A ∈ Subgroup.closure {conjAut n F A, conjAut n F B} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hcB : conjAut n F B ∈ Subgroup.closure {conjAut n F A, conjAut n F B} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  by_cases ha : ∃ e : Fˣ, e ^ p = a
  ·
    obtain ⟨e, he⟩ := ha
    refine ⟨sc e⁻¹ * A, B, b, z, ?_, hB, ?_, hzp, hz1, ?_, hcB⟩
    · rw [(show Commute (sc e⁻¹) A from hcen _ A).mul_pow, hA, ← map_pow, ← map_mul, inv_pow,
        he, inv_mul_cancel, map_one]
    · calc sc e⁻¹ * A * B = sc e⁻¹ * (A * B) := by rw [mul_assoc]
        _ = sc e⁻¹ * (sc z * (B * A)) := by rw [hAB]
        _ = sc z * (B * (sc e⁻¹ * A)) := by
            rw [(hsc e⁻¹ z).left_comm, (hc e⁻¹ B).left_comm]
    · rw [map_mul, conjAut_scalar, one_mul]
      exact hcA
  by_cases hb : ∃ e : Fˣ, e ^ p = b
  ·
    obtain ⟨e, he⟩ := hb
    refine ⟨sc e⁻¹ * B, A, a, z⁻¹, ?_, hA, ?_, by rw [inv_pow, hzp, inv_one], by simpa using hz1,
      ?_, hcA⟩
    · rw [(show Commute (sc e⁻¹) B from hcen _ B).mul_pow, hB, ← map_pow, ← map_mul, inv_pow,
        he, inv_mul_cancel, map_one]
    · have hBA : B * A = sc z⁻¹ * (A * B) := by
        rw [hAB, map_inv, ← mul_assoc, inv_mul_cancel, one_mul]
      calc sc e⁻¹ * B * A = sc e⁻¹ * (B * A) := by rw [mul_assoc]
        _ = sc e⁻¹ * (sc z⁻¹ * (A * B)) := by rw [hBA]
        _ = sc z⁻¹ * (A * (sc e⁻¹ * B)) := by
            rw [(hsc e⁻¹ z⁻¹).left_comm, (hc e⁻¹ A).left_comm]
    · rw [map_mul, conjAut_scalar, one_mul]
      exact hcB
  ·
    obtain ⟨i, e, he⟩ := exists_pthpower_mul hp a b ha
    have hBA : B * A = sc z⁻¹ * (A * B) := by
      rw [hAB, map_inv, ← mul_assoc, inv_mul_cancel, one_mul]
    have hAiB : A ^ i * B = sc (z ^ i) * (B * A ^ i) := by
      have h1 := pow_mul_comm_central (X := B) (Y := A) (z := sc z⁻¹)
        (fun g => hcen _ g) hBA i
      rw [map_inv, inv_inv, ← map_pow] at h1
      exact h1
    have hzi : (sc (z ^ i)) ^ p = 1 := by
      rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hzp, one_pow, map_one]
    have hpow : (A ^ i * B) ^ p = sc (a ^ i) * sc b := by
      rw [mul_pow_prime_central (fun g => hcen _ g) hAiB hp hp2 hzi, ← pow_mul, mul_comm, pow_mul,
        hA, ← map_pow, hB]
    refine ⟨sc e⁻¹ * (A ^ i * B), A, a, z⁻¹, ?_, hA, ?_, by rw [inv_pow, hzp, inv_one],
      by simpa using hz1, ?_, hcA⟩
    · rw [(show Commute (sc e⁻¹) (A ^ i * B) from hcen _ _).mul_pow, hpow, ← map_pow, ← map_mul,
        ← map_mul, inv_pow, he, inv_mul_cancel, map_one]
    · have hAAi : A ^ i * A = A * A ^ i := (pow_succ A i).symm.trans (pow_succ' A i)
      calc sc e⁻¹ * (A ^ i * B) * A = sc e⁻¹ * (A ^ i * (B * A)) := by simp only [mul_assoc]
        _ = sc e⁻¹ * (A ^ i * (sc z⁻¹ * (A * B))) := by rw [hBA]
        _ = sc e⁻¹ * (sc z⁻¹ * (A ^ i * (A * B))) := by
            rw [((hc z⁻¹ (A ^ i)).symm).left_comm]
        _ = sc e⁻¹ * (sc z⁻¹ * (A * (A ^ i * B))) := by
            rw [← mul_assoc (A ^ i), hAAi, mul_assoc]
        _ = sc z⁻¹ * (A * (sc e⁻¹ * (A ^ i * B))) := by
            rw [(hsc e⁻¹ z⁻¹).left_comm, (hc e⁻¹ A).left_comm]
    · rw [map_mul, conjAut_scalar, one_mul, map_mul, map_pow]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hcA i) hcB

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
