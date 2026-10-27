module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import CFSG.GH74.GLS.Stage2.OddAut.HeisField

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Aut

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem mul_dualAut_mem_of_not_mem (hn : 3 ≤ n) {x : MulAut (projectiveSL n K)}
    (hx : x ∉ semilinearAutGroup n K) : x * dualAut n K ∈ semilinearAutGroup n K := by
  have hR : x ∈ standardAutGroup n K := by rw [(automorphism_generation hn).1]; trivial
  exact (mem_or_mul_dualAut_mem hR).resolve_left hx

theorem inv_mul_mem_semilinear (hn : 3 ≤ n) {x y : MulAut (projectiveSL n K)}
    (hx : x ∉ semilinearAutGroup n K) (hy : y ∉ semilinearAutGroup n K) :
    x⁻¹ * y ∈ semilinearAutGroup n K := by
  have hδδ : dualAut n K * dualAut n K = 1 :=
    (standard_automorphism_transport (K := K) (n := n)).2.2.2.1
  have h : x⁻¹ * y = dualAut n K * ((x * dualAut n K)⁻¹ * (y * dualAut n K)) * dualAut n K := by
    rw [show dualAut n K * ((x * dualAut n K)⁻¹ * (y * dualAut n K)) * dualAut n K =
      x⁻¹ * y * (dualAut n K * dualAut n K) by group, hδδ, mul_one]
  rw [h]
  exact dualAut_mul_mul_dualAut_mem (mul_mem (inv_mem (mul_dualAut_mem_of_not_mem hn hx))
    (mul_dualAut_mem_of_not_mem hn hy))

end Aut

section Square

variable {K : Type} [Field K] {n : ℕ}

theorem mul_self_mul_involution {G : Type*} [Group G] (c f d : G) (h : d * d = 1) :
    c * f * d * (c * f * d) = c * f * (d * c * d) * (d * f * d) := by
  rw [show c * f * (d * c * d) * (d * f * d) = c * f * d * c * (d * d) * f * d by group, h]
  group

theorem mul_self_eq_conj_field {x : MulAut (projectiveSL n K)} {C : GL (Fin n) K} {σ : K ≃+* K}
    (hx : x * dualAut n K = conjAut n K C * fieldAut n K σ) :
    x * x = conjAut n K (C * GeneralLinearGroup.map (σ : K →+* K)
      (GeneralLinearGroup.inverseTranspose C)) * fieldAut n K (σ * σ) := by
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hδδ : dualAut n K * dualAut n K = 1 := htrans.2.2.2.1
  have hxe : x = conjAut n K C * fieldAut n K σ * dualAut n K := by
    rw [← hx, mul_assoc, hδδ, mul_one]
  calc x * x = conjAut n K C * fieldAut n K σ * (dualAut n K * conjAut n K C * dualAut n K) *
        (dualAut n K * fieldAut n K σ * dualAut n K) := by
        rw [hxe]
        exact mul_self_mul_involution _ _ _ hδδ
    _ = conjAut n K C * fieldAut n K σ *
        (conjAut n K (GeneralLinearGroup.inverseTranspose C) * fieldAut n K σ) := by
        rw [htrans.2.2.2.2.1 C, htrans.2.2.2.2.2.1 σ, mul_assoc (conjAut n K C * fieldAut n K σ)]
    _ = _ := conjAut_mul_fieldAut_mul C (GeneralLinearGroup.inverseTranspose C) σ σ

end Square

section Frobenius

theorem exists_frobenius_galoisField {f : ℕ} (hf : 1 ≤ f)
    (σ : GaloisField 2 f ≃+* GaloisField 2 f) : ∃ k : ℕ, ∀ a, σ a = a ^ 2 ^ k := by
  obtain ⟨k, -, hk⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow Nat.prime_two hf
    (GaloisField.card 2 f (by omega)) σ
  exact ⟨k, hk⟩

end Frobenius

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Lin
