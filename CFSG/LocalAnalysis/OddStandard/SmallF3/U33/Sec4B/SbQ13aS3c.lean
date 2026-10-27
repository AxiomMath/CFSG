module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13aS3b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAmbient

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {B : Type} [Group B]

theorem s3_dich_aut (e : B ≃* Outside.Z4pow 2) {ρ lam ψ : MulAut B} (hρ3 : ρ ^ 3 = 1)
    (hfpf : ∀ b : B, ρ b = b → b = 1) (hlρ : lam * ρ * lam⁻¹ = ρ⁻¹) (hψρ : ψ * ρ = ρ * ψ)
    (hψl : ψ * lam = lam * ψ) :
    (∀ b : B, ψ b = b) ∨ (∀ b : B, ψ b = b⁻¹) := by
  have hR : S3RValid (s3Mat e ρ) := by
    refine ⟨?_, s3Mat_fixed e hfpf⟩
    rw [← s3Mat_mul e ρ ρ, ← s3Mat_mul e (ρ * ρ) ρ]
    have h : (ρ * ρ) * ρ = 1 := by
      rw [← hρ3, pow_three]
      group
    rw [h, s3Mat_one]
  have hC : S3Inverts (s3Mat e ρ) (s3Mat e lam) := by
    have hρinv : ρ⁻¹ = ρ * ρ := by
      have h : ρ * (ρ * ρ) = 1 := by
        rw [← hρ3, pow_three]
      exact inv_eq_of_mul_eq_one_right h
    have hlρ1 : lam * ρ = ρ⁻¹ * lam := (mul_inv_eq_iff_eq_mul).mp hlρ
    have hlρ2 : lam * ρ = (ρ * ρ) * lam := by rw [hlρ1, hρinv]
    show s3mul (s3Mat e lam) (s3Mat e ρ)
        = s3mul (s3mul (s3Mat e ρ) (s3Mat e ρ)) (s3Mat e lam)
    rw [← s3Mat_mul e lam ρ, ← s3Mat_mul e ρ ρ, ← s3Mat_mul e (ρ * ρ) lam]
    rw [hlρ2]
  have hCu : S3DetUnit (s3Mat e lam) := by
    apply s3_detUnit_of_mul (Y := s3Mat e lam⁻¹)
    rw [← s3Mat_mul e lam lam⁻¹, mul_inv_cancel, s3Mat_one]
  have hPu : S3DetUnit (s3Mat e ψ) := by
    apply s3_detUnit_of_mul (Y := s3Mat e ψ⁻¹)
    rw [← s3Mat_mul e ψ ψ⁻¹, mul_inv_cancel, s3Mat_one]
  have hP : S3Comm (s3Mat e ρ) (s3Mat e lam) (s3Mat e ψ) := by
    refine ⟨?_, ?_⟩
    · rw [← s3Mat_mul e ψ ρ, hψρ, s3Mat_mul e ρ ψ]
    · rw [← s3Mat_mul e ψ lam, hψl, s3Mat_mul e lam ψ]
  rcases s3_matrix hR hC hCu hP hPu with h | h
  · exact Or.inl (eq_one_of_s3Mat e h)
  · exact Or.inr (inv_of_s3Mat e h)

variable {G : Type} [Group G] [Finite G]

theorem s3_dichotomy {A : Subgroup G} (hA : IsZ4pow 2 A) {rho lam psi : G}
    (hr : rho ∈ normalizer (A : Set G)) (hl : lam ∈ normalizer (A : Set G))
    (hp : psi ∈ normalizer (A : Set G)) (hrho3 : rho ^ 3 = 1)
    (hfpf : ∀ a ∈ A, rho * a * rho⁻¹ = a → a = 1) (hlr : lam * rho * lam⁻¹ = rho⁻¹)
    (hpr : ∀ a ∈ A, psi * (rho * a * rho⁻¹) * psi⁻¹ = rho * (psi * a * psi⁻¹) * rho⁻¹)
    (hpl : ∀ a ∈ A, psi * (lam * a * lam⁻¹) * psi⁻¹ = lam * (psi * a * psi⁻¹) * lam⁻¹) :
    (∀ a ∈ A, psi * a * psi⁻¹ = a) ∨ (∀ a ∈ A, psi * a * psi⁻¹ = a⁻¹) := by
  obtain ⟨e⟩ := hA
  have hρ3 : (Outside.conjAut A rho hr : MulAut A) ^ 3 = 1 := by
    rw [← Outside.conjAut_pow A hr 3 (pow_mem hr 3)]
    ext b
    rw [Outside.conjAut_coe, MulAut.one_apply, hrho3]
    group
  have hfpf' : ∀ b : A, Outside.conjAut A rho hr b = b → b = 1 := by
    intro b hb
    apply Subtype.ext
    have hb' : rho * (b : G) * rho⁻¹ = (b : G) := by
      have := congrArg (fun x : A => (x : G)) hb
      simpa [Outside.conjAut_coe] using this
    exact hfpf (b : G) b.2 hb'
  have hlρ' : Outside.conjAut A lam hl * Outside.conjAut A rho hr
      * (Outside.conjAut A lam hl)⁻¹ = (Outside.conjAut A rho hr)⁻¹ := by
    rw [← Outside.conjAut_inv A hl (inv_mem hl)]
    rw [← Outside.conjAut_mul A hl hr (mul_mem hl hr)]
    rw [← Outside.conjAut_mul A (mul_mem hl hr) (inv_mem hl)
      (mul_mem (mul_mem hl hr) (inv_mem hl))]
    rw [← Outside.conjAut_inv A hr (inv_mem hr)]
    ext b
    simp only [Outside.conjAut_coe, hlr]
  have hψρ' : Outside.conjAut A psi hp * Outside.conjAut A rho hr
      = Outside.conjAut A rho hr * Outside.conjAut A psi hp := by
    ext b
    simp only [MulAut.mul_apply, Outside.conjAut_coe]
    exact hpr (b : G) b.2
  have hψl' : Outside.conjAut A psi hp * Outside.conjAut A lam hl
      = Outside.conjAut A lam hl * Outside.conjAut A psi hp := by
    ext b
    simp only [MulAut.mul_apply, Outside.conjAut_coe]
    exact hpl (b : G) b.2
  rcases s3_dich_aut e hρ3 hfpf' hlρ' hψρ' hψl' with h | h
  · left
    intro a ha
    have h1 := congrArg (fun x : A => (x : G)) (h ⟨a, ha⟩)
    simpa [Outside.conjAut_coe] using h1
  · right
    intro a ha
    have h1 := congrArg (fun x : A => (x : G)) (h ⟨a, ha⟩)
    simp only [Outside.conjAut_coe, Subgroup.coe_inv] at h1
    exact h1

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
