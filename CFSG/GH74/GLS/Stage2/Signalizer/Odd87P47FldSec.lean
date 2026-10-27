module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47FldSub
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Field

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47Fld

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] noncomputable def subEquiv {F : Type} [Field F] (F0 : Subfield F) :
    projectiveSL 3 ↥F0 ≃* ↥(subRange F0) :=
  MonoidHom.ofInjective (subEmb_injective F0)

theorem field_section {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (α : MulAut (projectiveSL 3 F)) (hα : α * α = 1)
    (A : GL (Fin 3) F) (σ : F ≃+* F) (hσ : σ ≠ 1) (hαeq : α = conjAut 3 F A * fieldAut 3 F σ) :
    ∃ (F0 : Type) (_ : Field F0) (_ : Finite F0) (_ : CharP F0 p) (n : ℕ), 1 ≤ n ∧
      Nat.card F0 = p ^ n ∧
      ∃ Q : Subgroup (projectiveSL 3 F), Nonempty (projectiveSL 3 F0 ≃* ↥Q) ∧ ⁅Q, Q⁆ = Q ∧
        (∀ s ∈ Q, α s = s) ∧ ∀ x, α x = x → x ∈ normalizer (Q : Set (projectiveSL 3 F)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hsq : (conjAut 3 F A * fieldAut 3 F σ) ^ 2 = 1 := by rw [← hαeq, sq]; exact hα
  obtain ⟨-, -, H, hH⟩ := linear_field_involution_descent hp hf hcard (le_refl 3) A σ hσ hsq
  have : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have : CharP ↥(fixField σ) p := inferInstance
  have hF0card : ∃ n : ℕ+, Nat.card ↥(fixField σ) = p ^ (n : ℕ) := by
    have := Fintype.ofFinite ↥(fixField σ)
    obtain ⟨n, -, hn⟩ := FiniteField.card ↥(fixField σ) p
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨n, hn⟩ := hF0card
  refine ⟨↥(fixField σ), inferInstance, inferInstance, inferInstance, n, n.pos, hn, ?_⟩
  let γ : projectiveSL 3 F ≃* projectiveSL 3 F := conjAut 3 F H
  let e1 : ↥(subRange (fixField σ)) ≃* ↥((subRange (fixField σ)).map γ.toMonoidHom) :=
    (subRange (fixField σ)).equivMapOfInjective γ.toMonoidHom γ.injective
  have hperf : Group.IsPerfect ↥((subRange (fixField σ)).map γ.toMonoidHom) := by
    have := isPerfect_projectiveSL3_fl3 ↥(fixField σ)
    exact Group.IsPerfect.ofSurjective (f := ((subEquiv (fixField σ)).trans e1).toMonoidHom)
      ((subEquiv (fixField σ)).trans e1).surjective
  refine ⟨(subRange (fixField σ)).map γ.toMonoidHom, ⟨(subEquiv (fixField σ)).trans e1⟩,
    Subgroup.isPerfect_iff.1 hperf, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    rw [hαeq, hH, MulAut.mul_apply, MulAut.mul_apply]
    change γ (fieldAut 3 F σ (γ.symm (γ q))) = γ q
    rw [MulEquiv.symm_apply_apply, fieldAut_fix_subRange σ hq]
  · intro x hx
    have h1 : α x = γ (fieldAut 3 F σ (γ.symm x)) := by
      rw [hαeq, hH, MulAut.mul_apply, MulAut.mul_apply]
      rfl
    have hfix : fieldAut 3 F σ (γ.symm x) = γ.symm x := by
      rw [h1] at hx
      simpa using congrArg γ.symm hx
    have hn := mem_normalizer_subRange σ hfix
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have := (Subgroup.mem_normalizer_iff.1 hn) (γ.symm h)
    simpa [map_mul, map_inv] using this

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47Fld
