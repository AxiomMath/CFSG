module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Range

public section

namespace CFSG.OddStandard.Seitz77

namespace Nat16

open Matrix MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {F : Type*} [Field F]

theorem fStr_symm (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (a : F) (w : Fin 2 → F) :
    fStr Φ a (Φ.symm w) = Φ.symm (a • w) := by
  show Φ.symm (a • Φ (Φ.symm w)) = Φ.symm (a • w)
  rw [AddEquiv.apply_symm_apply]

theorem isSemilinear_zero_of_commute (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F))
    (n : GL (Fin 8) (ZMod 2))
    (hlin : ∀ (a : F) (v : Fin 8 → ZMod 2), (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ fStr Φ a v =
      fStr Φ a ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v)) :
    IsSemilinear 0 (fun w => Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w)) := by
  intro a w
  show Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm (a • w)) =
    a ^ 2 ^ 0 • Φ ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ Φ.symm w)
  rw [← fStr_symm, hlin, fStr_apply, pow_zero, pow_one]

theorem exists_F16_structure (hF : Nat.card F = 16) (ρ : SL(2, F) →* GL (Fin 8) (ZMod 2))
    (hρ : Function.Injective ρ) {x₃ : SL(2, F)} (hx₃ : orderOf x₃ = 3)
    (hfpf : ∀ v : Fin 8 → ZMod 2, (ρ x₃ : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v = v → v = 0) :
    ∃ (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F))
      (φ : F →+* Module.End (ZMod 2) (Fin 8 → ZMod 2)),
      (∀ (a : F) (v : Fin 8 → ZMod 2), Φ (φ a v) = a • Φ v) ∧
      (∀ (g : SL(2, F)) (a : F) (v : Fin 8 → ZMod 2),
        (ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ φ a v =
          φ a ((ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v)) ∧
      (∀ (g : SL(2, F)) (v : Fin 8 → ZMod 2),
        Φ ((ρ g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) =
          (g : Matrix (Fin 2) (Fin 2) F) *ᵥ Φ v) ∧
      (∀ (c : F) (v : Fin 8 → ZMod 2),
        Φ ((ρ (uE c) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v) =
          ![Φ v 0 + c * Φ v 1, Φ v 1]) ∧
      (∀ n : GL (Fin 8) (ZMod 2), n ∈ Set.range ρ ↔
        ((∀ (a : F) (v : Fin 8 → ZMod 2), (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ φ a v =
          φ a ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v)) ∧ fDet Φ n = 1)) ∧
      (∀ n : GL (Fin 8) (ZMod 2),
        (∀ (a : F) (v : Fin 8 → ZMod 2), (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ φ a v =
          φ a ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v)) →
        (∃ m : ℕ, n ^ 2 ^ m = 1) → ∃ g : SL(2, F), ρ g = n) ∧
      (∀ n : GL (Fin 8) (ZMod 2), (∀ g : SL(2, F), ∃ g' : SL(2, F), n * ρ g * n⁻¹ = ρ g') →
        ∃ j : ZMod 4, ∀ (a : F) (v : Fin 8 → ZMod 2),
          (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ φ a v =
            φ (a ^ 2 ^ j.val) ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v)) := by
  obtain ⟨Φ, hΦ⟩ := natural_module hF ρ hρ hx₃ hfpf
  refine ⟨Φ, fStr Φ, fStr_apply Φ, fun g a v => fStr_commute hΦ g a v, hΦ, ?_, ?_, ?_, ?_⟩
  · intro c v
    rw [hΦ]
    ext i
    fin_cases i <;> simp [uE, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro n
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨fun a v => fStr_commute hΦ g a v, fDet_ρ hΦ g⟩
    · rintro ⟨hlin, hdet⟩
      exact exists_eq_of_linear_det hΦ n (isSemilinear_zero_of_commute Φ n hlin) hdet
  · intro n hlin ⟨m, hn⟩
    exact exists_eq_of_linear_pow hΦ hF n (isSemilinear_zero_of_commute Φ n hlin) hn
  · intro n hn
    obtain ⟨j, hj, hsl⟩ := normalizer_semilinear hF hΦ n hn
    refine ⟨(j : ZMod 4), fun a v => ?_⟩
    rw [ZMod.val_natCast_of_lt hj]
    have h1 : fStr Φ a v = Φ.symm (a • Φ v) := by
      rw [← fStr_symm, AddEquiv.symm_apply_apply]
    have h2 := hsl a (Φ v)
    simp only [AddEquiv.symm_apply_apply] at h2
    apply Φ.injective
    rw [h1, fStr_apply]
    exact h2

end Nat16

end CFSG.OddStandard.Seitz77
