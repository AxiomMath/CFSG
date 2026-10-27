module

public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OFLa
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowOData

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIL

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

theorem exists_sq_add_sq {F : Type} [Field F] [Fintype F] (hq : Fintype.card F % 2 = 1)
    (d : F) : ∃ s t : F, s ^ 2 + t ^ 2 = d := by
  obtain ⟨s, t, h⟩ := OFL.exists_norm_eq hq (neg_ne_zero.mpr one_ne_zero) d
  exact ⟨s, t, by rw [← h]; ring⟩

variable {k : Type} [Field k]

section G0

variable (δ : k)

@[expose] def g0 : SpecialLinearGroup (Fin 2) (extension δ) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem coe_g0 : ((g0 δ : SpecialLinearGroup (Fin 2) (extension δ)) :
    Matrix (Fin 2) (Fin 2) (extension δ)) = !![0, 1; -1, 0] := rfl

theorem two_ne_zero_ext (h2 : (2 : k) ≠ 0) : (2 : extension δ) ≠ 0 := by
  intro h
  apply h2
  have := congrArg QuadraticAlgebra.re h
  rwa [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.re_zero] at this

theorem card_ext_odd [Fintype k] (hq : Fintype.card k % 2 = 1) [Fintype (extension δ)] :
    Fintype.card (extension δ) % 2 = 1 := by
  rw [← Nat.card_eq_fintype_card, extension_card, Nat.card_eq_fintype_card, Nat.pow_mod, hq]

end G0

theorem exists_conj_g0 [Fintype k] (hq : Fintype.card k % 2 = 1) (h2 : (2 : k) ≠ 0) {δ : k}
    (hδ : ¬ IsSquare δ) (g : SpecialLinearGroup (Fin 2) (extension δ)) (hg : g * g = -1) :
    ∃ a : SpecialLinearGroup (Fin 2) (extension δ), a * g0 δ = g * a := by
  have : Fact (¬ IsSquare δ) := ⟨hδ⟩
  have : Finite (extension δ) := Finite.of_equiv (k × k) (QuadraticAlgebra.equivProd δ 0).symm
  let : Fintype (extension δ) := Fintype.ofFinite _
  have hqE := card_ext_odd δ hq
  have h2E := two_ne_zero_ext δ h2
  have hgg : (g : Matrix (Fin 2) (Fin 2) (extension δ)) * g = -1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hg, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
  have hdet0 := g.2
  obtain ⟨α, β, γ, ε, hgm⟩ : ∃ α β γ ε : extension δ,
      (g : Matrix (Fin 2) (Fin 2) (extension δ)) = !![α, β; γ, ε] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hgm] at hgg hdet0
  rw [Matrix.det_fin_two_of] at hdet0
  have e00 := congrFun (congrFun hgg 0) 0
  have e01 := congrFun (congrFun hgg 0) 1
  have e10 := congrFun (congrFun hgg 1) 0
  have e11 := congrFun (congrFun hgg 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), neg_zero, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one] at e00 e01 e10 e11
  have htr : α + ε = 0 := by
    have : (α + ε) ^ 2 = 0 := by linear_combination e00 + e11 + 2 * hdet0
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have key : ∀ u₀ u₁ : extension δ,
      (α * u₀ + β * u₁) * u₁ - u₀ * (γ * u₀ + ε * u₁) = 1 →
      ∃ a : SpecialLinearGroup (Fin 2) (extension δ), a * g0 δ = g * a := by
    intro u₀ u₁ hu
    let a : SpecialLinearGroup (Fin 2) (extension δ) :=
      ⟨!![α * u₀ + β * u₁, u₀; γ * u₀ + ε * u₁, u₁], by rw [Matrix.det_fin_two_of]; exact hu⟩
    have hav : (a : Matrix (Fin 2) (Fin 2) (extension δ)) =
        !![α * u₀ + β * u₁, u₀; γ * u₀ + ε * u₁, u₁] := rfl
    refine ⟨a, ?_⟩
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_g0, hgm, hav]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-u₀) * e00 - u₁ * e01
    · linear_combination (-u₀) * e10 - u₁ * e11
  by_cases hβ0 : β = 0
  · subst hβ0
    have hα2 : α * α = -1 := by rw [zero_mul, add_zero] at e00; exact e00
    have hα0 : α ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hα2
      exact one_ne_zero (neg_eq_zero.mp hα2.symm)
    have hu : 2 * α * ((1 + γ) / (2 * α)) = 1 + γ := mul_div_cancel₀ _ (mul_ne_zero h2E hα0)
    refine key 1 ((1 + γ) / (2 * α)) ?_
    linear_combination hu - ((1 + γ) / (2 * α)) * htr
  · obtain ⟨s, t, hst⟩ := exists_sq_add_sq hqE β
    have hw : β * ((s - α * t) / β) = s - α * t := mul_div_cancel₀ _ hβ0
    refine key t ((s - α * t) / β) ?_
    apply mul_left_cancel₀ hβ0
    linear_combination (β * ((s - α * t) / β) + s + α * t) * hw + hst - t ^ 2 * e00 -
      β * t * ((s - α * t) / β) * htr

theorem mul_self_eq_neg_one_of_conjAut {m : ℕ} {δ : kˣ} (h2 : (2 : k) ≠ 0)
    (hδ : ¬ IsSquare (δ : k)) (ψ : (Fin m → k) ≃ₗ[k] hermitianSubmodule (δ : k))
    (hker : ∀ g : SpecialLinearGroup (Fin 2) (extension (δ : k)),
      conjAut m k (rowOHom δ ψ g) = 1 ↔ g = 1 ∨ g = -1)
    (g : SpecialLinearGroup (Fin 2) (extension (δ : k)))
    (hg2 : conjAut m k (rowOHom δ ψ g) ^ 2 = 1) (hg1 : conjAut m k (rowOHom δ ψ g) ≠ 1) :
    g * g = -1 := by
  have : Fact (¬ IsSquare (δ : k)) := ⟨hδ⟩
  rw [← map_pow, ← map_pow, hker, pow_two] at hg2
  rcases hg2 with h | h
  · exfalso
    apply hg1
    rw [hker]
    by_cases h1 : g = 1
    · exact Or.inl h1
    · right
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      exact CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq (two_ne_zero_ext (δ : k) h2) g
        (by rw [pow_two, h]) h1
  · exact h

end OIL

end CFSG.ComponentClassification.CatFactsL4U4
