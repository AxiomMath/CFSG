module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONorm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OModel

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal Matrix CFSG.Open
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin (quadMinus nondegenerate_polarBilin_quadMinus_of_finite
  coe_quadMinus)

section Similitude

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem semi_similitude (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (σ : OW F → OW F)
    (θ : F →+* F) (hθθ : ∀ r, θ (θ r) = r) (hadd : ∀ x y, σ (x + y) = σ x + σ y)
    (hsm : ∀ (r : F) x, σ (r • x) = θ r • σ x)
    (hN : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∃ g' ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : OW F,
        σ ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) =
          (g' : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
            σ x) :
    ∃ μ : F, ∀ x : OW F, quadMinus 3 F b c (σ x) = μ * θ (quadMinus 3 F b c x) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  set Q := quadMinus 3 F b c with hQdef
  have hσ0 : σ 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have h' : σ 0 + 0 = σ 0 + σ 0 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  have hinv : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x y : OW F,
      polar Q (σ ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x))
        (σ ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ y)) = polar Q (σ x) (σ y) := by
    intro g hg x y
    obtain ⟨g', hg', hgx⟩ := hN g hg
    rw [hgx x, hgx y]
    exact polar_mulVec_of_mem_statedOmega hg' _ _
  let B' : LinearMap.BilinForm F (OW F) :=
    LinearMap.mk₂ F (fun x y => θ (polar Q (σ x) (σ y)))
      (fun x x' y => by simp only [hadd, polar_add_left, map_add])
      (fun r x y => by simp only [hsm, polar_smul_left_eq, map_mul, hθθ, smul_eq_mul])
      (fun x y y' => by simp only [hadd, polar_add_right, map_add])
      (fun r x y => by simp only [hsm, polar_smul_right_eq, map_mul, hθθ, smul_eq_mul])
  let T := B'.symmCompOfNondegenerate (polarBilin Q) hQ
  have hT : ∀ x y, polar Q (T x) y = θ (polar Q (σ x) (σ y)) := by
    intro x y
    have h := LinearMap.BilinForm.symmCompOfNondegenerate_left_apply B' hQ y x
    rw [polarBilin_apply_apply] at h
    exact h.trans (by simp [B'])
  have hTcomm : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : OW F,
      T ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) =
        (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          T x := by
    intro g hg x
    have key : ∀ z, polar Q (T ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) -
          (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
            T x) z = 0 := by
      intro z
      obtain ⟨y, rfl⟩ : ∃ y, (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ y = z :=
        ⟨((g⁻¹ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ z, by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.one_mulVec]⟩
      rw [polar_sub_left, hT, hinv g hg x y, polar_mulVec_of_mem_statedOmega hg, hT, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_polar_eq_zero hQ key)
  obtain ⟨μ, hμ⟩ := omega_commutant hirr T.toAddMonoidHom hTcomm
  have hscal : ∀ x y, θ (polar Q (σ x) (σ y)) = μ * polar Q x y := by
    intro x y
    rw [← hT]
    have := hμ x
    simp only [LinearMap.toAddMonoidHom_coe] at this
    rw [this, polar_smul_left_eq]
  set R : OW F → F := fun x => θ (Q (σ x)) - μ * Q x with hRdef
  have hRadd : ∀ x y, R (x + y) = R x + R y := by
    intro x y
    simp only [hRdef]
    rw [hadd, QuadraticMap.map_add Q (σ x) (σ y), map_add, map_add, hscal x y,
      QuadraticMap.map_add Q x y]
    ring
  have hR0 : R 0 = 0 := by simp [hRdef, hσ0]
  have hRinv : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x : OW F,
      R ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) =
        R x := by
    intro g hg x
    obtain ⟨g', hg', hgx⟩ := hN g hg
    simp only [hRdef]
    rw [hgx x, quadMinus_mulVec_of_mem_statedOmega hg', quadMinus_mulVec_of_mem_statedOmega hg]
  have hRe0 : R (Pi.single (Sum.inl idx0) 1) = 0 := by
    obtain ⟨E, hE, hEx⟩ := eichler_mem_statedOmega hirr (Pi.single (Sum.inl idx1) 1)
      (Pi.single (Sum.inl idx0) 1)
    have h1 := hRinv E hE (Pi.single (Sum.inr (Sum.inl idx1)) 1)
    rw [hEx, eichler_e1_e0_f1, hRadd] at h1
    linear_combination h1
  have hRs : ∀ s, Q s = 0 → R s = 0 := by
    intro s hs
    by_cases hs0 : s = 0
    · rw [hs0]
      exact hR0
    obtain ⟨g, hg, hge⟩ := exists_statedOmega_apply_e0 hirr hs hs0
    rw [← hge, hRinv g hg]
    exact hRe0
  let S : AddSubgroup (OW F) :=
    { carrier := {x | R x = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [hRadd, hx, hy, add_zero]
      zero_mem' := hR0
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        have := hRadd x (-x)
        rw [add_neg_cancel, hR0, hx, zero_add] at this
        exact this.symm }
  have hQA : ∀ x, θ (Q (σ x)) = μ * Q x := fun x => by
    have := mem_of_forall_singular_mem S hRs x
    exact sub_eq_zero.mp this
  refine ⟨θ μ, fun x => ?_⟩
  have := congrArg θ (hQA x)
  rw [hθθ, map_mul] at this
  exact this

theorem semi_normalize (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (σ : OW F → OW F)
    (θ : F →+* F) (hθθ : ∀ r, θ (θ r) = r) (hadd : ∀ x y, σ (x + y) = σ x + σ y)
    (hsm : ∀ (r : F) x, σ (r • x) = θ r • σ x) (hσσ : ∀ x, σ (σ x) = x) {μ : F}
    (hμ : ∀ x : OW F, quadMinus 3 F b c (σ x) = μ * θ (quadMinus 3 F b c x)) :
    ∃ σ₁ : OW F → OW F, (∀ x y, σ₁ (x + y) = σ₁ x + σ₁ y) ∧
      (∀ (r : F) x, σ₁ (r • x) = θ r • σ₁ x) ∧ (∀ x, σ₁ (σ₁ x) = x) ∧
      ∀ x, quadMinus 3 F b c (σ₁ x) = θ (quadMinus 3 F b c x) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  obtain ⟨a, ha⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
  set Q := quadMinus 3 F b c with hQdef
  have hμθ : μ * θ μ = 1 := by
    have h1 : Q a = μ * θ μ * Q a := by
      calc Q a = Q (σ (σ a)) := by rw [hσσ]
        _ = μ * θ (Q (σ a)) := hμ _
        _ = μ * θ (μ * θ (Q a)) := by rw [hμ a]
        _ = μ * θ μ * Q a := by rw [map_mul, hθθ]; ring
    have h3 : (μ * θ μ - 1) * Q a = 0 := by linear_combination (-1 : F) * h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right ha)
  have hμ0 : μ ≠ 0 := fun h => by
    rw [h, zero_mul] at hμθ
    exact zero_ne_one hμθ
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) μ⁻¹
  have hl2 : l * l * μ = 1 := by
    rw [← hl]
    exact inv_mul_cancel₀ hμ0
  have hlθ : l * θ l = 1 := by
    have h4 : (l * θ l) * (l * θ l) = 1 := by
      calc (l * θ l) * (l * θ l) = (l * l) * (θ l * θ l) := by ring
        _ = μ⁻¹ * θ μ⁻¹ := by rw [← map_mul, ← hl]
        _ = 1 := by rw [map_inv₀, ← mul_inv, hμθ, inv_one]
    have h5 : (l * θ l - 1) ^ 2 = 0 := by linear_combination h4 + (1 - l * θ l) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
  refine ⟨fun x => l • σ x, fun x y => ?_, fun r x => ?_, fun x => ?_, fun x => ?_⟩
  · simp only [hadd, smul_add]
  · simp only [hsm]
    exact smul_comm l (θ r) (σ x)
  · simp only [hsm, hσσ, smul_smul, hlθ, one_smul]
  · simp only [QuadraticMap.map_smul, smul_eq_mul, hμ]
    linear_combination θ (Q x) * hl2

end Similitude

end CFSG.LocalAnalysis.RankThreeUC
