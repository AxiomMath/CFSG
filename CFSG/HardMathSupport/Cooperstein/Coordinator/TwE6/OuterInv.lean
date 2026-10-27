module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverTwRank

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule


section Gen

variable {G L : Type*} [Group G] [Group L] [Finite L]

theorem isCentralCover_of_odd_center (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* G) :
    IsCentralCover (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) 2 where
  surj := e.surjective.comp (QuotientGroup.mk'_surjective _)
  ker_le := by
    intro x hx
    have : (QuotientGroup.mk x : L ⧸ Subgroup.center L) = 1 := by
      have h1 : e (QuotientGroup.mk x) = 1 := hx
      exact e.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff _).1 this
  coprime := by
    have : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker =
        Subgroup.center L := by
      ext x
      constructor
      · intro hx
        have : (QuotientGroup.mk x : L ⧸ Subgroup.center L) = 1 := by
          have h1 : e (QuotientGroup.mk x) = 1 := hx
          exact e.injective (by rw [h1, map_one])
        exact (QuotientGroup.eq_one_iff _).1 this
      · intro hx
        show e (QuotientGroup.mk x) = 1
        rw [(QuotientGroup.eq_one_iff _).2 hx, map_one]
    rw [this]
    exact (Nat.coprime_two_right).2 hodd

theorem isPElt_two_of_sq {M : Type*} [Group M] {x : M} (hx : x ^ 2 = 1) : IsPElt 2 x :=
  ⟨1, by simpa using hx⟩

end Gen

section SL2

variable {F : Type*} [Field F]

theorem mem_of_upper_lower {H : Type*} [Group H] (S : Subgroup H) (f : SL2 F →* H)
    (hu : ∀ c, f (uSL c) ∈ S) (hv : ∀ c, f (vSL c) ∈ S) (g : SL2 F) : f g ∈ S := by
  have hle : Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper F) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower F)) ≤ S.comap f := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hu c
    · exact hv c
  have : g ∈ S.comap f := hle (by
    rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]; exact Subgroup.mem_top g)
  exact this

theorem hom_ext_SL2 {H : Type*} [Group H] {f₁ f₂ : SL2 F →* H}
    (hu : ∀ c, f₁ (uSL c) = f₂ (uSL c)) (hv : ∀ c, f₁ (vSL c) = f₂ (vSL c)) : f₁ = f₂ := by
  refine MonoidHom.ext fun g => ?_
  exact mem_of_upper_lower (MonoidHom.eqLocus f₁ f₂) (MonoidHom.id _) hu hv g

end SL2

section SLaut

variable {F : Type*} [Field F]

@[expose] def slAut (τ : F ≃+* F) (μ : Fˣ) : SL2 F →* SL2 F :=
  (MulAut.conj (HSL μ)).toMonoidHom.comp (Matrix.SpecialLinearGroup.map τ.toRingHom)

theorem coe_uSL' (c : F) : ((uSL c : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] := rfl

theorem coe_vSL' (c : F) : ((vSL c : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; c, 1] := rfl

theorem coe_HSL' (t : Fˣ) :
    ((HSL t : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)] := rfl

theorem slAut_coe (τ : F ≃+* F) (μ : Fˣ) (M : SL2 F) :
    ((slAut τ μ M : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      !![(μ : F), 0; 0, ((μ⁻¹ : Fˣ) : F)] * (M : Matrix (Fin 2) (Fin 2) F).map τ *
        !![((μ⁻¹ : Fˣ) : F), 0; 0, (μ : F)] := by
  simp only [slAut, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.map_apply_coe, coe_HSL', Matrix.adjugate_fin_two]
  congr 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem map_lit (τ : F → F) (a b c d : F) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F).map τ = !![τ a, τ b; τ c, τ d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem slAut_uSL (τ : F ≃+* F) (μ : Fˣ) (c : F) :
    slAut τ μ (uSL c) = uSL ((μ : F) ^ 2 * τ c) := by
  refine Subtype.ext ?_
  have h1 : (μ : F) * ((μ⁻¹ : Fˣ) : F) = 1 := μ.mul_inv
  have h2 : ((μ⁻¹ : Fˣ) : F) * (μ : F) = 1 := μ.inv_mul
  rw [slAut_coe, coe_uSL', coe_uSL', map_lit, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [map_one, map_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> first | ring | linear_combination h1 | linear_combination h2

theorem slAut_vSL (τ : F ≃+* F) (μ : Fˣ) (c : F) :
    slAut τ μ (vSL c) = vSL (((μ⁻¹ : Fˣ) : F) ^ 2 * τ c) := by
  refine Subtype.ext ?_
  have h1 : (μ : F) * ((μ⁻¹ : Fˣ) : F) = 1 := μ.mul_inv
  have h2 : ((μ⁻¹ : Fˣ) : F) * (μ : F) = 1 := μ.inv_mul
  rw [slAut_coe, coe_vSL', coe_vSL', map_lit, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [map_one, map_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> first | ring | linear_combination h1 | linear_combination h2

theorem slAut_HSL (τ : F ≃+* F) (μ : Fˣ) (w : Fˣ) :
    slAut τ μ (HSL w) = HSL (Units.map τ.toMonoidHom w) := by
  refine Subtype.ext ?_
  have h1 : (μ : F) * ((μ⁻¹ : Fˣ) : F) = 1 := μ.mul_inv
  have h2 : ((μ⁻¹ : Fˣ) : F) * (μ : F) = 1 := μ.inv_mul
  have hμ0 : (μ : F) ≠ 0 := μ.ne_zero
  rw [slAut_coe, coe_HSL', coe_HSL', map_lit, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [map_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [map_inv₀]
  all_goals field_simp

end SLaut

section Lift

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
  (a : Fin TwistTag.E6.foldedTag.rank)

include hf hK hσ in
@[expose] def Rhat : SL2 (orbitField TwistTag.E6 K σ a) →* ↥(TwistedE6.fixedGroup K σ) :=
  (minOrbitHom σ a).codRestrict (TwistedE6.fixedGroup K σ) (fun g =>
    mem_of_upper_lower (TwistedE6.fixedGroup K σ) (minOrbitHom σ a)
      (minOrbitHom_uSL_mem hf hK σ hσ a) (minOrbitHom_vSL_mem hf hK σ hσ a) g)

include hf hK hσ in
theorem Rhat_uSL (c : orbitField TwistTag.E6 K σ a) :
    Rhat hf hK σ hσ a (uSL c) = hatX hf hK σ hσ a c := rfl

include hf hK hσ in
theorem Rhat_vSL (c : orbitField TwistTag.E6 K σ a) :
    Rhat hf hK σ hσ a (vSL c) = hatY hf hK σ hσ a c := rfl

include hf hK hσ in
theorem Rhat_HSL (w : (orbitField TwistTag.E6 K σ a)ˣ) :
    Rhat hf hK σ hσ a (HSL w) = hatH hf hK σ hσ a w := rfl

end Lift

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
