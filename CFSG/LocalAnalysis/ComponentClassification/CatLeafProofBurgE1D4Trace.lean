module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1InnerRow
public import CFSG.RankThree.PartOne.KF4.F4Traces
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Lin

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.ClassicalInvolution.G2D4Models
open CFSG.RankThree.PartOne.KF4 (closure_traces_of_formula trace_simpleRootSL2_of_counts')

theorem rootExponents_D4_node :
    (rootExponents d4 (nd 2)).toFinset = {-2, -1, 0, 1, 2} ∧
      (rootExponents d4 (nd 2)).count (-2) = 1 ∧
      (rootExponents d4 (nd 2)).count (-1) = 8 ∧ (rootExponents d4 (nd 2)).count 0 = 6 ∧
      (rootExponents d4 (nd 2)).count 1 = 8 ∧ (rootExponents d4 (nd 2)).count 2 = 1 := by
  decide +kernel

theorem trace_simpleRootSL2_D4_node
    {k : Type} [Field k] (A : SL2 k) :
    LinearMap.trace k (RootModule d4 k)
        (simpleRootSL2 d4 k (nd 2) A : Module.End k (RootModule d4 k)) =
      ((1 : ℕ) : k) * (A : Matrix (Fin 2) (Fin 2) k).trace ^ 2 +
        ((8 : ℕ) : k) * (A : Matrix (Fin 2) (Fin 2) k).trace + ((8 : ℕ) : k) := by
  rw [trace_simpleRootSL2_of_counts' (a := 1) (b := 8) (m := 6) (nd 2) rootExponents_D4_node A]
  have : ((d4.rank : ℕ) : k) = 4 := by
    rw [show d4.rank = 4 from rfl]
    norm_num
  rw [this]
  push_cast
  ring

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem twistedIncl_slLong_eq_simpleRootSL2
    (A : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) :
    twistedIncl σ (slLong σ hσ A) =
      simpleRootSL2 d4 K (nd 2) (Matrix.SpecialLinearGroup.map (fixedField σ).subtype A) := by
  have h := CFSG.SectionRank.EvenCover.sl2_hom_ext
    (f := (twistedIncl σ).comp (slLong σ hσ))
    (g := (simpleRootSL2 d4 K (nd 2)).comp
      (Matrix.SpecialLinearGroup.map (fixedField σ).subtype)) (fun c => ?_) (fun c => ?_)
  · exact congrArg (fun φ => φ A) h
  · have e : Matrix.SpecialLinearGroup.map (fixedField σ).subtype (sl2Upper c) =
        sl2Upper (c : K) := Subtype.ext (by
      ext p q
      fin_cases p <;> fin_cases q <;> simp [coe_sl2Upper])
    simp only [MonoidHom.comp_apply, e]
    rw [← uSL_eq_sl2Upper, ← uSL_eq_sl2Upper, twistedIncl_slLong_upper hσ, simpleRootSL2_uSL,
      xPar_simple, RootOperatorFamily.coe_eltElement, RootOperatorFamily.eltUnit_simple]
  · have e : Matrix.SpecialLinearGroup.map (fixedField σ).subtype (sl2Lower c) =
        sl2Lower (c : K) := Subtype.ext (by
      ext p q
      fin_cases p <;> fin_cases q <;> simp [coe_sl2Lower])
    simp only [MonoidHom.comp_apply, e]
    rw [← vSL_eq_sl2Lower, ← vSL_eq_sl2Lower, twistedIncl_slLong_lower hσ, simpleRootSL2_vSL,
      xPar_neg_simple, RootOperatorFamily.coe_eltElement,
      RootOperatorFamily.eltUnit_neg_simple]

include hσ in
theorem fixes_fixedField_of_fixes_slLong_traces
    [Finite K] (δ : K ≃+* K)
    (hδ : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ),
      δ (LinearMap.trace K (RootModule d4 K)
        ((twistedIncl σ (slLong σ hσ A) : ModGL d4 K) : Module.End K (RootModule d4 K))) =
      LinearMap.trace K (RootModule d4 K)
        ((twistedIncl σ (slLong σ hσ A) : ModGL d4 K) : Module.End K (RootModule d4 K)))
    (c : K) (hc : c ∈ fixedField σ) : δ c = c := by
  have : Finite (fixedField σ) := Subtype.finite
  have hcl := closure_traces_of_formula (nd 2) 1 8 8
    (fun M _ A => trace_simpleRootSL2_D4_node A) (fixedField σ) (Or.inl (by simp))
    (fun h2 _ => by
      have : CharP (fixedField σ) 2 := ringChar.of_eq h2
      rw [show ((8 : ℕ) : fixedField σ) = ((2 * 4 : ℕ) : fixedField σ) by norm_num, Nat.cast_mul,
        Nat.cast_two, CharTwo.two_eq_zero, zero_mul]) K 1 1
  have hS : {x : K | ∃ A : SL2 (fixedField σ), x = LinearMap.trace K (RootModule d4 K)
      ((1 * simpleRootSL2 d4 K (nd 2)
        (conjGL 1 (Matrix.SpecialLinearGroup.map (algebraMap (fixedField σ) K) A)) *
        1⁻¹ : ModGL d4 K) : Module.End K (RootModule d4 K))} ⊆
      ((RingHom.eqLocusField δ.toRingHom (RingHom.id K) : Subfield K) : Set K) := by
    rintro _ ⟨A, rfl⟩
    have h1 := hδ A
    rw [twistedIncl_slLong_eq_simpleRootSL2 hσ] at h1
    change δ _ = _
    rw [conjGL_one_eq, one_mul, inv_one, mul_one]
    exact h1
  have hle := Subfield.closure_le.2 hS
  rw [hcl] at hle
  exact hle (RingHom.mem_fieldRange.2 ⟨⟨c, hc⟩, rfl⟩)

end CFSG.ComponentClassification.CatLeafProof
