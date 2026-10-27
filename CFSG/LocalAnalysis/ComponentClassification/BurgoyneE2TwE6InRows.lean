module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6InInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6InOuter
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Def
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6C4

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6In

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ClassicalInvolution
open scoped commutatorElement Pointwise

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Chevalley.OddE6AllInvolution (isAlgebraic_zmod_algebraicClosure)

omit [Fact p.Prime] [CharP k p] [IsAlgClosed k] in
theorem burgoyneE2TwistedE6NonGraphInput_of_t1
    (h1 : BurgoyneE2TwistedE6T1Input) : BurgoyneE2TwistedE6NonGraphInput := by
  intro p f hp hp2 hf K _ _ hK σ hσ α hα hF4 hc
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  by_cases hin : α ∉ twistedE6Inn K σ
  · obtain ⟨ψ, hψ | hψ⟩ := twE6_outer_involution_conj hp hp2 hf K hK σ hσ α hα2 hin
    · exact absurd hψ (hF4 ψ)
    · exact absurd hψ (hc ψ)
  rw [not_not] at hin
  obtain ⟨t, rfl⟩ := hin
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  have ht2 : t ^ 2 = 1 := conj_injective hZ (by rw [map_pow, hα2, map_one])
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hα
    exact absurd hα (by decide)
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK'
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hk := isAlgebraic_zmod_algebraicClosure K p
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨hder, -⟩ := twE6_lift_facts (p := p) (k := AlgebraicClosure K) hf hodd K hK σ hσ
  have hxH : baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL TwistTag.E6.tag K) ∈
      ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
          (frobTwistGL TwistTag.E6.tag (AlgebraicClosure K) p f
            (diagramMap TwistTag.E6 (AlgebraicClosure K))),
        fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
          (frobTwistGL TwistTag.E6.tag (AlgebraicClosure K) p f
            (diagramMap TwistTag.E6 (AlgebraicClosure K)))⁆ := by
    rw [hder]
    exact ⟨t, t.2, rfl⟩
  have hxR := Subgroup.commutator_le_of_le le_rfl le_rfl hxH
  have hx2 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL TwistTag.E6.tag K) ^ 2
      = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, ht2, Subgroup.coe_one, map_one]
  obtain ⟨r, hr, D, h, g₁, s, hg₁G, hhT, hFg₁, -, hg₁x, hDχ, hDe, hDθ, hDF, hcent⟩ :=
    Q3.exc3_e6_datum_conj p hp2 hk hf hxR hx2
  have hrmask : r.mask = 0 ∨ r.mask = 20 ∨ r.mask = 2 := by
    simp only [e6SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases hrmask with h0 | h20 | h2
  ·
    exfalso
    apply ht1
    have e1 : rootDiagUnit TwistTag.E6.tag
        (signCharTuple (k := AlgebraicClosure K) (signMaskChar TwistTag.E6.tag r.mask)) = 1 := by
      have e0 : signCharTuple (k := AlgebraicClosure K) (signMaskChar TwistTag.E6.tag 0) = 1 := by
        funext j
        rw [signCharTuple, signMaskChar_single]
        simp
      rw [h0, e0]
      exact rootDiagUnit_one
    rw [e1] at hg₁x
    refine Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) ?_)
    rw [Subgroup.coe_one, map_one]
    calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL TwistTag.E6.tag K) =
        g₁⁻¹ * (g₁ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (t : ModGL TwistTag.E6.tag K) * g₁⁻¹) * g₁ := by group
      _ = 1 := by rw [hg₁x]; group
  ·
    refine h1 p f hp2 hf K hK σ hσ t ht2 (AlgebraicClosure K) ⟨g₁, hg₁G, hFg₁, ?_⟩
    rw [hg₁x, h20]
  ·
    have hwG : rootDiagUnit TwistTag.E6.tag s * g₁ ∈
        adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
      mul_mem (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag _ s).1 hg₁G
    exact Or.inl (burgCoreFor_conj_of_mask_two hp2 hf K hK σ hσ hk t ht1 ht2 D h _ hwG hhT
      (by rw [hDχ, h2]) hDe hDθ hDF hcent)

end CFSG.ComponentClassification.Burgoyne.E2.TwE6In
