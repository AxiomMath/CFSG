module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFrame
public import CFSG.RankThree.Chevalley.SteinbergBID4WeylCert
public import CFSG.RankThree.PartOne.KE.OrdinaryEOuter
public import CFSG.RankThree.PartOne.KGD.PlaneBridge

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.GH74.GLS.Stage2.Bender.Thm1


section JFrame

variable {L : Type} [Field L]

@[expose] def jRep (L : Type) [Field L] (w : WeylGroup TwistTag.D4.tag) : ModGL TwistTag.D4.tag L :=
  canonicalRep (coxeterSystem TwistTag.D4.tag) L w

@[expose] def jN (L : Type) [Field L] (u w₂ : WeylGroup TwistTag.D4.tag) :
    ModGL TwistTag.D4.tag L :=
  jRep L u * jRep L w₂ * (jRep L (weylTwist TwistTag.D4 u))⁻¹

@[expose] def jG0 (L : Type) [Field L] (u : WeylGroup TwistTag.D4.tag)
    (g₂ : ModGL TwistTag.D4.tag L) : ModGL TwistTag.D4.tag L :=
  g₂ * (jRep L u)⁻¹

theorem jRep_mem_monomial (w : WeylGroup TwistTag.D4.tag) :
    jRep L w ∈ monomialSubgroup TwistTag.D4.tag L :=
  canonicalRep_mem_monomialSubgroup L w

theorem weylQuotientHom_jRep (w : WeylGroup TwistTag.D4.tag) :
    weylQuotientHom TwistTag.D4.tag L ⟨jRep L w, jRep_mem_monomial w⟩ = w :=
  weylQuotientHom_eq (mapsRootLines_canonicalRep w)

theorem jN_mem_monomial (u w₂ : WeylGroup TwistTag.D4.tag) :
    jN L u w₂ ∈ monomialSubgroup TwistTag.D4.tag L :=
  mul_mem (mul_mem (jRep_mem_monomial u) (jRep_mem_monomial w₂))
    (inv_mem (jRep_mem_monomial _))

theorem weylQuotientHom_jN (u w₂ : WeylGroup TwistTag.D4.tag) :
    weylQuotientHom TwistTag.D4.tag L ⟨jN L u w₂, jN_mem_monomial u w₂⟩ =
      u * w₂ * (weylTwist TwistTag.D4 u)⁻¹ := by
  have : (⟨jN L u w₂, jN_mem_monomial u w₂⟩ : monomialSubgroup TwistTag.D4.tag L) =
      ⟨jRep L u, jRep_mem_monomial u⟩ * ⟨jRep L w₂, jRep_mem_monomial w₂⟩ *
        (⟨jRep L (weylTwist TwistTag.D4 u), jRep_mem_monomial _⟩)⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, weylQuotientHom_jRep, weylQuotientHom_jRep,
    weylQuotientHom_jRep]

theorem jG0_mem_adjointGroup (u : WeylGroup TwistTag.D4.tag) {g₂ : ModGL TwistTag.D4.tag L}
    (hg₂ : g₂ ∈ adjointGroup TwistTag.D4.tag L) :
    jG0 L u g₂ ∈ adjointGroup TwistTag.D4.tag L :=
  mul_mem hg₂ (inv_mem (monomialSubgroup_le_adjointGroup' (jRep_mem_monomial u)))

theorem twistHom_jRep (Fr : L →+* L) (u : WeylGroup TwistTag.D4.tag) :
    twistHom TwistTag.D4 L Fr (jRep L u) = jRep L (weylTwist TwistTag.D4 u) :=
  twistHom_canonicalRep ..

theorem twistHom_jG0 (Fr : L →+* L) (u w₂ : WeylGroup TwistTag.D4.tag)
    {g₂ : ModGL TwistTag.D4.tag L}
    (hg₂ : twistHom TwistTag.D4 L Fr g₂ = g₂ * jRep L w₂) :
    twistHom TwistTag.D4 L Fr (jG0 L u g₂) = jG0 L u g₂ * jN L u w₂ := by
  unfold jG0 jN
  rw [map_mul, map_inv, twistHom_jRep, hg₂]
  group

end JFrame

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
