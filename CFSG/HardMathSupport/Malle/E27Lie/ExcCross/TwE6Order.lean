module

public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.TwE6Core
public import CFSG.RankThree.E6.LargePrimeStabilizers

public noncomputable section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CoxeterSystem

set_option linter.unusedSectionVars false

section TwOrder


variable {L : Type} [Field L]

local notation "ρ6" => TwistTag.E6.perm

@[expose] def X6Weyl (Fr : L →+* L) (w0 : WeylGroup TwistTag.E6.tag) :
    ↥(X6 L Fr w0) →* WeylGroup TwistTag.E6.tag :=
  (weylQuotientHom TwistTag.E6.tag L).comp (Subgroup.inclusion (X6_le_monomial Fr w0))

theorem X6Weyl_surjective (Fr : L →+* L) (w0 : WeylGroup TwistTag.E6.tag) :
    Function.Surjective (X6Weyl Fr w0) := by
  intro w
  induction w using (coxeterSystem TwistTag.E6.tag).simple_induction_left with
  | one => exact ⟨1, map_one _⟩
  | mul_simple_left w i ih =>
    obtain ⟨x, hx⟩ := ih
    have hy : weylElt TwistTag.E6.tag L i 1 ∈ X6 L Fr w0 :=
      tits6_le_X6 Fr w0 (weylElt_mem_tits6 i)
    refine ⟨⟨weylElt TwistTag.E6.tag L i 1, hy⟩ * x, ?_⟩
    rw [map_mul, hx]
    congr 1
    exact weylQuotientHom_eq (mapsRootLines_weylElt i)

theorem twistedTorus_le_ker_X6Weyl (Fr : L →+* L) (w0 : WeylGroup TwistTag.E6.tag) :
    (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L w0)
      (twistHom TwistTag.E6 L Fr)).subgroupOf (X6 L Fr w0) ≤ (X6Weyl Fr w0).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have ht : (x : ModGL TwistTag.E6.tag L) ∈ torusGroup TwistTag.E6.tag L :=
    (mem_twistedTorusOf.1 hx).1
  exact weylQuotientHom_eq (g := ⟨(x : ModGL TwistTag.E6.tag L), X6_le_monomial Fr w0 x.2⟩)
    (mapsRootLines_of_mem_torusGroup ht)

theorem twistedTorus6_card_mul_dvd (Fr : L →+* L) (w0 : WeylGroup TwistTag.E6.tag) :
    Nat.card (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L w0)
      (twistHom TwistTag.E6 L Fr)) * 51840 ∣ Nat.card (X6 L Fr w0) := by
  have h1 := Subgroup.card_ker_mul_card_range (X6Weyl Fr w0)
  have hW : Nat.card (WeylGroup TwistTag.E6.tag) = 51840 := CFSG.RankThree.E6.card_weylGroup_E6
  rw [MonoidHom.range_eq_top.2 (X6Weyl_surjective Fr w0), Subgroup.card_top, hW] at h1
  rw [← h1]
  refine Nat.mul_dvd_mul_right ?_ _
  have := Subgroup.card_dvd_of_le (twistedTorus_le_ker_X6Weyl Fr w0)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (twistedTorus_le_X6 Fr w0)).toEquiv] at this

end TwOrder

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross
