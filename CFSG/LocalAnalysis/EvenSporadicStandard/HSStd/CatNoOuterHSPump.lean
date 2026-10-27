module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTType
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5CatOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic
public import CFSG.RankThree.PartOne.S11c.HSPairCentralize

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem catNoOuterHS_of_kgPumpTableT
    (hT : Zassenhaus.Outer.KGPumpTableT) : CatNoOuterHS := by
  intro X _ _ hcat hsimple τ hτ2 hτo ⟨A, hAle, hAn, hAHS⟩
  have hτ1 : τ ≠ 1 := fun h => hτo 1 (h.trans (map_one MulAut.conj).symm)
  obtain ⟨e⟩ := hAHS
  obtain ⟨hs, a, b, hab⟩ := CFSG.RankThree.PartOne.HNRed.hs_simple_nonab
  have hsA : IsSimpleGroup ↥A := @MulEquiv.isSimpleGroup ↥A _ (Carrier .HS) _ hs e
  have hnaA : ∃ a b : ↥A, a * b ≠ b * a := by
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  have hq : CFSG.IsQuasisimple ↥A :=
    Induction.Hyp.isQuasisimple_of_simple_nonabelian hsA hnaA
  have hZ : center ↥A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥A) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnaA
      exact hcd (mem_center_iff.1 (h1 ▸ mem_top d) c)
  have hsn : (A.subgroupOf (HSStd.autCentralizer τ)).IsSubnormal := hAn.isSubnormal
  have hp : IsPGroup 2 ↥(center ↥A) := by
    rw [hZ]
    exact IsPGroup.of_bot
  have hs' : IsSporadic (↥A ⧸ center ↥A) .HS :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  obtain ⟨-, -, h3, -⟩ := hT X hcat hsimple τ hτ2 hτ1 A hAle hq hsn hp
  have h2 := (h3 hs').2
  rw [hZ] at h2
  simp at h2

end CFSG.EvenSporadicStandard.HSStd
