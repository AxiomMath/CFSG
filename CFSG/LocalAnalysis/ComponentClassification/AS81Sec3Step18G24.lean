module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step18Core
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18HoltG24
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Co1
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Census
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalQuotNF
public import CFSG.Fischer.NoF25.Local
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
public import CFSG.LargeExtraspecial.AS35DStmt
public import CFSG.LargeExtraspecial.GLRElimInv
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S10Five
public import CFSG.LargeExtraspecial.S10FourA
public import CFSG.LargeExtraspecial.S10SixA
public import CFSG.LargeExtraspecial.S10Three
public import CFSG.LargeExtraspecial.S12FourteenB
public import CFSG.LargeExtraspecial.S14C10Apply
public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocRed
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18FusionOdd
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18He
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Holt
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Suz
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocalBetween
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuz
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Monster.Schur.Restriction
public import CFSG.Perm.CentralizerOrbit
public import CFSG.RankThree.Literature.FSmithTheorem2
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Ly.ThreeBCount
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.Th.KernelContractBase
public import CFSG.Sporadic.ThSchreier.FullAutCoreBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)

section Quotient

variable {H : Type} [Group H] [Finite H] {A : Subgroup H}

local notation "π" => QuotientGroup.mk' (standardComponentOddCore H)

theorem rankTwoHyp_map_quotient (hH : RankTwoHypNF H A) :
    RankTwoHypNF (H ⧸ standardComponentOddCore H) (A.map π) ∧
      standardComponentOddCore (H ⧸ standardComponentOddCore H) = ⊥ ∧
      Nonempty (rankTwoQuot A ≃* rankTwoQuot (A.map π)) :=
  ⟨RankTwoClassical.NFQuot.rankTwoHyp_map hH,
    RankTwoSporadic.standardComponentOddCore_quotient_eq_bot,
    ⟨RankTwoClassical.NFQuot.quotCenterMap hH⟩⟩

theorem quotCenter_equiv_map_of_center_eq_bot (hA : standardComponentIsStandard A)
    (hrank : 2 ≤ Open.pRank 2 (centralizer (A : Set H)))
    (hZ : center ↥(rankTwoX (A.map π)) = ⊥) :
    Nonempty (↥(rankTwoX A) ⧸ center ↥(rankTwoX A) ≃* ↥(rankTwoX (A.map π))) ∧
      Odd (Nat.card (center ↥(rankTwoX A))) := by
  set O := standardComponentOddCore H with hOdef
  set X := rankTwoX A with hXdef
  have hOA : O ≤ centralizer (A : Set H) :=
    RankTwoSporadic.standardComponentOddCore_le_centralizer hA hrank
  have hCn : (centralizer (O : Set H)).Normal := inferInstance
  have hXO : X ≤ centralizer (O : Set H) :=
    normalClosure_le_normal (le_centralizer_iff.mp hOA)
  have hOX : O ≤ centralizer (X : Set H) := le_centralizer_iff.mp hXO
  have hmap : X.map π = rankTwoX (A.map π) :=
    map_normalClosure _ _ (QuotientGroup.mk'_surjective _)
  let ρ : ↥X →* ↥(rankTwoX (A.map π)) :=
    (MulEquiv.subgroupCongr hmap).toMonoidHom.comp (MonoidHom.subgroupMap π X)
  have hρ : Function.Surjective ρ :=
    (MulEquiv.subgroupCongr hmap).surjective.comp (MonoidHom.subgroupMap_surjective π X)
  have hρv : ∀ c : ↥X, ((ρ c : ↥(rankTwoX (A.map π))) : H ⧸ standardComponentOddCore H) =
      π (c : H) := fun c => rfl
  have hρ1 : ∀ c : ↥X, ρ c = 1 ↔ (c : H) ∈ O := by
    intro c
    rw [← OneMemClass.coe_eq_one, hρv, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : ρ.ker = center ↥X := by
    ext c
    rw [MonoidHom.mem_ker, hρ1]
    constructor
    · intro hc
      exact mem_center_iff.mpr fun d => Subtype.ext (mem_centralizer_iff.mp (hOX hc) d d.2)
    · intro hc
      have hρc : ρ c ∈ center ↥(rankTwoX (A.map π)) := by
        rw [mem_center_iff]
        intro y
        obtain ⟨d, rfl⟩ := hρ y
        rw [← map_mul, ← map_mul, (mem_center_iff.mp hc d)]
      rw [hZ, mem_bot, hρ1] at hρc
      exact hρc
  refine ⟨⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)⟩, ?_⟩
  refine (RankTwoSporadic.odd_card_standardComponentOddCore (G := H)).of_dvd_nat ?_
  rw [← card_map_of_injective X.subtype_injective]
  refine card_dvd_of_le ?_
  rintro _ ⟨c, hc, rfl⟩
  rw [← hker] at hc
  exact (hρ1 c).mp hc

end Quotient

end CFSG.ComponentClassification.AS81
