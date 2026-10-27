module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeSolvAutCfg
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeSolvParab
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCasesProof
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeSolvDirectCfg
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup SolvParab
open CFSG.ComponentClassification.AS76b (oUpperTwo)

private theorem symThreePairs_of_hat {G : Type} [Group G] [Finite G] {M X : Subgroup G}
    (hXM : X ≤ M) (h : SymThreePairs (↥(barM M X) ⧸ CFSG.pCore 2 ↥(barM M X))) :
    SymThreePairs (↥X ⧸ CFSG.pCore 2 ↥X) := by
  have hker : CFSG.pCore 2 ↥X = (TenThreeThree.hatHom M X hXM).ker :=
    CZeroLift.pCore_eq_ker _ (TenThreeThree.hatHom_surjective M X hXM)
      (TenThreeThree.isPGroup_ker_hatHom M X hXM) (TenThreeThree.pCore_hat_eq_bot M X)
  exact h.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (TenThreeThree.hatHom_surjective M X hXM))).symm

variable (G : Type) [Group G] [Finite G]

section Certified


theorem agl81TenThreeSolvBlock_cfg (hGA : CFSG.Open.GriessAllModelsStatement)
    (h93 : Asc81bNineThree) (h85 : Asc81bEightFive) (hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (h984 : AGL81NineEightFour G) (h91 : AGL81TenNineOneCfg G)
    (hZ6 : AGL81TenOneSixCenterCfg G) :
    Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      AGL81CfgData 3 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∀ I₁ ∈ cZero (H ⊓ L), ∀ I₂ ∈ cZero (H ⊓ L),
        Nonempty (↥I₁ ⧸ CFSG.pCore 2 ↥I₁ ≃* Equiv.Perm (Fin 3)) →
        Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)) →
        oUpperTwo I₁ ≠ oUpperTwo I₂ → ⁅I₁, I₂⁆ ≤ pCoreOf 2 (H ⊓ L) := by
  intro hS P M H Q K hd L hL I₁ hI₁ I₂ hI₂ hs₁ hs₂ hne
  have hP : SymThreePairs (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L))) := by
    rcases TwelveNotLe.nineThree_parabolic_or_unique h85 h93 hD2 h984 h91 hZ6 hS hd hL with
      ⟨hcl, hpar⟩ | hu
    · exact symThreePairs_of_parabolic hGA hL.component.2.2
        (TenThreeThree.pCoreOf_barM_eq_bot hL.toIsTwoPrimeComponent) hcl hpar
    · exact fun T₁ T₂ h₁ h₂ hb₁ hb₂ =>
        Or.inl (TwelveNotLe.kFactTwelveNotLeSymThreeUnique_holds _ hu T₁ T₂ h₁ h₂ hb₁ hb₂)
  exact commutator_le_pCoreOf_of_symThreePairs
    (symThreePairs_of_hat (inf_le_right.trans hL.le) hP) hI₁ hI₂ hs₁ hs₂ hne

theorem agl81TenThreeSolvStructCfg_holds (hGA : CFSG.Open.GriessAllModelsStatement)
    (h93 : Asc81bNineThree) (h85 : Asc81bEightFive) (hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (h984 : AGL81NineEightFour G) (h91 : AGL81TenNineOneCfg G)
    (hZ6 : AGL81TenOneSixCenterCfg G) : AGL81TenThreeSolvStructCfg G :=
  fun hS P M H Q K hd L hL I₀ hI₀ hshape =>
    ⟨agl81TenThreeSolvDirect_cfg G (agl81NoSUMemberCfg G hGA h93 h85 hD2 h984)
        (agl81TenThreeSolvBlock_cfg G hGA h93 h85 hD2 h984 h91 hZ6) hS P M H Q K hd L hL I₀ hI₀
        hshape,
      agl81TenThreeSolvAut_cfg G hGA h93 h85 hD2 h984 hS P M H Q K hd L hL I₀ hI₀ hshape⟩

end Certified

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
