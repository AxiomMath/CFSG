module

public import CFSG.GH74.GLS.C3.Layer1.EvenSetup
public import CFSG.GH74.GLS.C3.Layer1.Th2CaseI
public import CFSG.GH74.GLS.C3.Layer1.Thm1Normal
public import CFSG.GH74.GLS.C3.Layer1.Back91

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools

@[expose] def B_cor_PU4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (x : G) (K : Subgroup G),
    orderOf x = 2 → IsPCompIn 2 (centralizer ({x} : Set G)) K → 2 ≤ pRank 2 ↥K →
      IsTerminalPair 2 x K → IsStandardSubgroup K

theorem two_le_pRank_of_hasL2Model_odd {K : Type} [Group K] [Finite K] (h : HasL2Model K Odd) :
    2 ≤ pRank 2 K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := C3.Layer1.Thm1.exists_l2_model_of_hasL2Model h
  rw [Stage1.Thm2.Recip.pRank_eq_of_mulEquiv' (e.trans (IVK.L2.equivPSL F))]
  exact ComponentClassification.UnbalancedGS.RankSmallSources.two_le_pRank_psl_two
    (C3.Layer1.Thm1.ringChar_ne_two_of_odd_card F hF.1)

theorem b_even_std_of_PU4 (h : B_cor_PU4) : B_even_std := by
  intro G _ _ hG _ _ x K T Q hs
  have hodd : HasL2Model ↥K Odd :=
    C3.Layer1.Back.hasL2Model_mono (fun q hq => C3.Layer1.Back.isFM9_odd hq) hs.isL2
  have hstd : IsStandardSubgroup K :=
    h G hG.kproper x K hs.terminal.1 hs.twoTerminal.1.2.2 (two_le_pRank_of_hasL2Model_odd hodd)
      hs.terminal
  exact ⟨hstd, Th2.CaseI.gammaK_le_normalizer_of_standard hstd hs.sylowQ⟩

end CFSG.GH74.GLS
