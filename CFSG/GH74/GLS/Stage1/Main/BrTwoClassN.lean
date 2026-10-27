module

public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassL

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final CFSG.LocalAnalysis.ComponentInitial

@[expose] def L4NFInduced : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ) (w : G) (ε : Bool), Cen2 G z S →
    Term7Out G z S q w → w ≠ 1 → q % 4 = (if ε then 3 else 1) →
      ∀ L₁ L₂ : Subgroup (CentralizerBar z), Stage1Pair G z S q L₁ L₂ →
        InducedPGL2 L₁ (SBar (S1 S z) z) q ∧ InducedPGL2 L₂ (SBar (S1 S z) z) q

@[expose] def L4NFGood : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ) (w : G) (ε : Bool), Cen2 G z S →
    Term7Out G z S q w → w ≠ 1 → q % 4 = (if ε then 3 else 1) →
      ∀ L₁ L₂ : Subgroup (CentralizerBar z), Stage1Pair G z S q L₁ L₂ →
        ∀ (K₁ K₂ : Subgroup G) (t u : G), Cfg7 G z S K₁ K₂ t u q →
          ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) = {imgBar z K₁, imgBar z K₂} →
            (∃ y : G, GoodInvolution z S L₁ L₂ q y ∧ y ∈ centralizer ({u} : Set G)) ∧
              ∀ y : G, GoodInvolution z S L₁ L₂ q y → IsConj z y

theorem l4nfRest_of_induced_good (hII : II4_4_4_center) (h41 : Prop4_1) (h61 : Prop6_1)
    (h66 : Prop6_6) (hpnf : P_normal_four) (hL44 : Lemma4_4) (hL45 : Lemma4_5)
    (h31 : IVK_3_1a_lifted) (h72 : Prop7_2) (h73 : Lemma7_3) (h74 : Lemma7_4) (h77 : Lemma7_7)
    (hI : L4NFInduced) (hG : L4NFGood) : L4NFRest :=
  fun G _ _ z S q w ε hcen hT hw hε L₁ L₂ hpair => by
    obtain ⟨K₁, K₂, t, u, hcfg, hsets, hcore⟩ :=
      twoClass_core_cfg hII h41 h61 h66 hpnf hL44 hL45 h31 h72 h73 h74 h77 hcen hT hpair
    exact ⟨hI G z S q w ε hcen hT hw hε L₁ L₂ hpair, u, TwoClassData.of_core hcore,
      hG G z S q w ε hcen hT hw hε L₁ L₂ hpair K₁ K₂ t u hcfg hsets⟩

end CFSG.GH74.GLS.Stage1.Main
