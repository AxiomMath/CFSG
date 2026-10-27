module

public import CFSG.ClassicalInvolution.Asc77.AscT8YC1
public import CFSG.ClassicalInvolution.Asc77.AscT8X5
import CFSG.ClassicalInvolution.Asc77.AscT8YC2Eng
public import CFSG.ClassicalInvolution.Asc77.AscT8YA2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Balance.Theorem5

namespace T8YY

variable (p f : ℕ) [Fact p.Prime]

@[expose] def LayerFrattiniFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        ¬ DConnected (T8.layerFamQ Ω (z * t)) → ∀ F : FrameData Ω W K J z t,
          ∀ c ∈ Subgroup.centralizer ({z * t} : Set G),
            ∃ o ∈ oddCoreOf (T8.layerJoin Ω (z * t)), conjSub (o * c) F.vGroup = F.vGroup

@[expose] def PureBCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        (∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
          ¬ DConnected (T8.layerFamQ Ω (z * s))) →
        alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ →
          ∃ A : Subgroup G, A ≤ (S : Subgroup G) ∧ A ≠ ⊥ ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
            StronglyClosedIn A (S : Subgroup G)

variable {p f}


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem centralizer_le_normalizer_alpha_of_edge [IsSimpleGroup G] (hV : LayerFrattiniFact p f)
    (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hdisc : ¬ DConnected Ω) (hframe : ∃ A₀, FuzzyFrameOn p f Ω A₀)
    (hN : sigmaNorm Ω K ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G))
    {M : Subgroup G} (hM : M ∈ omegaNbr Ω K) {s : G} (hs' : IsUniqueInvolution M s) :
    Subgroup.centralizer ({z * s} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  by_cases hconn : DConnected (T8.layerFamQ Ω (z * s))
  · exact centralizer_le_normalizer_alpha_of_nbr hs hμ hne hdisc hframe hN hM hs' hconn
  · have hp : p ≠ 2 := hs.stand.odd
    have hq : 5 ≤ p ^ f := hs.stand.five
    have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
    obtain ⟨S', R', T', W', hstd⟩ :=
      c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
    have hμ' := muIsoWylD4_transfer hp hq hΩ hs.hW.1 hstd.hW.1 hμ
    have hnc' : ¬ DbarConnected Ω W' := T8X.not_dbarConnected_of_ne hstd hne
    obtain ⟨F'⟩ := exists_frameData hstd hμ' hnc'
    have hfr := hV G Ω K M S' R' T' W' z s hstd hdisc hμ' hne hconn F'
    have hα : alphaOf (Subgroup.closure ({s, z} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) :=
      (T8U.alphaOf_eq_of_omegaNbr_frame hs.stand hs.noTwins hframe hs.hz hs' hs.ht hM hs.hJ).symm
    rw [← hα]
    exact centralizer_le_normalizer_alpha_of_frattini hstd F' hfr

theorem alphaOf_eq_bot_of_frattini [IsSimpleGroup G] (hV : LayerFrattiniFact p f)
    (hs : Std8 p f Ω K J S R T W z t) (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) :
    alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ := by
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have hframe := exists_fuzzyFrame hs hμ hnc
  have hN := sigmaNorm_le_normalizer_alpha hs hframe
  exact alphaOf_eq_bot_of_frattiniE hs.hz hN
    (fun hM => fun hs' => centralizer_le_normalizer_alpha_of_edge hV hs hμ hne hdisc hframe hN hM hs')
    (h274_eq_top hs hdisc hμ hne) (alphaOf_odd hs hμ hne)

theorem false_of_caseA_of_alpha_bot [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (hconn : DConnected (T8.layerFamQ Ω (z * t)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) : False := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have hY : oddCoreOf (T8.layerJoin Ω (z * t)) ≤ sigmaNorm Ω K :=
    T8.oddCoreOf_layerJoin_le_of_alpha hs hα
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hKx : T8.XMem Ω (z * t) K := T8.xMem_zt hs
  have hY1 : T8.layerJoin Ω (z * t) ≤ sigmaNorm Ω K :=
    layerJoin_le_sigmaNorm_of_lift hp hq hΩ hx hKx hY hconn
  have hC : Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K :=
    T8.centralizer_le_sigmaNorm_of_layerJoin_le hs hY1
  obtain ⟨F⟩ := exists_frameData hs hμ hnc
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hM := F.mgrp_le_centralizer c 0 1
  rw [F.hz0, F.hz1] at hM
  exact mgrp_not_le_sigmaNorm hs hne (hM.trans hC)

theorem w2caseB_of_facts (hV : LayerFrattiniFact p f) (hP : PureBCase p f) : T8X.W2CaseB p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne _
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have hframe := exists_fuzzyFrame hs hμ hnc
  have hα := alphaOf_eq_bot_of_frattini hV hs hdisc hμ hne
  by_cases huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      ¬ DConnected (T8.layerFamQ Ω (z * s))
  · exact hP G Ω K J S R T W z t hs hdisc hμ hne huni hα
  · exfalso
    push Not at huni
    obtain ⟨M, hM, s, hs', hconnM⟩ := huni
    obtain ⟨S', R', T', W', hstd⟩ :=
      c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
    have hμ' := muIsoWylD4_transfer hp hq hΩ hs.hW.1 hstd.hW.1 hμ
    have hα' : alphaOf (Subgroup.closure ({s, z} : Set G)) = ⊥ := by
      rw [(T8U.alphaOf_eq_of_omegaNbr_frame hs.stand hs.noTwins hframe hs.hz hs' hs.ht hM
        hs.hJ).symm]
      exact hα
    exact false_of_caseA_of_alpha_bot hstd hμ' hne hconnM hα'

end T8YY

end CFSG.ClassicalInvolution.Asc77
