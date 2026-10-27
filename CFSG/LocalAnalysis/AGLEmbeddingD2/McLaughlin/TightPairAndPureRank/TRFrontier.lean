module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TwoPureA6U33
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PermJordan
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive
import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.BigVector
import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.Fixed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OddCentre
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightSep
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockRows
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

section AltSeven

variable {G : Type} [Group G] [Finite G]

@[expose] def PairTwoAltSeven (M L : Subgroup G) : Prop :=
  (∃ N : ℕ, (N = 12 ∨ N = 16) ∧ Nonempty (↥(barM M L) ≃* alternatingGroup (Fin N))) ∨
  (NineThreeFive M L ∧
    Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 7)))

theorem false_of_altSeven_aux (hCF : CitedFive) (hat : U33Atlas) (hJ : JordanPrimeCycle)
    (hnat : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive)
    {P : Sylow 3 G} {M A H R : Subgroup G}
    (hctx : PairStrongCtx P M A H R) {L L' : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hL' : IsWeakSBlock M (pCoreOf 2 H) L')
    (hne : barM M L ≠ barM M L')
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hreq : 2 ≤ Open.pRank 3 L → 2 ≤ Open.pRank 3 L') (hA : PairTwoAltSeven M L) : False := by
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have hpr := hctx.pair
  rcases hA with ⟨N, hN, ⟨e⟩⟩ | ⟨h5, ⟨e⟩⟩
  · obtain ⟨x, hxV, hx1, hrk⟩ :=
      CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.exists_bigVector_of_alt' h86 hnat hctx hL
      (by rcases hN with rfl | rfl <;> norm_num) e
    refine hctx.esc.false_of_pureVector hctx.d1 hctx.beta hctx.strong hxV hx1
      (hrk.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three
        (le_inf inf_le_right (inf_le_left.trans hL.le)))) fun y hy _ => ?_
    exact (CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.fixed_of_alt_pair' h86 hJ hnat hctx hL hN e
      hy).trans
      (Subgroup.card_dvd_of_le (inf_le_inf_right _ hL.le))
  · have hZ' : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
      rwa [← card_inf_centralizer_eq_card_center]
    have hodd : Odd (Nat.card (Subgroup.center ↥(barM M L))) := by
      rw [← card_inf_centralizer_eq_card_center]
      exact odd_card_center_barM hL.toIsTwoPrimeComponent
    have hcen : Subgroup.center ↥(barM M L) = ⊥ :=
      tightCentreTrivial_of_atlas hat _ hL.component.2.2 (Or.inl ⟨7, by omega, ⟨e⟩⟩) hodd hZ'
    have hr2 : 2 ≤ Open.pRank 3 L' := by
      have h1 := pRank_top_quot_center_eq hL.le hZ
      have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e
      have h3 := le_pRank_alternatingGroup_three (N := 7) (k := 2) (by norm_num)
      exact hreq (by omega)
    have hnA8 : ¬ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃*
        alternatingGroup (Fin 8)) := by
      rintro ⟨e8⟩
      have := Nat.card_congr (e.symm.trans e8).toEquiv
      rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin] at this
      simp [Nat.factorial] at this
    obtain ⟨x, hxV, hx1, -, hrk⟩ := exists_sep_of_tightRow' hCF hat h86 hctx hL hL' hne hZ hr2
      (Or.inr (Or.inl ⟨h5, ⟨e⟩⟩)) hcen hnA8
    refine hctx.esc.false_of_pureVector hctx.d1 hctx.beta hctx.strong hxV hx1 hrk fun y hy _ => ?_
    exact (fixed_of_nineThreeFive_pair h86 hpr hL h5 hy).trans
      (Subgroup.card_dvd_of_le (inf_le_inf_right _ hL.le))

end AltSeven

end CFSG.AGLEmbeddingD2.McLaughlin
