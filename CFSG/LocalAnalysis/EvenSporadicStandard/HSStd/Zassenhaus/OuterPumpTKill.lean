module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTKillSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpKill
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.LitX

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.HSStd CFSG.Open
  CFSG.Assembly.LowTwoRank

@[expose] def SporadicInvComp (G : Type) [Group G] : Prop :=
  ∃ (t : G) (L : Subgroup G) (s : TauCeti.SporadicName), orderOf t = 2 ∧
    Solomon78.IsCompIn L (centralizer ({t} : Set G)) ∧ IsSporadic (↥L ⧸ center ↥L) s

section Cases

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem false_of_genQuaternion_of_comp [IsSimpleGroup G] (thm24_1 : Sol78Thm24_1Use)
    (hlie : Hyp.OddLieCompNotSporadic) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hHS : 44352000 ∣ Nat.card G) (hM : CFSG.Open.standardComponentIsStandard M)
    (S : Sylow 2 (centralizer (M : Set G)))
    (hq : IsGenQuaternion ↥(S : Subgroup ↥(centralizer (M : Set G))))
    (hcomp : SporadicInvComp G) : False := by
  have hfs : FStarSimple (⊤ : Subgroup G) := fStarSimple_top G hnonab
  have hodd := thm24_1 G ⊤ hfs (not_card_top_dvd_95040_of_hs_dvd hHS) M
    (solStd_of_standardComponentIsStandard hM) ⟨S, hq⟩
  obtain ⟨t, L, s, ht, hL, hs⟩ := hcomp
  exact hlie G ⊤ hfs hodd t ht L hL s hs

theorem stdHyp_of_rank_one_of_comp (thm24_1 : Sol78Thm24_1Use) (hlie : Hyp.OddLieCompNotSporadic)
    (hsimp : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a) (hHS : 44352000 ∣ Nat.card G)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hbal : ∀ t : G, orderOf t = 2 →
      CFSG.Open.standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    (hM : CFSG.Open.standardComponentIsStandard M) (hZ : IsPGroup 2 (center ↥M))
    (hcomp : SporadicInvComp G) (hr : CFSG.Open.pRank 2 (centralizer (M : Set G)) ≤ 1) :
    StdHyp G M ∧ ∀ P : Sylow 2 (centralizer (M : Set G)),
      IsCyclic (P : Subgroup (centralizer (M : Set G))) := by
  have hcyc : ∀ P : Sylow 2 (centralizer (M : Set G)),
      IsCyclic (P : Subgroup (centralizer (M : Set G))) := by
    intro P
    rcases Hyp.isCyclic_or_genQuaternion_of_pRank_le_one P.isPGroup'
        (pRank_sylow_le_one_of_le_one hr P) with hc | hq
    · exact hc
    · exact (false_of_genQuaternion_of_comp thm24_1 hlie hnonab hHS hM P hq hcomp).elim
  obtain ⟨P⟩ : Nonempty (Sylow 2 (centralizer (M : Set G))) := inferInstance
  exact ⟨⟨hsimp, hnonab, hK, hM, hbal, ⟨P, hcyc P⟩, hZ⟩, hcyc⟩

theorem false_of_standard_hn_loc (hCTB : CentralTwoBound)
    (hLE : ∀ L : Subgroup G, StdHyp G L → ¬ IsSporadic ↥L .HN) (h : StdHyp G M)
    (e : IsSporadic (↥M ⧸ center ↥M) .HN) : False := by
  have hb := (hCTB ↥M h.standard.1 h.centerTwo .HN e).1
  have h1 : Nat.card (center ↥M) = 1 := Nat.dvd_one.1 (by simpa [twoPartBound] using hb)
  exact hLE M h (isSporadic_of_center_eq_bot (Subgroup.eq_bot_of_card_eq _ h1) e)

theorem false_of_a10_of_pair (hSI : SolomonIAltCentralizer) (hKG : KGA10A8) {K J : Subgroup G}
    (h : StdHyp G M) (hZ : center ↥M = ⊥)
    (hA10 : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 10)))
    (hKM : K ≤ M) (hK : Nonempty (↥K ≃* alternatingGroup (Fin 8)))
    (hJ : J ≤ centralizer (K : Set G)) (hJ8 : Nonempty (↥J ≃* alternatingGroup (Fin 8))) :
    False := by
  let eM : ↥M ≃* ↥M ⧸ center ↥M :=
    MulEquiv.ofBijective (QuotientGroup.mk' (center ↥M))
      ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk']; exact hZ),
        QuotientGroup.mk'_surjective _⟩
  exact false_of_sylow_trick_a10 hKG h.standard hA10
    (hSI G M h 10 (by norm_num) ⟨eM.trans hA10.some⟩) hKM hK hJ hJ8

end Cases

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
