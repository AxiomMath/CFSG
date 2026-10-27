module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneReductions
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSpor
public import CFSG.LocalAnalysis.AGLEmbedding.AltCaseThreeK
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporOut
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeOut
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Assembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BCoverFiveScal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporRowsB
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporRowsM
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporRowsSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporRowsTc

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section AltSporCert


theorem not_dvd_card_outer_spor {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {s : TauCeti.SporadicName} (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    ¬ p ∣ Nat.card (Outer K) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  obtain ⟨k, hk⟩ := CFSG.ComponentClassification.HarrisLit.T1.SporRow.sporadic_outer_two_pow K
    ⟨s, ⟨e.trans b.symm⟩⟩
  intro hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow (hdvd.trans hk)))

theorem pRank_le_two_spor {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {s : TauCeti.SporadicName} (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hs : ¬ P1ThreeSporList p s ∨ (s = .M22 ∧ p = 3) ∨ (s = .Fi24Prime ∧ p = 7) ∨
      (s = .M ∧ p = 13)) :
    Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  have f : K ≃* CFSG.Blueprint.NativeSporadic.Carrier s := e.trans b.symm
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier s) := Finite.of_equiv _ f.toEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt f]
  suffices hmid : SporMidAt (CFSG.Blueprint.NativeSporadic.Carrier s) p by
    rcases hmid with h3 | ⟨h4, hpair, -⟩
    · exact CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd (k := 2) hp h3
    · exact pRank_le_two_of_hasNoncommPair hp h4 hpair
  rcases hs with hl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact sporMidAt_of_offList (card_carrier_eq_sporOrd CFSG.Milestones.fam_m_finiteness) s p hp
      hp2 hl
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact KFactProofs.KlingenIdentSporAux.rankData_M22_three
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact KFactProofs.KlingenIdentSporAux.rankData_Fi24_seven
  · haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    haveI := CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
    exact KFactProofs.KlingenIdentSporAux.rankData_M_thirteen (MulEquiv.refl _)

private theorem weakCore_eq_top_of_equiv {K X : Type} [Group K] [Finite K] [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] (e : K ≃* X)
    (hX : ∀ T : Sylow p X, GLBWeakCore p (T : Subgroup X) = ⊤) (T : Sylow p K) :
    GLBWeakCore p (T : Subgroup K) = ⊤ := by
  let T' : Sylow p X := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hT : (T : Subgroup K) = (T' : Subgroup X).map e.symm.toMonoidHom := by
    ext x
    simp [T']
  exact glbWeakCore_eq_top_of_mulEquiv Fact.out e.symm hT (hX T')

theorem weakCore_eq_top_spor
    {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {s : TauCeti.SporadicName} (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hs : P1ThreeSporList p s) (hJ3 : ¬ (s = .J3 ∧ p = 3)) (hM22 : ¬ (s = .M22 ∧ p = 3))
    (hFi : ¬ (s = .Fi24Prime ∧ p = 7)) (hM : ¬ (s = .M ∧ p = 13)) (T : Sylow p K) :
    GLBWeakCore p (T : Subgroup K) = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  have e' : K ≃* CFSG.Blueprint.NativeSporadic.Carrier s := e.trans b.symm
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier s) := Finite.of_equiv _ e'.toEquiv
  have hMs : s = .M → IsSimpleGroup K := by
    rintro rfl
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
      CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
    exact e'.isSimpleGroup
  rcases hs with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, rfl⟩
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact (hJ3 ⟨rfl, rfl⟩).elim
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_McL_three.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_Suz_three.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_ON_three.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_Co1_three.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_Co2_three.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_Co3_three.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_Fi22_three.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_Fi23_three.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_Fi24_three.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_HN_three.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_Ly_three.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_Th_three.1 T
    · have hc : 2 < Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .B) := by
        rw [CFSG.EvenSmallLie.Child3.card_carrier .B (by decide) (by decide)]
        decide
      exact weakCore_eq_top_of_equiv e'
        (KFactProofs.KlingenIdentSporAux.genData_B_three hc).1 T
    · haveI := hMs rfl
      obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e'
      obtain ⟨x, y, -, -, hxy, -⟩ :=
        CFSG.AGLEmbedding.Norton.MON11_13.hasNoncommPair_thirteen_of_mulEquiv_Gmat ε
      have hZ : Subgroup.center K = ⊥ :=
        TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative fun h =>
          hxy (h.is_comm.comm x y)
      let e'' : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M :=
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e'
      haveI : Nontrivial (CFSG.Blueprint.NativeSporadic.Carrier .M) := e'.injective.nontrivial
      haveI : Nontrivial (K ⧸ Subgroup.center K) := e''.symm.injective.nontrivial
      exact KFactProofs.KlingenIdentSporAux.weakCore_eq_top_M_three e''
        (by rw [hZ]; exact IsPGroup.of_bot) T
    · exact (hM22 ⟨rfl, rfl⟩).elim
  · rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_Co1_five.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_Ly_five.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_HN_five.1 T
    · exact weakCore_eq_top_of_equiv e'
        KFactProofs.KlingenIdentSporAux.genData_B_five_of_scal.1 T
    · haveI := hMs rfl
      exact (KFactProofs.KlingenIdentSporAux.genData_M_five e').1 T
  · rcases hs with rfl | rfl
    · exact (hFi ⟨rfl, rfl⟩).elim
    · haveI := hMs rfl
      exact (KFactProofs.KlingenIdentSporAux.genData_M_seven e').1 T
  · exact (hM ⟨rfl, rfl⟩).elim

variable {p : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {P : Sylow p G}
  {E : Subgroup G}

theorem Hyp.threeOne_alt (H : Hyp p K P E) (h3 : 3 ≤ Open.pRank p (P : Subgroup G))
    (hnot : ¬ K ≤ GLBWeakCore p (P : Subgroup G)) (hC : Subgroup.centralizer (K : Set G) = ⊥)
    (n : ℕ) (hn : 5 ≤ n) (e : K ≃* (TauCeti.CFSGIndex.alternating n hn).Group) :
    OnThreeOneList p K := by
  have e' : K ≃* alternatingGroup (Fin n) := e
  have hPK : (P : Subgroup G) ≤ K := H.le_of_not_dvd_card_outer hC
    (not_dvd_card_outer_of_mulEquiv_of_not_dvd e'
      (not_dvd_card_outer_alternatingGroup n hn p H.prime H.ne_two))
  have hK3 : 3 ≤ Open.pRank p (⊤ : Subgroup K) := h3.trans (H.pRank_le_of_le hPK)
  by_cases h3p : 3 * p + 1 ≤ n
  · exact (hnot (H.le_weakCore_of_sylow fun T =>
      weakCore_eq_top_of_three_mul_lt H.prime H.ne_two h3p e' T)).elim
  · by_cases h23 : n = 2 * p ∨ n = 3 * p
    · exact ⟨.alternating n hn, Or.inr (Or.inr ⟨n, hn, rfl, h23⟩), ⟨e⟩⟩
    · have := pRank_le_two_of_lt H.prime e' (by omega) (⊤ : Subgroup K)
      omega

theorem Hyp.threeOne_spor
    (H : Hyp p K P E) (h3 : 3 ≤ Open.pRank p (P : Subgroup G))
    (hnot : ¬ K ≤ GLBWeakCore p (P : Subgroup G)) (hC : Subgroup.centralizer (K : Set G) = ⊥)
    (s : TauCeti.SporadicName) (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    OnThreeOneList p K := by
  have hPK : (P : Subgroup G) ≤ K :=
    H.le_of_not_dvd_card_outer hC (not_dvd_card_outer_spor H.prime H.ne_two e)
  have hK3 : 3 ≤ Open.pRank p (⊤ : Subgroup K) := h3.trans (H.pRank_le_of_le hPK)
  by_cases hs : P1ThreeSporList p s
  · by_cases hJ3 : s = .J3 ∧ p = 3
    · obtain ⟨rfl, rfl⟩ := hJ3
      exact ⟨.sporadic .J3, Or.inl (Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩), ⟨e⟩⟩
    by_cases hsmall : (s = .M22 ∧ p = 3) ∨ (s = .Fi24Prime ∧ p = 7) ∨ (s = .M ∧ p = 13)
    · have := pRank_le_two_spor H.prime H.ne_two e (Or.inr hsmall)
      omega
    · exact (hnot (H.le_weakCore_of_sylow fun T => weakCore_eq_top_spor H.prime H.ne_two e hs hJ3
        (fun h => hsmall (Or.inl h)) (fun h => hsmall (Or.inr (Or.inl h)))
        (fun h => hsmall (Or.inr (Or.inr h))) T)).elim
  · have := pRank_le_two_spor H.prime H.ne_two e (Or.inl hs)
    omega

end AltSporCert

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
