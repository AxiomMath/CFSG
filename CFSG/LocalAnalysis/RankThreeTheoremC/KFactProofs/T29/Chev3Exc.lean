module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3Rank
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.LocalAnalysis.SectionRank.SmallRee
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeExc
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcCensus
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofG23
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Families
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3

open TauCeti
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
  (four_le_pRank_three_of_isExcBig)

section Certified


theorem four_le_pRank_exceptional {G : Type} [Group G] [Finite G] (d : ValidLieTypeIndex)
    (hd : d.1.characteristic = 3)
    (hex : (∃ q, d.1 = .E6 q) ∨ (∃ q, d.1 = .E7 q) ∨ (∃ q, d.1 = .E8 q) ∨ (∃ q, d.1 = .F4 q) ∨
      (∃ q, d.1 = .G2 q) ∨ (∃ q, d.1 = .twistedE6 q) ∨ (∃ q, d.1 = .trialityD4 q) ∨
      (∃ m, d.1 = .reeG2 m))
    (e : G ≃* (CFSGIndex.lie d).Group) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q => simp at hex
  | twistedA r q => simp at hex
  | B r q => simp at hex
  | C r q => simp at hex
  | D r q => simp at hex
  | twistedD r q => simp at hex
  | E6 q =>
    exact four_le_pRank_three_of_isExcBig
      ⟨.E6 q, hv⟩ trivial e
  | E7 q =>
    exact four_le_pRank_three_of_isExcBig
      ⟨.E7 q, hv⟩ trivial e
  | E8 q =>
    exact four_le_pRank_three_of_isExcBig
      ⟨.E8 q, hv⟩ trivial e
  | F4 q =>
    exact four_le_pRank_three_of_isExcBig
      ⟨.F4 q, hv⟩ trivial e
  | twistedE6 q =>
    exact four_le_pRank_three_of_isExcBig
      ⟨.twistedE6 q, hv⟩ trivial e
  | trialityD4 q =>
    have hp : q.p = 3 := by simpa using hd
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hT := CFSG.HardMathSupport.Timmesfeld.Tables.Census.twistedChevalleyModel_of_bridge
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 e
    have h4 := CFSG.SectionRank.four_le_pRank_of_trialityD4Model q.exponent_pos hT
    rw [hp] at h4
    exact h4
  | G2 q =>
    have hp : q.p = 3 := by simpa using hd
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hU := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedChevalleyModel_of_bridge
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 e
    by_cases hf : 2 ≤ q.exponent
    · have h3 := CFSG.SectionRank.three_mul_le_pRank_of_G2Model hU
      rw [hp] at h3
      omega
    · have he1 : q.exponent = 1 := by
        have := q.exponent_pos
        omega
      have hU' : CFSG.Blueprint.UntwistedChevalleyModel G .G2 (3 ^ 1) := by
        have h1 : q.p ^ q.exponent = 3 ^ 1 := by rw [hp, he1]
        rw [← h1]
        exact hU
      have hCh : CFSG.Blueprint.ChevalleyExceptionalModel G .G2 3 1 :=
        ⟨⟨Nat.prime_three, le_rfl, rfl, by norm_num⟩, hU'⟩
      obtain ⟨P, -, -, hP, hcard, -⟩ :=
        CFSG.RankThree.PartTwo.Sec4.Res417Five.k417E81G23_holds G hCh
      exact CFSG.SectionRank.le_pRank (by norm_num) le_top hP (k := 4) hcard
  | suzuki m => simp at hex
  | reeG2 m =>
    have hR := CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 (S := G) m ⟨hv, ⟨e⟩⟩
    have h2 := (CFSG.SectionRank.smallReeModel_rank hR).2
    omega
  | reeF4 m => simp at hex
  | tits => simp at hex

theorem rank_dichotomy {G : Type} [Group G] [Finite G] (d : ValidLieTypeIndex)
    (hd : d.1.characteristic = 3) (e : G ≃* (CFSGIndex.lie d).Group) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) ∨
      (∃ q, d.1 = .A 1 q ∧ q.card = 27 ∧ 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)) ∨
      (∃ q, d.1 = .A 2 q ∧ q.card = 3) ∨ (∃ q, d.1 = .twistedA 2 q ∧ q.card = 3) := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q => exact rank_dichotomy_classical ⟨.A r q, hv⟩ hd (Or.inl ⟨r, q, rfl⟩) e
  | twistedA r q =>
    exact rank_dichotomy_classical ⟨.twistedA r q, hv⟩ hd (Or.inr (Or.inl ⟨r, q, rfl⟩)) e
  | B r q =>
    exact rank_dichotomy_classical ⟨.B r q, hv⟩ hd (Or.inr (Or.inr (Or.inl ⟨r, q, rfl⟩))) e
  | C r q =>
    exact rank_dichotomy_classical ⟨.C r q, hv⟩ hd
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, rfl⟩)))) e
  | D r q =>
    exact rank_dichotomy_classical ⟨.D r q, hv⟩ hd
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, rfl⟩))))) e
  | twistedD r q =>
    exact rank_dichotomy_classical ⟨.twistedD r q, hv⟩ hd
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, q, rfl⟩))))) e
  | E6 q =>
    exact Or.inl (four_le_pRank_exceptional ⟨.E6 q, hv⟩ hd (Or.inl ⟨q, rfl⟩) e)
  | E7 q =>
    exact Or.inl (four_le_pRank_exceptional ⟨.E7 q, hv⟩ hd (Or.inr (Or.inl ⟨q, rfl⟩)) e)
  | E8 q =>
    exact Or.inl (four_le_pRank_exceptional ⟨.E8 q, hv⟩ hd
      (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))) e)
  | F4 q =>
    exact Or.inl (four_le_pRank_exceptional ⟨.F4 q, hv⟩ hd
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))) e)
  | G2 q =>
    exact Or.inl (four_le_pRank_exceptional ⟨.G2 q, hv⟩ hd
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))))) e)
  | twistedE6 q =>
    exact Or.inl (four_le_pRank_exceptional ⟨.twistedE6 q, hv⟩ hd
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))))) e)
  | trialityD4 q =>
    exact Or.inl (four_le_pRank_exceptional ⟨.trialityD4 q, hv⟩ hd
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))))))) e)
  | reeG2 m =>
    exact Or.inl (four_le_pRank_exceptional ⟨.reeG2 m, hv⟩ hd
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, rfl⟩))))))) e)
  | suzuki m => simp at hd
  | reeF4 m => simp at hd
  | tits => simp at hd

end Certified

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3
