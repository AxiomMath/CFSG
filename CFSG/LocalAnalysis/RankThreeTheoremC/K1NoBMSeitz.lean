module

public import CFSG.LocalAnalysis.RankThreeTheoremC.K1NoBMDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSERankTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.D2Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporSmall

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Blueprint CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.RankThreeTheoremC (NotBM StronglyEmbeddedRankTwoKFactNoBM)

@[expose] def KFactSmallIdentNoBM : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → NotBM K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      pRank p (⊤ : Subgroup K) ≤ 2 → IsSmallStrongP p K

theorem smallIdentSporAt_of_rows_noB (hrows : SporProvedRows) (hFi : SporFi24SevenRow)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hcard : ∀ s : TauCeti.SporadicName, s ≠ .M →
      Nat.card (NativeSporadic.Carrier s) = d2SporadicOrder s)
    (s : TauCeti.SporadicName) (hs : s ≠ .M) (hsB : s ≠ .B) (hHS5 : SporGammaOneAt .HS 5) :
    SmallIdentSporAt s := by
  intro K _ _ _ _ ⟨e⟩ p hp hp2 T hT hΓ hr
  obtain ⟨f⟩ := hbr s
  have e' : K ≃* NativeSporadic.Carrier s := e.trans f.symm
  by_cases hsq : p ^ 2 ∣ d2SporadicOrder s
  · rcases (d2SporadicSq_iff s p).1 ⟨hs, hp, hp2, hsq⟩ with hpr | hleaf | hopen
    · exact (false_of_d2DatumPlus hp hp2 (hrows s p hpr K ⟨e'⟩) T hT hΓ hr).elim
    · simp only [d2SporadicLeafList, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hleaf
      rcases hleaf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl ⟨e⟩)⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ⟨e⟩⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨e⟩⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨e⟩)⟩))))
    · simp only [d2SporadicOpenList, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hopen
      rcases hopen with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (hHS5 K ⟨e⟩ T) hΓ
      · exact (false_of_d2DatumPlus hp hp2 (Or.inl (hFi K ⟨e'⟩)) T hT hΓ hr).elim
      · exact absurd rfl hsB
  · refine absurd (isCyclic_sylow_of_not_sq_dvd hp T ?_) hT
    rwa [Nat.card_congr e'.toEquiv, hcard s hs]

theorem kFactSmallIdentNoBM_of_families (halt : SmallIdentAlt) (hcp : SmallIdentLieCharP)
    (hoff : SmallIdentLieOffChar) (hspor : ∀ s, s ≠ .B → s ≠ .M → SmallIdentSporAt s) :
    KFactSmallIdentNoBM := by
  intro K _ _ hs hnab hcat hBM p hp hp2 T hT hΓ hr
  have hr' : Open.pRank p (⊤ : Subgroup K) ≤ 2 :=
    (CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp (⊤ : Subgroup K)).symm.le.trans hr
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic q hq => exact (not_nonempty_mulEquiv_zmod hnab ⟨e⟩).elim
  | alternating n hn => exact halt K n hn ⟨e⟩ p hp hp2 T hT hΓ hr'
  | lie d =>
    by_cases hc : p = d.1.characteristic
    · exact hcp K hs hnab d ⟨e⟩ p hc hp hp2 T hT hΓ hr'
    · exact hoff K hs hnab d ⟨e⟩ p hc hp hp2 T hT hΓ hr'
  | sporadic s =>
    have hsB : s ≠ .B := by
      rintro rfl
      exact hBM.1 ⟨e⟩
    have hsM : s ≠ .M := by
      rintro rfl
      exact hBM.2 ⟨e⟩
    exact hspor s hsB hsM K hs hnab ⟨e⟩ p hp hp2 T hT hΓ hr'

theorem stronglyEmbeddedRankTwoKFactNoBM_of_smallIdent (h : KFactSmallIdentNoBM) :
    StronglyEmbeddedRankTwoKFactNoBM := by
  intro K _ _ hs hnab hcat hBM p hp hp2 T hrk hΓ
  have : Fact p.Prime := ⟨hp⟩
  have hnc : ¬ IsCyclic (T : Subgroup K) := by
    intro hcyc
    have h1 := openPRank_le_one_of_isCyclic hp (T : Subgroup K)
    rw [hrk] at h1
    omega
  have hglb : CFSG.Open.GLBCore p 1 (T : Subgroup K) ≠ ⊤ := by
    rw [← CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeGamma_eq_glbCore]
    exact hΓ
  have hr2 : CFSG.Open.pRank p (⊤ : Subgroup K) = 2 :=
    (CFSG.SectionRank.pRank_sylow T).1.symm.trans hrk
  have hr : CFSG.pRank p (⊤ : Subgroup K) ≤ 2 := by
    rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp]
    exact hr2.le
  exact isRankTwoSEGroup_of_isSmallStrongP hp hp2 (h K hs hnab hcat hBM p hp hp2 T hnc hglb hr)

end CFSG.AGLEmbedding
