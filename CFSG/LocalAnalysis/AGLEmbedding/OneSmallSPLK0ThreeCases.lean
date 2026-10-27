module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeChevTwo
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeak
import CFSG.LocalAnalysis.AGLEmbedding.AltCaseThreeK
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0ThreeKill
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0ThreeKlingen

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def IsP1ChevTwoSurvivor (p : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q) ∨
  (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ (d.1 = .B 2 q ∨ d.1 = .G2 q)) ∨
  (p = 5 ∧ d.1 = .reeF4 2)


theorem D1Escape.caseThree_cases (hβ : KFactBeta)
    (hα : KFactAlphaW) {G : Type} [Group G] [Finite G] (hglob : D1Global G) {p : ℕ}
    [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G}
    (hloc : D1Local p P M) (h : D1Escape p P M H R)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (hRbar : (Rbar : Subgroup _) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hred : ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))))
    (hcat : CatalogSimpleSections (H ⧸ primeComplementCore (G := H) p))
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hKl : KFactKlingenSpFour)
    (hin : KFactChevTwoInnerGen) (hout : KFactChevTwoOuterGen)
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hSF : SporCaseThreeKFacts)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hnc : ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
      orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) :
    (∃ d : TauCeti.ValidLieTypeIndex,
        ((∃ n, IsLinTwoIndex p n d) ∨ IsUnitaryIndex p d ∨ IsReeGTwoIndex p d) ∧
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      (∃ d : TauCeti.ValidLieTypeIndex, IsP1ChevTwoSurvivor p d ∧
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      (Subgroup.center K = ⊥ ∧
        Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin (3 * p)))) ∨
      (p = 3 ∧ Subgroup.center K = ⊥ ∧
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) := by
  have hp : p.Prime := Fact.out
  have hKD : ¬ HasKlingenData p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) :=
    fun hk => h.false_of_klingen hβ hα hglob hloc Rbar hRbar hk
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hmem := ReducedNongeneration.mem_of_mem_centralizer_of_unique hK huniq hcent
  have hZp : IsPGroup p (Subgroup.center K) :=
    isPGroup_center_of_isComponentOf hp hred.core_eq_bot hK
  have hZc : IsCyclic (Subgroup.center K) := hred.isCyclic_center_of_unique hK huniq
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have : Finite (MulAut K) := MulEquiv.finite_left
  obtain ⟨i, ⟨e⟩⟩ := hcat.isCatalogGroup_center_quotient hK
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K
    hK.2.2
  cases i with
  | cyclic q hq => exact (not_nonempty_mulEquiv_zmod hnab ⟨e⟩).elim
  | alternating n hn =>
    have hn3 := hP1A p _ Rbar _ hred hcat K hK huniq hnc hcent n hn ⟨e⟩
    subst hn3
    by_cases hZ : Subgroup.center K = ⊥
    · exact Or.inr (Or.inr (Or.inl ⟨hZ, ⟨e⟩⟩))
    · exfalso
      have hOutQ : ¬ p ∣ Nat.card (Outer (K ⧸ Subgroup.center K)) := by
        rw [Nat.card_congr (equivalence e).toEquiv]
        exact not_dvd_card_outer_alternatingGroup _ hn p hp hred.ne_two
      exact hred.false_of_caseThreeKFact hK huniq hnc hcent hKD
        (not_dvd_card_outer_of_quotient hOutQ) s2Lemma klingenTransport
        (altCaseThreeKFacts K hK.2.2 _ hn ⟨e⟩ p hred.ne_two hZp hZc (fun h' => hZ h'.2))
  | sporadic s =>
    by_cases hJ : s = .J3 ∧ p = 3 ∧ Subgroup.center K = ⊥
    · obtain ⟨rfl, hp3, hZ⟩ := hJ
      exact Or.inr (Or.inr (Or.inr ⟨hp3, hZ, ⟨e⟩⟩))
    · exfalso
      have : Finite (TauCeti.CFSGIndex.sporadic s).Group := Finite.of_equiv _ e.toEquiv
      have : Finite (MulAut (TauCeti.CFSGIndex.sporadic s).Group) := MulEquiv.finite_left
      have hOutQ : ¬ p ∣ Nat.card (Outer (K ⧸ Subgroup.center K)) := by
        rw [Nat.card_congr (equivalence e).toEquiv]
        exact hOutS s p hp hred.ne_two
      exact hred.false_of_caseThreeKFact hK huniq hnc hcent hKD
        (not_dvd_card_outer_of_quotient hOutQ) s2Lemma klingenTransport
        (hSF K hK.2.2 s ⟨e⟩ p hred.ne_two hZp hZc hJ)
  | lie d =>
    have hinner : p = 3 → IsChevTwoInnerIndex d → False := by
      rintro rfl hdi
      exact hred.false_of_weakCore_eq_top hK huniq (hin d hdi K hK.2.2 ⟨e⟩ hZp hZc)
    have houter : p = 3 → IsChevTwoOuterIndex d → False := by
      rintro rfl hdo
      exact hred.false_of_le_weakCore hK huniq hcent e (hout.1 d hdo)
        (hout.2 d hdo _ K hKn hK.2.2 ⟨e⟩
          (isPGroup_centralizer_of_forall_mem hp hred.ne_two hred.core_eq_bot hKn hmem)
          (fun c hc hcp => mem_map_center_of_mem_of_mem_centralizer (hmem c hc hcp) hc)
          Rbar hred.three_le_pRank)
    rcases hP1L p _ Rbar _ hred hcat K hK huniq hnc hcent d ⟨e⟩ with h1 | h1 | h1 | h1 | h1
    · exact Or.inl ⟨d, Or.inl h1, ⟨e⟩⟩
    · exact Or.inl ⟨d, Or.inr (Or.inl h1), ⟨e⟩⟩
    · exact Or.inl ⟨d, Or.inr (Or.inr h1), ⟨e⟩⟩
    · exact (hKD (hKl p _ Rbar _ hred hcat K hK huniq hnc hcent d h1 ⟨e⟩)).elim
    · rcases h1 with ⟨hp3, q, hq, hq1, h | h | h | h | h | h | h | h⟩ |
        ⟨hp3, q, hq, hq3, h | h | h | h⟩ | ⟨hp5, h⟩
      · exact Or.inr (Or.inl ⟨d, Or.inl ⟨hp3, q, hq, hq1, h⟩, ⟨e⟩⟩)
      · exact (hinner hp3 ⟨q, hq, hq1, Or.inl h⟩).elim
      · exact (hinner hp3 ⟨q, hq, hq1, Or.inr (Or.inl h)⟩).elim
      · exact (hinner hp3 ⟨q, hq, hq1, Or.inr (Or.inr (Or.inl h))⟩).elim
      · exact (hinner hp3 ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩).elim
      · exact (hinner hp3 ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩).elim
      · exact (hinner hp3 ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩).elim
      · exact (houter hp3 (Or.inl ⟨q, hq, hq1, h⟩)).elim
      · exact Or.inr (Or.inl ⟨d, Or.inr (Or.inl ⟨hp3, q, hq, hq3, Or.inl h⟩), ⟨e⟩⟩)
      · exact Or.inr (Or.inl ⟨d, Or.inr (Or.inl ⟨hp3, q, hq, hq3, Or.inr h⟩), ⟨e⟩⟩)
      · exact (houter hp3 (Or.inr ⟨q, hq, hq3, Or.inl h⟩)).elim
      · exact (houter hp3 (Or.inr ⟨q, hq, hq3, Or.inr h⟩)).elim
      · exact Or.inr (Or.inl ⟨d, Or.inr (Or.inr ⟨hp5, h⟩), ⟨e⟩⟩)

end CFSG.AGLEmbedding
