module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248CoreDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CharPGenThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieCharPAll
import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListLie
import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Glue4
import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma63
import CFSG.GroupTheory.GLBCoreCentralQuotient
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

private theorem catRankOne_of_rankOne {d : TauCeti.ValidLieTypeIndex} {q : ℕ}
    (hchar : q = d.1.characteristic) (h : CFSG.AGLEmbedding.IsRankOneLieIndex d.1) :
    CatRankOne q (.lie d) := by
  obtain ⟨d, hv⟩ := d
  rcases h with ⟨Q, rfl⟩ | ⟨Q, rfl⟩ | ⟨m, rfl⟩
  · change Q.p = q
    simpa using hchar.symm
  · change Q.p = q
    simpa using hchar.symm
  · change q = 3
    simpa using hchar

private theorem false_of_ambiguousChev {S : Type} [Group S] [Finite S] {q p : ℕ}
    (hq2 : q ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hqp : q ≠ p)
    (h : catalogIs S (ambiguousChev q))
    (hnotR1 : ¬ CatRankOneGroup q S)
    (hVac : CoreSmallVac)
    {A : Subgroup (MulAut S)} (hAab : IsElemAbelian p A) (hA3 : p ^ 3 ≤ Nat.card A) :
    False := by
  have hp3_of (e : q = 3) : p ≠ 3 := fun hp3 => hqp (e.trans hp3.symm)
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact absurd hi (by simp [ambiguousChev])
  | alternating n hn =>
      rcases hi with ⟨h5, hq2' | hq5⟩ | ⟨h6, hq2' | hq3⟩ | ⟨h8, hq2'⟩
      · exact hq2 hq2'
      · refine hnotR1 ⟨.alternating n hn, ?_, ⟨e⟩⟩
        subst h5
        exact Or.inl ⟨rfl, hq5⟩
      · exact hq2 hq2'
      · refine hnotR1 ⟨.alternating n hn, ?_, ⟨e⟩⟩
        subst h6
        exact Or.inr ⟨rfl, hq3⟩
      · exact hq2 hq2'
  | sporadic _ => exact absurd hi (by simp [ambiguousChev])
  | lie dd =>
      obtain ⟨d, hv⟩ := dd
      change ambiguousChev q (.lie ⟨d, hv⟩) at hi
      cases d with
      | A r Q =>
        by_cases hr1 : r = 1
        · subst hr1
          rcases hi with ⟨hQ7, hq2'⟩ | ⟨hQ8, hq3⟩
          · exact hq2 hq2'
          · exact absurd hA3 (not_le.mpr (hVac p hp hp2 (hp3_of hq3) S ⟨.A 1 Q, hv⟩ ⟨e⟩
              (Or.inl ⟨Q, rfl, hQ8⟩) A hAab))
        · simp [ambiguousChev, hr1] at hi
      | twistedA r Q =>
        rcases Nat.lt_or_ge r 4 with h4 | h4
        · interval_cases r
          · exact hi.elim
          · exact hi.elim
          · exact hq2 hi.2
          · exact absurd hA3 (not_le.mpr (hVac p hp hp2 (hp3_of hi.2) S ⟨.twistedA 3 Q, hv⟩ ⟨e⟩
              (Or.inr (Or.inl ⟨Q, rfl, Or.inl hi.1⟩)) A hAab))
        · obtain ⟨r', rfl⟩ := Nat.exists_eq_add_of_le' h4
          exact hi.elim
      | B r Q => exact absurd hi (by simp [ambiguousChev])
      | C r Q => exact absurd hi (by simp [ambiguousChev])
      | D r Q => exact absurd hi (by simp [ambiguousChev])
      | twistedD r Q => exact absurd hi (by simp [ambiguousChev])
      | E6 Q => exact absurd hi (by simp [ambiguousChev])
      | E7 Q => exact absurd hi (by simp [ambiguousChev])
      | E8 Q => exact absurd hi (by simp [ambiguousChev])
      | F4 Q => exact absurd hi (by simp [ambiguousChev])
      | G2 Q => exact absurd hi (by simp [ambiguousChev])
      | twistedE6 Q => exact absurd hi (by simp [ambiguousChev])
      | trialityD4 Q => exact absurd hi (by simp [ambiguousChev])
      | suzuki m => exact absurd hi (by simp [ambiguousChev])
      | reeG2 m => exact absurd hi (by simp [ambiguousChev])
      | reeF4 m => exact absurd hi (by simp [ambiguousChev])
      | tits => exact absurd hi (by simp [ambiguousChev])

private theorem main_lie_case
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hGen : CFSG.AGLEmbedding.CharPGen3At fun d =>
      CFSG.AGLEmbedding.IsWeakSLIndex d ∨ CFSG.AGLEmbedding.IsWeakSpIndex d ∨
      CFSG.AGLEmbedding.IsSUIndex d ∨ CFSG.AGLEmbedding.IsBOddIndex d ∨
      CFSG.AGLEmbedding.IsDIndex d ∨ CFSG.AGLEmbedding.IsTwistedDIndex d ∨
      CFSG.AGLEmbedding.IsExceptionalIndex d)
    (hRank : CoreRankFour) (hVac : CoreSmallVac)
    {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    {H : Type} [Group H] [Finite H] (hH : CFSG.Open.IsQuasisimple H)
    {d : TauCeti.ValidLieTypeIndex}
    (e : (H ⧸ Subgroup.center H) ≃* CFSG.AGLEmbedding.CatGroup d)
    (hchar : q = d.1.characteristic)
    (hrn : ¬ CFSG.AGLEmbedding.IsRankOneLieIndex d.1)
    (hcp : ¬ IsCorePrimeIndex q d.1)
    (Q : Subgroup H) (hQ : IsPGroup q Q)
    (hQcard : Nat.card Q = q ^ (Nat.card H).factorization q)
    {A : Subgroup (MulAut (H ⧸ Subgroup.center H))} (hAab : IsElemAbelian p A)
    (hA3 : p ^ 3 ≤ Nat.card A) :
    4 ≤ CFSG.Open.pRank q Q ∧
      CFSG.HardMathSupport.Solomon.Coordinator.coreIn q 3 Q ⊤ = ⊤ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hqZ : ¬ q ∣ Nat.card (Subgroup.center H) := by
    intro hqZ
    have hcase := GL83.I243.CoverList.lie_case hGA hH hq hq2 hqZ d e
    rcases hcase with ⟨hne, -, -⟩ | ⟨hq3, hcov | ⟨hl4, -⟩⟩
    · exact hne hchar
    · rcases hcov with h1 | h1 | h1 | h1 | h1 | h1 |
        ⟨Q', hv', hQcard', hd⟩ | ⟨Q', hv', hQcard', hd⟩ | ⟨Q', hv', hQcard', hd⟩
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · cases hd
        have hp3 : p ≠ 3 := fun hp3 => hqp (hq3.trans hp3.symm)
        exact absurd hA3 (not_le.mpr (hVac p hp hp2 hp3 (H ⧸ Subgroup.center H) _ ⟨e⟩
          (Or.inr (Or.inl ⟨Q', rfl, Or.inr hQcard'⟩)) A hAab))
      · cases hd
        have hp3 : p ≠ 3 := fun hp3 => hqp (hq3.trans hp3.symm)
        exact absurd hA3 (not_le.mpr (hVac p hp hp2 hp3 (H ⧸ Subgroup.center H) _ ⟨e⟩
          (Or.inr (Or.inr ⟨Q', rfl, hQcard'⟩)) A hAab))
      · cases hd
        have hQp3 : Q'.p = 3 ∧ Q'.exponent = 1 :=
          (Nat.prime_three.pow_eq_iff).1 (by simpa [TauCeti.PrimePower.card_def] using hQcard')
        exact hcp ⟨Q', hQp3.1.trans hq3.symm, hQp3.2, Or.inr (Or.inr rfl)⟩
    · obtain ⟨d', hd, Q', hQp, hQexp, hd'⟩ := hl4
      cases hd
      rw [hd'] at hchar
      simp only [TauCeti.LieTypeIndex.characteristic_A] at hchar
      exact hq2 (hchar.trans hQp)
  have hfam : CFSG.AGLEmbedding.IsWeakSLIndex d ∨ CFSG.AGLEmbedding.IsWeakSpIndex d ∨
      CFSG.AGLEmbedding.IsSUIndex d ∨ CFSG.AGLEmbedding.IsBOddIndex d ∨
      CFSG.AGLEmbedding.IsDIndex d ∨ CFSG.AGLEmbedding.IsTwistedDIndex d ∨
      CFSG.AGLEmbedding.IsExceptionalIndex d := by
    refine CFSG.AGLEmbedding.exists_weak_family_of_odd hq2 hchar hrn ?_ ?_
    · rintro ⟨Q', (⟨hQp, hQexp, hd⟩ | ⟨hq3, hQp, hQexp, hd⟩)⟩
      · exact hcp ⟨Q', hQp, hQexp, Or.inr (Or.inl hd)⟩
      · rw [hd] at hchar
        simp only [TauCeti.LieTypeIndex.characteristic_twistedA] at hchar
        exact hq2 (hchar.trans hQp)
    · rintro ⟨Q', hQp, hQexp, hd⟩
      exact hcp ⟨Q', hQp, hQexp, Or.inl hd⟩
  have hQmap : IsPGroup q (Q.map (QuotientGroup.mk' (Subgroup.center H))) ∧
      Nat.card (Q.map (QuotientGroup.mk' (Subgroup.center H))) =
        q ^ (Nat.card (H ⧸ Subgroup.center H)).factorization q :=
    sylow_map_quotient hq (Subgroup.center H) Q hQ hQcard
  let T : Sylow q (H ⧸ Subgroup.center H) :=
    Sylow.ofCard (Q.map (QuotientGroup.mk' (Subgroup.center H))) hQmap.2
  have hcoreT : GLBCore q 3 (T : Subgroup (H ⧸ Subgroup.center H)) = ⊤ := by
    have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian H hH
    exact hGen (H ⧸ Subgroup.center H) hH.2 hnonab d hfam ⟨e⟩ q hq hq2 hchar hrn T
  have hcore : GLBCore q 3 (Q.map (QuotientGroup.mk' (Subgroup.center H))) = ⊤ := by
    simpa [T, Sylow.coe_ofCard] using hcoreT
  have hrankTop : 4 ≤ CFSG.Open.pRank q (⊤ : Subgroup H) := by
    have h1 := hRank (H ⧸ Subgroup.center H) d ⟨e⟩ q hq2 hchar hrn hcp
    rwa [CFSG.SectionRank.pRank_quotient_eq (Subgroup.center H) hqZ] at h1
  let TQ : Sylow q H := Sylow.ofCard Q hQcard
  have hsylow : CFSG.Open.pRank q Q = CFSG.Open.pRank q (⊤ : Subgroup H) := by
    have h := (CFSG.SectionRank.pRank_sylow TQ).1
    rwa [Sylow.coe_ofCard] at h
  refine ⟨?_, ?_⟩
  · rw [hsylow]
    exact hrankTop
  · rw [CFSG.LocalAnalysis.GLTheoremA.L63.coreIn_top_eq_glbCore]
    exact CFSG.GroupTheory.glbCore_eq_top_of_central_quotient le_rfl hq hqZ hQ (by omega) hcore

theorem coreFact_of_parts (hGA : CFSG.Open.GriessAllModelsStatement)
    (hGen : CFSG.AGLEmbedding.CharPGen3At fun d =>
      CFSG.AGLEmbedding.IsWeakSLIndex d ∨ CFSG.AGLEmbedding.IsWeakSpIndex d ∨
      CFSG.AGLEmbedding.IsSUIndex d ∨ CFSG.AGLEmbedding.IsBOddIndex d ∨
      CFSG.AGLEmbedding.IsDIndex d ∨ CFSG.AGLEmbedding.IsTwistedDIndex d ∨
      CFSG.AGLEmbedding.IsExceptionalIndex d)
    (hRank : CoreRankFour) (hExcl : CorePrimeExcl) (hVac : CoreSmallVac) : CoreFact := by
  intro p q hp hp2 hq hq2 hqp H
  intro gH fH hH hChev hnotR1 hA _hnotU3 Q hQ hQcard
  letI : Group H := gH
  letI : Finite H := fH
  obtain ⟨A, hAab, hA3⟩ := hA
  set S : Type := H ⧸ Subgroup.center H with hS
  have hChev' : IsChevSimple q S := hChev
  have hnotR1' : ¬ CatRankOneGroup q S := hnotR1
  rcases hChev' with hlie | hamb
  · rcases hlie with ⟨i, hi, ⟨e⟩⟩
    cases i with
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
    | lie d =>
        have hchar : q = d.1.characteristic := hi.symm
        by_cases hrn : CFSG.AGLEmbedding.IsRankOneLieIndex d.1
        · exact absurd ⟨.lie d, catRankOne_of_rankOne hchar hrn, ⟨e⟩⟩ hnotR1'
        · by_cases hcp : IsCorePrimeIndex q d.1
          · exact absurd hA3 (not_le.mpr (hExcl p q hp hp2 hq hq2 hqp S d ⟨e⟩ hcp A hAab))
          · exact main_lie_case hGA hGen hRank hVac hp hp2 hq hq2 hqp hH e hchar hrn hcp
              Q hQ hQcard hAab hA3
  · exact (false_of_ambiguousChev hq2 hp hp2 hqp hamb hnotR1' hVac hAab hA3).elim

end CFSG.LocalAnalysis.GLTheoremA.H248
