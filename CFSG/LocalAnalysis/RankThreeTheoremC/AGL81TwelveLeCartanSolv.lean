module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeCartanRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LargeFieldProof
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LnTwoCentralizerAbsHolds
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveRanksNotLe
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveRanksLeOrth

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

theorem card_eq_two_or_four_le {q : TauCeti.PrimePower} (hp : q.p = 2) :
    (q.card = 2 ∧ q.exponent = 1) ∨ 4 ≤ q.card := by
  rcases Nat.lt_or_ge q.exponent 2 with h | h
  · have h1 : q.exponent = 1 := by
      have := q.exponent_pos
      omega
    left
    refine ⟨?_, h1⟩
    rw [TauCeti.PrimePower.card_def, hp, h1]
    norm_num
  · right
    rw [TauCeti.PrimePower.card_def, hp]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h

theorem isLieOver_of_card_center_eq_one {Y : Type} [Group Y] [Finite Y]
    {d : TauCeti.ValidLieTypeIndex} {f : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    {q : TauCeti.PrimePower} (hqp : q.p = 2) (hqe : q.exponent = 1) (hdq : d.1 = f q)
    (e : Y ⧸ center Y ≃* (TauCeti.CFSGIndex.lie d).Group) (hc : Nat.card (center Y) = 1) :
    IsLieOver Y f 2 1 := by
  have hbot : center Y = ⊥ := Subgroup.eq_bot_of_card_eq _ hc
  exact ⟨d, ⟨q, hqp, hqe, hdq⟩,
    ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans e⟩⟩


theorem solvThree_case (hGA : GriessAllModelsStatement) (h3 : KFactTwelveLeSolvThree)
    {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {β : A} (hY : Open.IsQuasisimple ↥Y)
    (hO : pCoreOf 2 Y = ⊥) {d : TauCeti.ValidLieTypeIndex} (hd : IsClassicalOrG2Index d.1)
    (e : ↥Y ⧸ center ↥Y ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hB2 : ¬ IsLieOf ParabCensus.IdxBTwo (↥Y ⧸ center ↥Y)) (hP : IsParabolicTwo Y P)
    (hPY : P ≠ Y) (hSyl : ¬ IsSylowTwoOf (pCoreOf 2 P) Y) (hβ3 : orderOf β = 3)
    (hβY : β ∈ normalizer (Y : Set A)) (hnc : ¬ ∀ y ∈ Y, β * y = y * β)
    (hrk : Open.pRank 3 Y ≤ 3) (hnoJ : ∀ J : Subgroup A, J ≤ P → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J) :
    (∃ D : Subgroup A, Open.IsComponentOf D (Y ⊓ centralizer ({β} : Set A)) ∧
        3 ∣ Nat.card D) ∨
      ((IsLieOver (↥Y ⧸ center ↥Y) (.twistedA 3) 2 1 ∨ IsLieOver ↥Y (.twistedD 4) 2 1) ∧
        ∀ T : Subgroup A, T ≤ P → IsPGroup 3 T → Nat.card T ≤ 9) := by
  classical
  haveI : Group.IsPerfect ↥Y := ⟨hY.1⟩
  have hodd : Odd (Nat.card (center ↥Y)) := ParabCensus.odd_card_center_of_pCoreOf_eq_bot hO
  have hβ3' : β ^ 3 = 1 := by
    have h := pow_orderOf_eq_one β
    rwa [hβ3] at h
  have hnc' : ¬ Y ≤ centralizer ({β} : Set A) := fun h =>
    hnc fun y hy => mem_centralizer_iff.1 (h hy) β (Set.mem_singleton β)
  have hq4 : LieField d.1 < 4 := by
    by_contra hge
    obtain ⟨J, hJP, hJperf, hJ3⟩ :=
      largeFieldParabolic_proved A Y P hY d hd (by omega) ⟨e⟩ hP hSyl
    exact hnoJ J hJP hJperf hJ3
  have hcenter : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (center ↥Y) →
      (∃ r q, d.1 = .A r q ∧ ℓ ∣ q.card - 1) ∨ (∃ r q, d.1 = .twistedA r q ∧ ℓ ∣ q.card + 1) := by
    intro ℓ hℓ hℓd
    have hℓ2 : ℓ ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hℓd)
    exact AGLEmbedding.ToralCensus.prime_dvd_torus_of_dvd_card_center hGA d hd e hℓ hℓ2 hℓd
  obtain ⟨d', hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  cases d' <;> try exact hd.elim
  ·
    rename_i r q
    have hqp : q.p = 2 := hd
    simp only [LieField] at hq4
    rcases card_eq_two_or_four_le hqp with ⟨hc2, hqe⟩ | h4
    swap
    · omega
    have hZ : Nat.card (center ↥Y) = 1 := by
      by_contra hne
      obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hne
      rcases hcenter ℓ hℓ hℓd with ⟨r', q', hdq, hdvd⟩ | ⟨r', q', hdq, -⟩
      · injection hdq with h1 h2
        subst h2
        rw [hc2] at hdvd
        exact hℓ.not_dvd_one (by simpa using hdvd)
      · cases hdq
    have hLie : IsLieOver ↥Y (.A r) 2 1 := isLieOver_of_card_center_eq_one hqp hqe rfl e hZ
    obtain ⟨D, hD, hD3⟩ := kFactLnTwoCentralizerAbs_holds A Y β r hLie hβY hβ3' hnc'
    exact Or.inl ⟨D, hD, hD3⟩
  ·
    rename_i r q
    have hqp : q.p = 2 := hd
    simp only [LieField] at hq4
    rcases card_eq_two_or_four_le hqp with ⟨hc2, hqe⟩ | h4
    swap
    · omega
    have hr2 : 2 ≤ r ∧ (r = 2 → 3 ≤ q.card) := hrange
    have hr3 : 3 ≤ r := by
      by_contra hlt
      have := hr2.2 (by omega)
      omega
    have hLieU : IsLieOver (↥Y ⧸ center ↥Y) (.twistedA r) 2 1 :=
      ⟨⟨.twistedA r q, hv⟩, ⟨q, hqp, hqe, rfl⟩, ⟨e⟩⟩
    by_cases hr : r = 3
    · subst hr
      exact Or.inr ⟨Or.inl hLieU, h3 A Y P hY hO (Or.inl hLieU) hP hPY hSyl hnoJ⟩
    · have h4 := four_le_pRank_of_isLieOver_twistedA hY hO (by omega : 4 ≤ r) hLieU
      omega
  ·
    rename_i r q
    have hqp : q.p = 2 := hd
    simp only [LieField] at hq4
    rcases card_eq_two_or_four_le hqp with ⟨hc2, hqe⟩ | h4
    swap
    · omega
    exact absurd ⟨⟨.B r q, hv⟩, hc2, ⟨e⟩⟩ hB2
  ·
    rename_i r q
    have hqp : q.p = 2 := hd
    simp only [LieField] at hq4
    rcases card_eq_two_or_four_le hqp with ⟨hc2, hqe⟩ | h4
    swap
    · omega
    have hZ : Nat.card (center ↥Y) = 1 :=
      AGLEmbedding.ToralCensus.card_center_eq_one_of_index hGA ⟨.D r q, hv⟩ hd
        (fun r' q' h => by cases h) (fun r' q' h => by cases h) e hodd
    have hLie : IsLieOver ↥Y (.D r) 2 1 := isLieOver_of_card_center_eq_one hqp hqe rfl e hZ
    have h4 := TwelveRanksNotLe.four_le_pRank_three_of_isLieOver_D hLie
    rw [← CFSG.LocalAnalysis.GLTheoremB.pRank_eq_pRank_top_subtype (by norm_num) Y] at h4
    omega
  ·
    rename_i r q
    have hqp : q.p = 2 := hd
    simp only [LieField] at hq4
    rcases card_eq_two_or_four_le hqp with ⟨hc2, hqe⟩ | h4
    swap
    · omega
    have hZ : Nat.card (center ↥Y) = 1 :=
      AGLEmbedding.ToralCensus.card_center_eq_one_of_index hGA ⟨.twistedD r q, hv⟩ hd
        (fun r' q' h => by cases h) (fun r' q' h => by cases h) e hodd
    have hLie : IsLieOver ↥Y (.twistedD r) 2 1 :=
      isLieOver_of_card_center_eq_one hqp hqe rfl e hZ
    have hr4 : 4 ≤ r := hrange
    by_cases hr : r = 4
    · subst hr
      exact Or.inr ⟨Or.inr hLie, h3 A Y P hY hO (Or.inr hLie) hP hPY hSyl hnoJ⟩
    · have h4 := TwelveRanksLe.four_le_pRank_of_isLieOver_twistedD hLie (by omega)
      rw [← CFSG.LocalAnalysis.GLTheoremB.pRank_eq_pRank_top_subtype (by norm_num) Y] at h4
      omega
  ·
    rename_i q
    have hqp : q.p = 2 := hd
    simp only [LieField] at hq4
    have h3q : 3 ≤ q.card := hrange
    rcases card_eq_two_or_four_le hqp with ⟨hc2, hqe⟩ | h4
    · omega
    · omega

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe
