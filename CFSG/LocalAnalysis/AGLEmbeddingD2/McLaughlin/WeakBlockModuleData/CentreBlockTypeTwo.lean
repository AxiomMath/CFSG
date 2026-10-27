module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentreTypeTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentreOneImage

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFactCentreBlockPLRankPSU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), IsWeakSBlock M S L →
    NineThreeTwo M S L → BlockPLThreeSolv M S L →
    (NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) →
    barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
    3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    (∃ d : TauCeti.ValidLieTypeIndex,
      (∃ r : ℕ, ∃ q : TauCeti.PrimePower, d.1 = .twistedA r q ∧ q.card = 2 ∧ 3 ∣ r + 1) ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    3 ≤ Open.pRank 3 (barM M (Subgroup.normalizer (S : Set G) ⊓ L))


theorem kFactCentreBlockPLRank_of_psu (hG : GriessAllModelsStatement)
    (hP : KFactCentreBlockPLRankPSU) : KFactCentreBlockPLRank := by
  intro G _ _ M S L hL hconc hnot hSyl hsolv hZP hZ hnA6
  have h3p : Nat.Prime 3 := Nat.prime_three
  have hq : CFSG.Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
  have hperfX : commutator ↥(barM M L) = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr (barM_perfect hL.le hL.perfect))
  have hnt : Nontrivial ↥(barM M L) := by
    haveI := hq.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L))).nontrivial
  have hcard := card_inf_centralizer_eq_card_center (barM M L)
  have hcentreless : Subgroup.center ↥(barM M L) = ⊥ → False := fun h => by
    apply (absurd hZ)
    rw [hcard, h, Subgroup.card_bot]
    norm_num
  rcases hconc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hnot
  · obtain ⟨hY, hpar, hS⟩ := h2
    have h2' : NineThreeTwo M S L := ⟨hY, hpar, hS⟩
    have hnot' : ¬ IsSylowTwoOf (pCoreOf 2 (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
        (barM M L) := hS ▸ hSyl h2'
    obtain ⟨T, hT, hNJ, hJne, hJperf⟩ := exists_overgroup_quotient_map _ _ hpar hnot' hsolv
    have hcensus := kFactParabolicThreeCensus _ hY T _ hT hNJ hJne hJperf
    have h3c : 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by rw [← hcard]; exact hZ
    rcases rows_of_three_dvd_center hG ⟨hperfX⟩ h3c hcensus with heA | hpsu
    · exact absurd heA hnA6
    · exact hP G M S L hL h2' hsolv hSyl hZP hZ hpsu
  · exfalso
    obtain ⟨-, horth, -⟩ := h3
    haveI : Group.IsPerfect ↥(barM M L) := ⟨hperfX⟩
    have hnab : ∃ a b : ↥(barM M L), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact Group.IsPerfect.not_isMulCommutative (G := ↥(barM M L)) ⟨⟨fun a b => hcon a b⟩⟩
    exact hcentreless (center_eq_bot_of_isOrthogonalTwo ‹_› hnab horth)
  · exfalso
    obtain ⟨-, -, ⟨eY⟩, -⟩ := h4
    exact hnA6 ⟨eY⟩
  · exfalso
    obtain ⟨-, ⟨e⟩, -⟩ := h5
    exact hcentreless (center_eq_bot_of_alt (by norm_num) e)
  · exfalso
    obtain ⟨-, n, -, ⟨eQ⟩⟩ := h6
    have hPL : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M L := barM_mono inf_le_right
    obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) 3 hZ
    have hz3 : (z' : ↥M ⧸ CFSG.pCore 2 ↥M) ^ 3 = 1 := by
      have := pow_orderOf_eq_one z'
      rw [hz'] at this
      exact congrArg Subtype.val this
    have hz1 : (z' : ↥M ⧸ CFSG.pCore 2 ↥M) ≠ 1 := by
      intro h
      have : z' = 1 := Subtype.ext h
      rw [this, orderOf_one] at hz'
      omega
    exact false_of_central_three_perm _ (z' : ↥M ⧸ CFSG.pCore 2 ↥M) hz3 hz1 (hZP z'.2)
      (fun p hp => (Subgroup.mem_centralizer_iff.mp z'.2.2 p (hPL hp))) eQ
  · exfalso
    obtain ⟨-, n, ⟨e⟩, -⟩ := h7
    exact hcentreless (center_eq_bot_of_alt
      (by have := five_le_of_perfect_alt hperfX e; omega) e)
  · exfalso
    obtain ⟨-, N, r, -, -, -, -, -, ⟨e⟩, -⟩ := h8
    exact hcentreless (center_eq_bot_of_alt
      (by have := five_le_of_perfect_alt hperfX e; omega) e)

end CFSG.AGLEmbeddingD2.McLaughlin
