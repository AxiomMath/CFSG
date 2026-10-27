module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeCensus
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeKFacts
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeAlt
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeOut
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeLinModel
import CFSG.LocalAnalysis.AGLEmbedding.BlockOutNine
import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockTypes
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem threeAutFixedTwoThree_lie_of_census (hLie : KFactThreeCentLieTwo)
    (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2IndexTwo d.1 ∨ (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) :
    ThreeAutFixedTwoThree (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  rcases hd with hd | hd7 | ⟨q, hq, hd⟩
  · cases d with
    | A r q => exact threeAutFixedTwoThree_lie_A_two ⟨.A r q, hv⟩ ⟨r, q, hd, rfl⟩
    | twistedA r q => exact hLie ⟨.twistedA r q, hv⟩ (Or.inl hd)
    | B r q => exact hLie ⟨.B r q, hv⟩ hd
    | D r q => exact hLie ⟨.D r q, hv⟩ hd
    | twistedD r q => exact hLie ⟨.twistedD r q, hv⟩ hd
    | G2 q =>
      change q.card = 2 at hd
      have hq3 : 3 ≤ q.card :=
        (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      omega
    | _ => exact hd.elim
  · exact threeAutFixedTwoThree_lie_A_seven ⟨d, hv⟩ hd7
  · simp only at hd
    subst hd
    exact hLie _ (Or.inr ⟨rfl, hq⟩)


theorem threeAutFixedTwoThree_barM_of_nineThree (hLie : KFactThreeCentLieTwo) {G : Type}
    [Group G] [Finite G] {M S L : Subgroup G} (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (h93 : NineThreeConclusion M S L) (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (hperf : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y)) :
    ThreeAutFixedTwoThree ↥(barM M L) ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (Outer ↥(barM M L)) := by
  have hq := hL.component.2.2
  have : Group.IsPerfect ↥(barM M L) := Group.isPerfect_def.mpr hq.1
  have : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hq.2.toNontrivial
  have : Nontrivial ↥(barM M L) :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L))).nontrivial
  have hlie : ∀ (d : TauCeti.ValidLieTypeIndex),
      (IsClassicalOrG2IndexTwo d.1 ∨ (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) →
      ∀ {X : Type} [Group X], (X ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ThreeAutFixedTwoThree X ∧ ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (Outer X) :=
    fun d hd X _ e => ⟨(threeAutFixedTwoThree_lie_of_census hLie d hd).of_mulEquiv e,
      fun p hp hp5 => not_dvd_card_outer_lie_two d hd e hp hp5⟩
  have halt : ∀ {X : Type} [Group X] {n : ℕ}, (X ≃* alternatingGroup (Fin n)) → 5 ≤ n →
      ThreeAutFixedTwoThree X ∧ ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (Outer X) :=
    fun e hn => ⟨threeAutFixedTwoThree_of_mulEquiv_alternatingGroup e hn, fun p hp hp5 =>
      not_dvd_card_outer_of_mulEquiv_alternatingGroup e hn hp hp5⟩
  have hcen : (ThreeAutFixedTwoThree (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p →
        ¬ p ∣ Nat.card (Outer (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)))) →
      ThreeAutFixedTwoThree ↥(barM M L) ∧
        ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (Outer ↥(barM M L)) :=
    fun h => ⟨threeAutFixedTwoThree_of_centerQuotient h.1, fun p hp hp5 =>
      not_dvd_card_outer_of_centerQuotient (h.2 p hp hp5)⟩
  rcases h93 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · have hns : ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L) := fun hsyl =>
      hS (isSylowTwoOf_inf_of_barM hL.le hA.twoCore_le hA.twoRadical.isPGroup hsyl)
    obtain ⟨T₁, hT₁, hN, hne⟩ := exists_sylowTwo_parabolic_of_nineThreeTwo h2 hns
    have hJ : ∀ W : Subgroup ↥(barM M L),
        W ≤ (barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L) →
          ⁅W, W⁆ = W → Nat.Coprime 3 (Nat.card W) := fun W hW hWp => by
      have h1 := coprime_card_of_le_barM_of_perfect inf_le_left hperf
        (B := W.map (barM M L).subtype) (fun y hy => by
          obtain ⟨w, hw, rfl⟩ := hy
          exact barM_mono (show Subgroup.normalizer (S : Set G) ⊓ L ≤
            M ⊓ Subgroup.normalizer (S : Set G) from fun _ hz => ⟨hL.le hz.2, hz.1⟩)
            (Subgroup.mem_subgroupOf.mp (hW hw)))
        (by rw [← Subgroup.map_commutator, hWp])
      rwa [Subgroup.card_map_of_injective (barM M L).subtype_injective] at h1
    obtain ⟨T, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT₁
    obtain ⟨hT', hN1, hN2, hperf'⟩ := map_overgroup_of_central
      (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L)))
      (QuotientGroup.ker_mk' _).le T hN hne hJ
    rcases kFactParabolicThreeCensus _ h2.1 _ _ hT' hN1 hN2 hperf' with
      ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
    · exact hcen (hlie d (Or.inl hd) e)
    · exact hcen (halt e (by omega))
    · exact hcen (hlie d (Or.inr hd) e)
  · rcases h3.2.1 with ⟨d, ⟨m, q, hq2, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · have hd' : IsClassicalOrG2IndexTwo d.1 := by
        rcases hd with h | h | ⟨-, h⟩ <;> rw [h] <;> exact hq2
      exact hlie d (Or.inl hd') e
    · exact halt e (by omega)
  · obtain ⟨-, -, ⟨e⟩, -⟩ := h4
    exact hcen (halt e (by norm_num))
  · obtain ⟨-, ⟨e⟩, -⟩ := h5
    exact halt e (by norm_num)
  · obtain ⟨-, n, ⟨e⟩, -⟩ := h6
    exact hcen (halt e (five_le_of_isPerfect_mulEquiv_alternatingGroup e))
  · obtain ⟨-, n, ⟨e⟩, -⟩ := h7
    exact halt e (five_le_of_isPerfect_mulEquiv_alternatingGroup e)
  · obtain ⟨-, N, r, -, -, -, -, -, ⟨e⟩, -⟩ := h8
    exact halt e (five_le_of_isPerfect_mulEquiv_alternatingGroup e)

theorem kFactBlockThreeCentCoprime_of (hLie : KFactThreeCentLieTwo) :
    KFactBlockThreeCentCoprime := by
  intro G _ _ M S L _ hA hL h93 hX hS hperf u hu hu3 _ hfree t ht htu ht6
  obtain ⟨hP, hOut⟩ := threeAutFixedTwoThree_barM_of_nineThree hLie hA hL h93 hX hS hperf
  exact mem_centralizer_of_threeAutFixedTwoThree hOut hP hu hu3 hfree ht htu ht6

end CFSG.AGLEmbedding
