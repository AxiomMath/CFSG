module

import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22Basic

public section

namespace CFSG.ComponentClassification.AS76b

namespace Lemma37

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22

variable {G : Type*} [Group G]

section Transfer

theorem centralizer_subgroupOf {L X : Subgroup G} (hLX : L ≤ X) :
    centralizer ((L.subgroupOf X : Subgroup X) : Set X) =
      (centralizer (L : Set G)).subgroupOf X := by
  ext c
  rw [mem_subgroupOf, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h l hl
    have hl' : (⟨l, hLX hl⟩ : X) ∈ (L.subgroupOf X : Set X) := hl
    simpa using congrArg Subtype.val (h _ hl')
  · intro h l hl
    apply Subtype.ext
    simpa using h l hl

theorem conj_subgroupOf (L : Subgroup G) {X : Subgroup G} (g : X) :
    conj (L.subgroupOf X) g = (conj L (g : G)).subgroupOf X := by
  ext x
  rw [mem_conj_iff, mem_subgroupOf, mem_subgroupOf, mem_conj_iff]
  simp

theorem tightlyEmbedded_subgroupOf [Finite G] {Q X : Subgroup G} (hQX : Q ≤ X)
    (hQ : TightlyEmbedded Q) : TightlyEmbedded (Q.subgroupOf X) :=
  StandardSubgroupAPI.tightlyEmbedded_subgroupOf hQX hQ

theorem isSylowOf_subgroupOf_iff [Finite G] {p : ℕ} [Fact p.Prime] {P Q X : Subgroup G}
    (hPX : P ≤ X) (hQX : Q ≤ X) :
    IsSylowOf p (P.subgroupOf X) (Q.subgroupOf X) ↔ IsSylowOf p P Q := by
  rw [← isSylowOf_map_subtype_iff X, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_eq_left.mpr hPX, inf_eq_left.mpr hQX]

theorem isQuasisimple_subgroupOf_iff {L X : Subgroup G} (hLX : L ≤ X) :
    CFSG.Open.IsQuasisimple ↥(L.subgroupOf X) ↔ CFSG.Open.IsQuasisimple ↥L :=
  ⟨isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hLX),
    isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hLX).symm⟩

theorem isSolvable_subgroupOf {K X : Subgroup G} (hKX : K ≤ X) (h : Group.IsSolvable ↥K) :
    Group.IsSolvable ↥(K.subgroupOf X) :=
  Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hKX).toMonoidHom)
    (subgroupOfEquivOfLe hKX).injective

end Transfer

section Sylow

variable [Finite G]

omit [Finite G] in
theorem normalizer_le_of_le_of_even {K Q : Subgroup G} (hK : TightlyEmbedded K) (hQK : Q ≤ K)
    (hQ : Even (Nat.card Q)) : normalizer (Q : Set G) ≤ normalizer (K : Set G) :=
  StandardSubgroupAPI.normalizer_le_normalizer_of_le_of_even hK hQK hQ

theorem isSylowOf_of_isSylowOf_inf_normalizer {R X : Subgroup G}
    (h : IsSylowOf 2 R (X ⊓ normalizer (R : Set G))) : IsSylowOf 2 R X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX : R ≤ X := h.le.trans inf_le_left
  obtain ⟨P, hRP⟩ := (h.isPGroup.comap_subtype (K := X)).exists_le_sylow
  set P' : Subgroup G := (P : Subgroup X).map X.subtype with hP'def
  have hP' : IsSylowOf 2 P' X := ⟨P, rfl⟩
  have hRP' : R ≤ P' := fun r hr => ⟨⟨r, hRX hr⟩, hRP hr, rfl⟩
  have hP'X : P' ≤ X := hP'.le
  suffices hRe : R = P' by rw [hRe]; exact hP'
  by_contra hne
  have hlt : R.subgroupOf P' < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm hRP' fun x hx => ?_)
    have : (⟨x, hx⟩ : P') ∈ R.subgroupOf P' := htop ▸ mem_top _
    exact this
  have hp : IsPGroup 2 ↥P' := hP'.isPGroup
  have : Group.IsNilpotent ↥P' := hp.isNilpotent
  have hlt' := Group.normalizerCondition_of_isNilpotent (R.subgroupOf P') hlt
  set N : Subgroup G := (normalizer (R.subgroupOf P' : Set P')).map P'.subtype with hNdef
  have hRN : R ≤ N := fun r hr => ⟨⟨r, hRP' hr⟩, le_normalizer (show (⟨r, hRP' hr⟩ : P') ∈
    R.subgroupOf P' from hr), rfl⟩
  have hNle : N ≤ X ⊓ normalizer (R : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨hP'X y.2, ?_⟩
    rw [← subgroupOf_normalizer_eq hRP'] at hy
    exact hy
  have hNp : IsPGroup 2 N := hP'.isPGroup.to_le (map_subtype_le _)
  have hNR : N = R := h.eq_of_le hRN hNle hNp
  apply hlt'.ne
  apply le_antisymm le_normalizer
  intro y hy
  have hyN : (y : G) ∈ N := ⟨y, hy, rfl⟩
  rw [hNR] at hyN
  exact hyN

theorem isSolvable_oddCoreIn_sup {G : Type} [Group G] [Finite G] {K R : Subgroup G}
    (hR : IsSylowOf 2 R K) : Group.IsSolvable ↥(oddCoreIn K ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := oddCoreIn K with hOdef
  set X := O ⊔ R with hX
  have hXK : X ≤ K := sup_le (oddCoreIn_le K) hR.le
  have hOX : O ≤ X := le_sup_left
  have hOn : (O.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOX).mpr
      (hXK.trans ((le_normalizer).trans (normalizer_le_normalizer_oddCoreIn K)))
  have hOsolv : Group.IsSolvable (O.subgroupOf X) := by
    refine CFSG.FeitThompson.isSolvable_of_odd_natCard _ ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe hOX).toEquiv]
    exact odd_card_oddCoreIn K
  have hXOsolv : Group.IsSolvable (↥X ⧸ O.subgroupOf X) := by
    have hidx : O.relIndex X = O.relIndex R :=
      AschbacherTheorem3.relIndex_sup_of_le_normalizer
        (hR.le.trans ((le_normalizer).trans (normalizer_le_normalizer_oddCoreIn K)))
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR.isPGroup
    have hdvd : Nat.card (↥X ⧸ O.subgroupOf X) ∣ 2 ^ m := by
      change O.relIndex X ∣ 2 ^ m
      rw [hidx, ← hm]
      exact relIndex_dvd_card O R
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have := (IsPGroup.of_card hj).isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (O.subgroupOf X).subtype
    (QuotientGroup.mk' (O.subgroupOf X)) (by rw [QuotientGroup.ker_mk', range_subtype])

end Sylow

end Lemma37

end CFSG.ComponentClassification.AS76b
