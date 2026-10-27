module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomTransport
import CFSG.GH74.BNPair.Lemma3013
import CFSG.LieType.BorelTits.CentralQuotient
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup

section Simple

variable {L : Type} [Group L]

theorem IsGomiChevTwo.isSimpleGroup (h : IsGomiChevTwo L) : IsSimpleGroup (L ⧸ center L) :=
  h.1.2.1

theorem IsGomiChevTwo.exists_mul_ne_mul (h : IsGomiChevTwo L) :
    ∃ a b : L ⧸ center L, a * b ≠ b * a :=
  h.1.2.2

theorem IsGomiChevTwo.isChevTwo (h : IsGomiChevTwo L) : IsChevTwo (L ⧸ center L) :=
  h.2.2

theorem IsGomiChevTwo.coprime_card_center [Finite L] (h : IsGomiChevTwo L) :
    Nat.Coprime (Nat.card (center L)) 2 :=
  ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
    (CFSG.GH74.BNPair.not_dvd_card_center (p := 2) h.2.1)).symm

end Simple

section Quotient

variable {X : Type} [Group X] (Z : Subgroup X) [Z.Normal] {r : ℕ}

theorem comap_map_mk'_eq_of_normalizer_le (hZ : Z ≤ center X) {U P : Subgroup X}
    (hP : normalizer (U : Set X) ≤ P) :
    (P.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) = P := by
  refine Subgroup.comap_map_eq_self ?_
  rw [QuotientGroup.ker_mk']
  exact hZ.trans ((Subgroup.center_le_normalizer (U : Set X)).trans hP)

theorem map_mk'_eq_top_iff_of_normalizer_le (hZ : Z ≤ center X) {U P : Subgroup X}
    (hP : normalizer (U : Set X) ≤ P) : P.map (QuotientGroup.mk' Z) = ⊤ ↔ P = ⊤ := by
  constructor
  · intro h
    calc P = (P.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) :=
          (comap_map_mk'_eq_of_normalizer_le Z hZ hP).symm
      _ = ⊤ := by rw [h, Subgroup.comap_top]
  · intro h
    rw [h]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)

theorem map_mk'_normalizer_eq (hZ : Z ≤ center X) (hZr : Nat.Coprime (Nat.card Z) r)
    {U : Subgroup X} (hU : IsPGroup r U) :
    (normalizer (U : Set X)).map (QuotientGroup.mk' Z) =
      normalizer (U.map (QuotientGroup.mk' Z) : Set (X ⧸ Z)) := by
  rw [CFSG.LieType.BorelTits.normalizer_eq_comap_normalizer_map Z hZ hZr hU]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) _

private theorem covBy_comap_iff {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) {C D : Subgroup H} :
    C.comap f ⋖ D.comap f ↔ C ⋖ D := by
  constructor
  · intro h
    have hle : C ≤ D := (Subgroup.comap_le_comap_of_surjective hf).1 h.le
    refine (covBy_iff_lt_and_eq_or_eq).2
      ⟨lt_of_le_of_ne hle fun hEq => h.lt.ne (by rw [hEq]), fun E hCE hED => ?_⟩
    rcases h.eq_or_eq ((Subgroup.comap_le_comap_of_surjective hf).2 hCE)
      ((Subgroup.comap_le_comap_of_surjective hf).2 hED) with hE | hE
    · exact Or.inl (Subgroup.comap_injective hf hE)
    · exact Or.inr (Subgroup.comap_injective hf hE)
  · intro h
    have hle : C.comap f ≤ D.comap f := (Subgroup.comap_le_comap_of_surjective hf).2 h.le
    have hker : f.ker ≤ C.comap f := Subgroup.ker_le_comap f C
    refine (covBy_iff_lt_and_eq_or_eq).2
      ⟨lt_of_le_of_ne hle fun hEq => h.lt.ne (Subgroup.comap_injective hf hEq),
        fun E hCE hED => ?_⟩
    have h1 : C ≤ E.map f := by
      rw [← Subgroup.map_comap_eq_self_of_surjective hf C]
      exact Subgroup.map_mono hCE
    have h2 : E.map f ≤ D := by
      rw [← Subgroup.map_comap_eq_self_of_surjective hf D]
      exact Subgroup.map_mono hED
    rcases h.eq_or_eq h1 h2 with hE | hE
    · left
      rw [← Subgroup.comap_map_eq_self (hker.trans hCE), hE]
    · right
      rw [← Subgroup.comap_map_eq_self (hker.trans hCE), hE]

theorem isGomiAtom_top_comap_mk'_iff (hZ : Z ≤ center X) (hZr : Nat.Coprime (Nat.card Z) r)
    {U : Subgroup X} (hU : IsPGroup r U) (A : Subgroup (X ⧸ Z)) :
    IsGomiAtom ⊤ U (A.comap (QuotientGroup.mk' Z)) ↔
      IsGomiAtom ⊤ (U.map (QuotientGroup.mk' Z)) A := by
  rw [isGomiAtom_top_iff_covBy, isGomiAtom_top_iff_covBy,
    CFSG.LieType.BorelTits.normalizer_eq_comap_normalizer_map Z hZ hZr hU]
  exact covBy_comap_iff (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)

theorem isGomiAtom_top_map_mk'_iff (hZ : Z ≤ center X) (hZr : Nat.Coprime (Nat.card Z) r)
    {U A : Subgroup X} (hU : IsPGroup r U) (hZA : Z ≤ A) :
    IsGomiAtom ⊤ (U.map (QuotientGroup.mk' Z)) (A.map (QuotientGroup.mk' Z)) ↔
      IsGomiAtom ⊤ U A := by
  have hker : (QuotientGroup.mk' Z).ker ≤ A := by
    rwa [QuotientGroup.ker_mk']
  conv_rhs => rw [← Subgroup.comap_map_eq_self hker]
  exact (isGomiAtom_top_comap_mk'_iff Z hZ hZr hU (A.map (QuotientGroup.mk' Z))).symm

theorem IsGomiAtom.map_mk' (hZ : Z ≤ center X) (hZr : Nat.Coprime (Nat.card Z) r)
    {U A : Subgroup X} (hU : IsPGroup r U) (h : IsGomiAtom ⊤ U A) :
    IsGomiAtom ⊤ (U.map (QuotientGroup.mk' Z)) (A.map (QuotientGroup.mk' Z)) :=
  (isGomiAtom_top_map_mk'_iff Z hZ hZr hU (hZ.trans h.center_le)).2 h

end Quotient

theorem isSylowOf_top_map_of_surjective {X Y : Type} [Group X] [Group Y] [Finite X] {p : ℕ}
    [Fact p.Prime] {f : X →* Y} (hf : Function.Surjective f) {U : Subgroup X}
    (hU : IsSylowOf p U ⊤) : IsSylowOf p (U.map f) ⊤ := by
  rw [← Subgroup.map_top_of_surjective f hf]
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c7_isSylowOf_map hU f

end CFSG.GroupTheory
