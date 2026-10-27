module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbLinTransport
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbLinVoid
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearFlag

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

theorem exists_model_A {X : Type} [Group X] (h : IsLieOf IdxA X) :
    ∃ n f : ℕ, 2 ≤ n ∧ 1 ≤ f ∧ (n = 2 → 3 ≤ f) ∧ (n = 3 → 2 ≤ f) ∧ (n = 4 → 2 ≤ f) ∧
      Nonempty (X ≃* projectiveSL n (GaloisField 2 f)) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  cases d with
  | A r q =>
    change q.p = 2 at hd
    have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hv'.1
    have hdup := hv'.2
    rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
    obtain ⟨p, k, hp, hk⟩ := q
    change p = 2 at hd
    subst hd
    have : Fact (Nat.Prime 2) := ⟨hp⟩
    have hcard : (TauCeti.PrimePower.card ⟨2, k, hp, hk⟩) = 2 ^ k := by
      rw [TauCeti.PrimePower.card_def]
    refine ⟨r + 1, k, by omega, hk, ?_, ?_, ?_,
      ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r ⟨2, k, hp, hk⟩ hv)).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL _ _)⟩⟩
    · intro hr2
      have hr1 : r = 1 := by omega
      subst hr1
      have h4 := hr.2 rfl
      rw [hcard] at h4
      by_contra hk3
      have hk2 : k = 2 := by
        have : 4 ≤ 2 ^ k := h4
        by_contra hne
        have : k ≤ 2 := by omega
        have : 2 ≤ k := by
          by_contra h2
          have : k = 1 := by omega
          subst this
          omega
        omega
      subst hk2
      exact hdup (Or.inl ⟨rfl, Or.inl (by simp)⟩)
    · intro hr3
      have hr2 : r = 2 := by omega
      subst hr2
      by_contra hk2
      have hk1 : k = 1 := by omega
      subst hk1
      exact hdup (Or.inr (Or.inl ⟨rfl, by simp⟩))
    · intro hr4
      have hr3 : r = 3 := by omega
      subst hr3
      by_contra hk2
      have hk1 : k = 1 := by omega
      subst hk1
      exact hdup (Or.inr (Or.inr ⟨rfl, by simp⟩))
  | _ => exact hd.elim

section Void

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}

theorem blockIb_false_of_four_le (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x) {n f : ℕ}
    (hn : 4 ≤ n) (hf : 1 ≤ f) (hf4 : n = 4 → 2 ≤ f)
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* projectiveSL n (GaloisField 2 f)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine blockIb_false_of_perfect_centralizer hP hD e ?_
  intro v hv3 hv1
  obtain ⟨t, rfl⟩ := proj_surjective n _ v
  have ht : t ^ 3 ∈ scalars n (GaloisField 2 f) := by
    rw [← proj_eq_one_iff, map_pow]; exact hv3
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  refine exists_perfect_centralizer_proj ?_ t ht
  by_cases hf2 : f = 1
  · right
    subst hf2
    refine ⟨by rw [hcard]; norm_num, ?_⟩
    by_contra h5
    have := hf4 (by omega)
    omega
  · left
    refine ⟨?_, hn⟩
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem blockIb_false_of_two (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x) {f : ℕ}
    (hT : IsClassicalTwoOrG2 (↥Lb ⧸ Subgroup.center ↥Lb))
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* projectiveSL 2 (GaloisField 2 f)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hNJ, hne, htop⟩ := exists_parab_X hP hD hT e
  obtain ⟨g, I, hI, hNB, hJ⟩ := LinearThreeKit.exists_eq_map_conj_flagStabilizer 2
    (K := GaloisField 2 f) (n := 2) (by norm_num) S _ hNJ
  by_cases h1 : 1 ∈ I
  · apply hne
    have hall : ∀ i, 1 ≤ i → i < 2 → i ∈ I := fun i hi hi2 => by
      have : i = 1 := by omega
      rw [this]; exact h1
    rw [hJ, hNB, ToralCensus.flagStabilizer_eq_upperTriangular hI hall]
    rfl
  · apply htop
    have hI0 : I = ∅ := Set.eq_empty_of_forall_notMem fun i hi => by
      obtain ⟨h1', h2'⟩ := hI i hi
      have : i = 1 := by omega
      exact h1 (this ▸ hi)
    rw [hJ, hI0, flagStabilizer_empty, Subgroup.map_top_of_surjective _ (proj_surjective 2 _),
      Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

end Void

end CFSG.HardMathSupport.Curtis.UnitaryLevi
