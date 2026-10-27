module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverEdge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Orient

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem spThreeStandard_or_twisted (e : L ≃* StatedSp 3 K) :
    SpThreeStandard e ∨ SpThreeTwisted e := by
  by_cases h : (Nat.card K) ^ 2 ∣ Nat.card (edgeCoreSp e 0 1)
  · exact Or.inr fun k l hkl => by rw [natCard_edgeCoreSp_eq_zero_one e hkl]; exact h
  · exact Or.inl fun k l hkl => by rw [natCard_edgeCoreSp_eq_zero_one e hkl]; exact h

theorem ne_succAbove_zero_three (k : Fin 3) : k ≠ k.succAbove 0 := (Fin.succAbove_ne k 0).symm

variable [Finite K] [CharP K 2]

theorem spThreeUnitaryNormalized_of_standard
    {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .unitaryEven) (hstd : SpThreeStandard e) :
    SpThreeUnitaryNormalized e t f k false := by
  rcases spThreeUnitaryNormalized_false_or_true hset hKc hf e htC ht k hk with h | h
  · exact h
  · exact absurd (sq_dvd_natCard_edgeCoreSp_of_unitary_twisted hKc hf h)
      (hstd k _ (ne_succAbove_zero_three k))

theorem spThreeUnitaryNormalized_of_twisted
    {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .unitaryEven) (htw : SpThreeTwisted e) :
    SpThreeUnitaryNormalized e t f k true := by
  rcases spThreeUnitaryNormalized_false_or_true hset hKc hf e htC ht k hk with h | h
  · exact absurd (htw k _ (ne_succAbove_zero_three k))
      (not_sq_dvd_natCard_edgeCoreSp_of_unitary_std hKc hf h)
  · exact h

end Orient

@[expose] def SpThreeUnitaryEvenStandardInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .unitaryEven) → SpThreeStandard e →
        SpGlobalCoverType e f .unitaryEven

@[expose] def SpThreeUnitaryEvenTwistedInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .unitaryEven) → SpThreeTwisted e →
        Sp2mKindType (spGlobal e) 3 f .omegaMinus

theorem spThreeUnitaryEvenRecognitionInput_of_oriented (hs : SpThreeUnitaryEvenStandardInput)
    (ht : SpThreeUnitaryEvenTwistedInput) : SpThreeUnitaryEvenRecognitionInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot
  rcases spThreeStandard_or_twisted e with h | h
  · exact Or.inl (hs G L hset f K hKc hf e t hto hKt hroot h)
  · exact Or.inr (ht G L hset f K hKc hf e t hto hKt hroot h)

end CFSG.SeitzReduction.SymplecticPilot
