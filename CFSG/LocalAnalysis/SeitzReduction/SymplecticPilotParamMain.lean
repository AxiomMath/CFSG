module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamField
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamSwap
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRowsUnique

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs

section Quadratic

theorem exists_quadraticExtension (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ι : K →+* F) (σ : F ≃+* F),
      orderOf σ = 2 ∧ ∀ x : F, σ x = x ↔ x ∈ Set.range ι := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfix : ∀ x : FiniteField.Extension K 2 2,
      FiniteField.Extension.frob K 2 2 x = x ↔
        x ∈ Set.range (algebraMap K (FiniteField.Extension K 2 2)) := by
    intro x
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    constructor
    · intro hx g
      obtain ⟨i, -, rfl⟩ := FiniteField.Extension.exists_frob_pow_eq K 2 2 g
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
    · intro h
      exact h _
  have hcardF : Nat.card (FiniteField.Extension K 2 2) = Nat.card K ^ 2 :=
    FiniteField.natCard_extension K 2 2
  refine ⟨FiniteField.Extension K 2 2, inferInstance, inferInstance,
    algebraMap K (FiniteField.Extension K 2 2), (FiniteField.Extension.frob K 2 2).toRingEquiv,
    ?_, fun x => hfix x⟩
  apply orderOf_eq_prime
  · ext x
    rw [sq]
    change FiniteField.Extension.frob K 2 2 (FiniteField.Extension.frob K 2 2 x) = _
    rw [FiniteField.Extension.frob_apply, FiniteField.Extension.frob_apply, ← pow_mul, ← sq,
      ← hcardF]
    have := Fintype.ofFinite (FiniteField.Extension K 2 2)
    rw [Nat.card_eq_fintype_card, FiniteField.pow_card]
    rfl
  · intro h1
    have hsurj : Function.Surjective (algebraMap K (FiniteField.Extension K 2 2)) := fun x =>
      (hfix x).1 (by
        have := congrArg (fun σ : FiniteField.Extension K 2 2 ≃+* FiniteField.Extension K 2 2 =>
          σ x) h1
        simpa using this)
    have hle := Nat.card_le_card_of_surjective _ hsurj
    rw [hcardF] at hle
    have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
    nlinarith

end Quadratic

section AllPlanes


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem forall_nonempty_fieldNeighbourParam_of_rootKindSp {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {F : Type} [Field F] [Finite F]
    (ι : K →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {k₀ : Fin (m + 1)} (h : RootKindSp e t f k₀ .field) (k : Fin (m + 1)) :
    Nonempty (FieldNeighbourParam e t ι σ k) :=
  nonempty_fieldNeighbourParam_of_rootKindSp hset hKc hf hm e htC ht k ι hσ hfix
    ((rootKindSp_iff e htC f k₀ k .field).1 h)

theorem forall_nonempty_swapNeighbourParam_of_rootKindSp {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {k₀ : Fin (m + 1)}
    (h : RootKindSp e t f k₀ .swap) (k : Fin (m + 1)) : Nonempty (SwapNeighbourParam e t k) :=
  nonempty_swapNeighbourParam_of_rootKindSp hset hKc hf hm e htC ht k
    ((rootKindSp_iff e htC f k₀ k .swap).1 h)

theorem exists_rootKindSp_param {m f : ℕ} (hcat : Sp2mCatalogueClausesAt m)
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m)
    (e : L ≃* StatedSp (m + 1) K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) :
    ∃ κ : Sp2mKind, (∀ k : Fin (m + 1), RootKindSp e t f k κ) ∧
      (κ = .field → ∀ (F : Type) [Field F] [Finite F] (ι : K →+* F) (σ : F ≃+* F),
        orderOf σ = 2 → (∀ x : F, σ x = x ↔ x ∈ Set.range ι) →
          ∀ k, Nonempty (FieldNeighbourParam e t ι σ k)) ∧
      (κ = .swap → ∀ k, Nonempty (SwapNeighbourParam e t k)) := by
  obtain ⟨κ, hκ, -⟩ := existsUnique_rootKindSp (n := m + 1) hcat hset hKc hf (by omega) e htC ht
  refine ⟨κ, hκ, ?_, ?_⟩
  · rintro rfl F _ _ ι σ hσ hfix k
    exact nonempty_fieldNeighbourParam_of_rootKindSp hset hKc hf hm e htC ht k ι hσ hfix (hκ k)
  · rintro rfl k
    exact nonempty_swapNeighbourParam_of_rootKindSp hset hKc hf hm e htC ht k (hκ k)

end AllPlanes

end CFSG.SeitzReduction.SymplecticPilot
