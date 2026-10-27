module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTAgree
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTParamEven

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Five

theorem spGlobalCoverType_linearEven_of_five_le {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hn : 5 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin n, RootKindSp e t f k .linearEven) : SpGlobalCoverType e f .linearEven := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hP : ∀ k : Fin (m + 1), Nonempty (CtLinParam 0 e k) := fun k =>
    nonempty_ctLinParam_linearEven hset hKc hf (by omega) e htC ht k (hroot k)
  obtain ⟨Q, hQ⟩ := exists_ctLinParamAgree hq hn fun k => (hP k).some
  exact spGlobalCoverType_of_ctLinParamAgree hKc hf hn (Or.inl ⟨rfl, rfl⟩) Q hQ

end Five

@[expose] def SpLinearEvenCoverFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, RootKindSp e t f k .linearEven) → SpGlobalCoverType e f .linearEven

theorem spKindCoverInput_linearEven_of_four
    (h4 : SpLinearEvenCoverFourInput) : SpKindCoverInput .linearEven := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · exact h4 G L hset f K hKc hf e t ht hKt hroot
  · exact spGlobalCoverType_linearEven_of_five_le hset h5 hKc hf e ht hKt hroot

@[expose] def SpLinearOddAlignedParamInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 5 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k .linearOdd) →
        ∃ P : ∀ k : Fin n, CtLinParam 1 e k, CtLinParamAgree P

@[expose] def SpLinearOddCoverFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 4, RootKindSp e t f k .linearOdd) → SpGlobalCoverType e f .linearOdd

theorem spKindCoverInput_linearOdd_of_alignedParam (hP : SpLinearOddAlignedParamInput)
    (h4 : SpLinearOddCoverFourInput) : SpKindCoverInput .linearOdd := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · exact h4 G L hset f K hKc hf e t ht hKt hroot
  · obtain ⟨P, hPa⟩ := hP G L hset n f K h5 hKc hf e t ht hKt hroot
    exact spGlobalCoverType_of_ctLinParamAgree hKc hf h5 (Or.inr ⟨rfl, rfl⟩) P hPa

end CFSG.SeitzReduction.SymplecticPilot
