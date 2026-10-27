module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLinear
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphParamExists

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Recognition


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

theorem sp2mKindType_nsGlobal_of_linear (hset : SeitzSetting G L) {n : ℕ} (hK : Nat.card K = 2)
    (hn : 4 ≤ n) (e : L ≃* StatedSp (n + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .linearEven ∨ κ = .linearOdd) (hroot : ∀ k : Fin (n + 1), NsKindSp e t k κ) :
    Sp2mKindType (nsGlobal e) (n + 1) 1 κ := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  rcases hκ with rfl | rfl
  · have P : ∀ k : Fin (n + 1), NsLinParam hK 0 e k := fun k =>
      (nonempty_nsLinParam hset hK (by omega) (by omega) e htC ht k (Or.inl ⟨rfl, rfl⟩)
        (hroot k)).some
    obtain ⟨Q, hQ⟩ := exists_nsLinParamAgree (by omega) (by omega) P
    obtain ⟨-, -, -, hty⟩ := exists_injective_nsLinRow_of_agree (by omega) (by omega) Q hQ
    exact hty
  · have P : ∀ k : Fin (n + 1), NsLinParam hK 1 e k := fun k =>
      (nonempty_nsLinParam hset hK le_rfl (by omega) e htC ht k (Or.inr ⟨rfl, rfl⟩)
        (hroot k)).some
    obtain ⟨Q, hQ⟩ := exists_nsLinParamAgree le_rfl (by omega) P
    obtain ⟨-, -, -, hty⟩ := exists_injective_nsLinRow_of_agree le_rfl (by omega) Q hQ
    exact hty

end Recognition

theorem spTwoGraphKindInput_linearEven :
    SpTwoGraphKindInput .linearEven :=
  fun _ _ _ _ hset _ _ _ _ _ hK hn e _ ht hKt hroot =>
    sp2mKindType_nsGlobal_of_linear hset hK hn e ht hKt (Or.inl rfl) hroot

theorem spTwoGraphKindInput_linearOdd :
    SpTwoGraphKindInput .linearOdd :=
  fun _ _ _ _ hset _ _ _ _ _ hK hn e _ ht hKt hroot =>
    sp2mKindType_nsGlobal_of_linear hset hK hn e ht hKt (Or.inr rfl) hroot

section Rows


theorem spTwoRowInput_linearOdd_of_five_le :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
      ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (n + 1), NsKindSp e t k .linearOdd) → False :=
  spTwoRowInput_linearOdd_of_four_le spTwoGraphKindInput_linearOdd

theorem spTwoRowInput_linearEven_of_five_le (h2 : SpTwoLinearEvenSecondClassInput) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
      ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (n + 1), NsKindSp e t k .linearEven) → False :=
  spTwoRowInput_linearEven_of_four_le spTwoGraphKindInput_linearEven h2

end Rows

end CFSG.SeitzReduction.SymplecticPilot
