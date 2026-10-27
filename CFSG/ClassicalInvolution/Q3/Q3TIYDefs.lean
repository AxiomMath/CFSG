module

public import CFSG.ClassicalInvolution.Q3.Q3WARow
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinStmt

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinRow IsTwinAt TwinElt TwinDatumOn twinYModel)

@[expose] def TwinRowLarge3 (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .POmegaPlus ∧ 5 ≤ n) ∨ (t = .POmegaMinus ∧ 5 ≤ n) ∨ (t = .POmegaOdd ∧ 4 ≤ n)

theorem TwinRowLarge3.twinRow {t : StatedLieTag} {n : ℕ} (h : TwinRowLarge3 t n) :
    TwinRow t n := by
  rcases h with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
  · exact Or.inl ⟨rfl, rfl, by omega⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by omega⟩))))
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by omega⟩))


@[expose] def TwinYNoCentral3On (P : StatedLieTag → ℕ → Prop) : Prop :=
  OddThreeFreeInput → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ (t : StatedLieTag) (n : ℕ),
      TwinRow t n → P t n → LocalShapeC3 2 (CompData.model t n) (conjClass3 K) z →
        ∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → IsClassicalMember3 T z →
          ∀ e : TwinElt K T z, ∀ M ∈ centralizingMembers (conjClass3 K) {e.u},
            ∃ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K ∧ N ≠ T ∧ ¬ Commutes M N

@[expose] def TwinYRank3On (P : StatedLieTag → ℕ → Prop) : Prop :=
  OddThreeFreeInput → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ (t : StatedLieTag) (n : ℕ),
      TwinRow t n → P t n → LocalShapeC3 2 (CompData.model t n) (conjClass3 K) z →
        ∀ T : Subgroup G, IsTwinAt (conjClass3 K) K T z → IsClassicalMember3 T z →
          ∀ e : TwinElt K T z, LocalOddCentral (conjClass3 K) {e.u} →
            LocalOddThreeFree3 (conjClass3 K) e.u →
              ∀ (ι : Type) [Finite ι]
                (D : LieSystemData3 ι (locQuot (conjClass3 K) e.u) (locFamily (conjClass3 K) e.u)),
                Nat.card ι = 1 → ∀ (i : ι) (t' : StatedLieTag) (n' : ℕ),
                  D.kind i = CompData.model t' n' → TwinRow t' n' →
                    t' = (twinYModel 3 t n).1 ∧ n' = (twinYModel 3 t n).2

@[expose] def TwinRank3Model (tY : StatedLieTag) (nY : ℕ) : Prop :=
  ∀ (R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K)
    (x x' ã ã' : (modelUniv tY nY 3 1 Nat.prime_three).K),
    TwinDatumOn tY (modelUniv tY nY 3 1 Nat.prime_three) R R' x x' → ã ∈ R → ã' ∈ R' →
    ã * ã * x⁻¹ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K →
    ã' * ã' * x'⁻¹ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K →
    ∀ (t' : StatedLieTag) (n' : ℕ), TwinRow t' n' → StatedLieAdmissible t' n' 3 1 →
      ¬ ((t' = .PSp ∧ n' = 2) ∨ (t' = .PSL ∧ n' = 4) ∨ (t' = .PSU ∧ n' = 4)) →
      ∀ R₀ ∈ fundamentalSubgroups t' (modelUniv t' n' 3 1 Nat.prime_three).D,
        Nat.card {S : Subgroup (modelUniv t' n' 3 1 Nat.prime_three).K //
            S ∈ fundamentalSubgroups t' (modelUniv t' n' 3 1 Nat.prime_three).D ∧
              Commutes S R₀} =
          1 + Nat.card {S : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K //
            S ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D ∧
              S ≤ Subgroup.centralizer
                ({ã * ã'} : Set (modelUniv tY nY 3 1 Nat.prime_three).K)} →
        t' = (twinYModel 3 tY nY).1 ∧ n' = (twinYModel 3 tY nY).2

@[expose] def SmallNoThree3 : Prop :=
  ∀ (t : StatedLieTag) (k : ℕ), StatedLieAdmissible t k 3 1 →
    ((t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨ (t = .POmegaOdd ∧ k = 3) ∨
      (t = .POmegaMinus ∧ k = 4)) →
    ∀ A ∈ fundamentalSubgroups t (modelUniv t k 3 1 Nat.prime_three).D,
      ∀ B ∈ fundamentalSubgroups t (modelUniv t k 3 1 Nat.prime_three).D,
      ∀ S ∈ fundamentalSubgroups t (modelUniv t k 3 1 Nat.prime_three).D,
        A ≠ B → A ≠ S → B ≠ S → Commutes A B → Commutes A S → Commutes B S → False

end CFSG.ClassicalInvolution.Q3.Q3TIY
