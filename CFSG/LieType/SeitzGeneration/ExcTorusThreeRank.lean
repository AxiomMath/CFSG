module

public import CFSG.LieType.SeitzGeneration.ExcTorusThree
public import CFSG.LieType.SeitzGeneration.ExcTorusF4One
public import CFSG.LieType.SeitzGeneration.ExcTorusF4Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE6One
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE7One
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE8One
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Two

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE

theorem orderOf_natCast_three {q : ℕ} (hq : ¬ 3 ∣ q) :
    orderOf (q : ZMod 3) = 1 ∨ orderOf (q : ZMod 3) = 2 := by
  have h0 : (q : ZMod 3) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q 3).1 h)
  have h12 : (q : ZMod 3) = 1 ∨ (q : ZMod 3) = 2 := by
    generalize (q : ZMod 3) = x at h0 ⊢
    revert x
    decide
  rcases h12 with h | h
  · left
    rw [h]
    exact orderOf_one
  · right
    rw [h]
    exact orderOf_eq_prime (by decide) (by decide)

theorem not_rankLE2_three_of_ge {G : Type*} [Group G] {m d : ℕ} (hm : 4 ≤ m) (hd : d ≤ 3)
    {E : Subgroup G} (hE : IsElemAbelian 3 E) (hle : 3 ^ m ≤ d * Nat.card E) :
    ¬ RankLE2 3 G := by
  intro hr
  have h1 := hr E hE
  have h2 : 3 ^ 4 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h3 : d * Nat.card E ≤ 3 * 3 ^ 2 := Nat.mul_le_mul hd h1
  norm_num at h2 h3
  omega

section Rational


theorem relIndex_dvd_untwisted {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) (K : Type) [Field K]
    [Finite K] :
    ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L),
      (∀ c, Fr c = c ^ Nat.card K) → ∀ (X : Subgroup (ModGL τ L)) [Finite X],
        X ≤ adjointGroup τ L → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X ∣ d :=
  fun _ _ _ _ Fr hFr X _ hXC hXF => (finite_fixed_subgroup_rational d hτ Fr hFr X hXC hXF).1

theorem relIndex_dvd_F4 (K : Type) [Field K] [Finite K] :
    ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L),
      (∀ c, Fr c = c ^ Nat.card K) → ∀ (X : Subgroup (ModGL Tag.F4 L)) [Finite X],
        X ≤ adjointGroup Tag.F4 L → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        ((adjointGroup Tag.F4 K).map (baseChangeGL (algebraMap K L))).relIndex X ∣ 1 := by
  intro L _ _ _ Fr hFr X _ hXC hXF
  have hXle : X ≤ (adjointGroup Tag.F4 K).map (baseChangeGL (algebraMap K L)) := by
    intro y hy
    rw [← (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices Tag.F4
      (Or.inr rfl) K L Fr hFr).1]
    exact ⟨hXC hy, hXF y hy⟩
  exact Nat.dvd_one.2 (Subgroup.relIndex_eq_one.2 hXle)

end Rational

section Rank


theorem not_rankLE2_F4_three (K : Type) [Field K] [Finite K] (hpq : ¬ 3 ∣ Nat.card K) :
    ¬ RankLE2 3 (adjointGroup Tag.F4 K) := by
  have hrat := relIndex_dvd_F4 K
  rcases orderOf_natCast_three hpq with he | he
  · obtain ⟨E, hE, hle⟩ := exists_elemAbelian_three_of_blocks one_ne_zero K hrat
      (IsWeylMatrix.of_word Tag.F4 f4OneWord) [1, 1, 1, 1]
      f4One_charpoly f4One_pow he (by norm_num) (by decide)
    exact not_rankLE2_three_of_ge (m := 4) (d := 1) (by norm_num) (by norm_num) hE
      (by simpa using hle)
  · obtain ⟨E, hE, hle⟩ := exists_elemAbelian_three_of_blocks one_ne_zero K hrat
      (IsWeylMatrix.of_word Tag.F4 f4TwoWord) [2, 2, 2, 2]
      f4Two_charpoly f4Two_pow he (by norm_num) (by decide)
    exact not_rankLE2_three_of_ge (m := 4) (d := 1) (by norm_num) (by norm_num) hE
      (by simpa using hle)

theorem not_rankLE2_E6_three (K : Type) [Field K] [Finite K] (hpq : ¬ 3 ∣ Nat.card K) :
    ¬ RankLE2 3 (adjointGroup Tag.E6 K) := by
  have hrat := relIndex_dvd_untwisted 3 (Or.inl ⟨rfl, rfl⟩) K
  rcases orderOf_natCast_three hpq with he | he
  · obtain ⟨E, hE, hle⟩ := exists_elemAbelian_three_of_blocks (by norm_num) K hrat
      (IsWeylMatrix.of_word Tag.E6 e6OneWord) [1, 1, 1, 1, 1, 1]
      e6One_charpoly e6One_pow he (by norm_num) (by decide)
    exact not_rankLE2_three_of_ge (m := 6) (d := 3) (by norm_num) (by norm_num) hE
      (by simpa using hle)
  · obtain ⟨E, hE, hle⟩ := exists_elemAbelian_three_of_blocks (by norm_num) K hrat
      (IsWeylMatrix.of_word Tag.E6 e6TwoWord) [1, 1, 2, 2, 2, 2]
      e6Two_charpoly e6Two_pow he (by norm_num) (by decide)
    exact not_rankLE2_three_of_ge (m := 4) (d := 3) (by norm_num) (by norm_num) hE
      (by simpa using hle)

theorem not_rankLE2_E7_three (K : Type) [Field K] [Finite K] (hpq : ¬ 3 ∣ Nat.card K) :
    ¬ RankLE2 3 (adjointGroup Tag.E7 K) := by
  have hrat := relIndex_dvd_untwisted 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K
  rcases orderOf_natCast_three hpq with he | he
  · obtain ⟨E, hE, hle⟩ := exists_elemAbelian_three_of_blocks (by norm_num) K hrat
      (IsWeylMatrix.of_word Tag.E7 e7OneWord) [1, 1, 1, 1, 1, 1, 1]
      e7One_charpoly e7One_pow he (by norm_num) (by decide)
    exact not_rankLE2_three_of_ge (m := 7) (d := 2) (by norm_num) (by norm_num) hE
      (by simpa using hle)
  · obtain ⟨E, hE, hle⟩ := exists_elemAbelian_three_of_blocks (by norm_num) K hrat
      (IsWeylMatrix.of_word Tag.E7 e7TwoWord) [2, 2, 2, 2, 2, 2, 2]
      e7Two_charpoly e7Two_pow he (by norm_num) (by decide)
    exact not_rankLE2_three_of_ge (m := 7) (d := 2) (by norm_num) (by norm_num) hE
      (by simpa using hle)

theorem not_rankLE2_E8_three (K : Type) [Field K] [Finite K] (hpq : ¬ 3 ∣ Nat.card K) :
    ¬ RankLE2 3 (adjointGroup Tag.E8 K) := by
  have hrat := relIndex_dvd_untwisted 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K
  rcases orderOf_natCast_three hpq with he | he
  · obtain ⟨E, hE, hle⟩ := exists_elemAbelian_three_of_blocks one_ne_zero K hrat
      (IsWeylMatrix.of_word Tag.E8 e8OneWord) [1, 1, 1, 1, 1, 1, 1, 1]
      e8One_charpoly e8One_pow he (by norm_num) (by decide)
    exact not_rankLE2_three_of_ge (m := 8) (d := 1) (by norm_num) (by norm_num) hE
      (by simpa using hle)
  · obtain ⟨E, hE, hle⟩ := exists_elemAbelian_three_of_blocks one_ne_zero K hrat
      (IsWeylMatrix.of_word Tag.E8 e8TwoWord) [2, 2, 2, 2, 2, 2, 2, 2]
      e8Two_charpoly e8Two_pow he (by norm_num) (by decide)
    exact not_rankLE2_three_of_ge (m := 8) (d := 1) (by norm_num) (by norm_num) hE
      (by simpa using hle)

end Rank

end CFSG.LieType.SeitzGeneration
