module

public import CFSG.RankThree.PartOne.KF.SU5Centralizer

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH3

open Matrix CFSG.RankThree.PartOne.KFSU5

variable {K : Type} [Field K]

theorem eq_one_of_perfect {T M : Type*} [Group T] [CommMonoid M] (hT : commutator T = ⊤)
    (φ : T →* M) (t : T) : φ t = 1 := by
  have h1 : commutator T ≤ (MonoidHom.toHomUnits φ).ker :=
    Abelianization.commutator_subset_ker _
  rw [hT] at h1
  have h2 : MonoidHom.toHomUnits φ t = 1 := h1 (Subgroup.mem_top t)
  simpa using congrArg Units.val h2

theorem entry_eq_zero_of_commute {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → K}
    {M : Matrix ι ι K} (hM : M * diagonal d = diagonal d * M) {j k : ι} (hjk : d j ≠ d k) :
    M j k = 0 := by
  have h1 := congrFun (congrFun hM j) k
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : M j k * (d k - d j) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hjk

open scoped Classical in
@[expose] noncomputable def level {ι : Type} [Fintype ι] (d : ι → K) (c : K) : Finset ι :=
  Finset.univ.filter fun j => d j = c

omit [Field K] in
theorem mem_level {ι : Type} [Fintype ι] {d : ι → K} {c : K} {j : ι} :
    j ∈ level d c ↔ d j = c := by
  classical
  simp [level]

@[expose] def blockHom {ι : Type} [Fintype ι] [DecidableEq ι] {T : Type*} [Monoid T]
    (J : Finset ι) (ρ : T →* Matrix ι ι K) (hρ : ∀ t, ∀ j ∈ J, ∀ k ∉ J, ρ t j k = 0) :
    T →* Matrix J J K where
  toFun t := blockOf J (ρ t)
  map_one' := by rw [map_one]; exact blockOf_one J
  map_mul' s t := by rw [map_mul]; exact blockOf_mul J (hρ s)

theorem blockOf_unitary {ι : Type} [Fintype ι] [DecidableEq ι] (σ : K →+* K) (J : Finset ι)
    {X : Matrix ι ι K} (hX : (X.map σ).transpose * X = 1) (hvan : ∀ j ∈ J, ∀ k ∉ J, X k j = 0) :
    ((blockOf J X).map σ).transpose * blockOf J X = 1 := by
  have h1 : blockOf J ((X.map σ).transpose * X) = blockOf J (X.map σ).transpose * blockOf J X :=
    blockOf_mul J (fun j hj k hk => by
      simp [Matrix.transpose_apply, hvan j hj k hk])
  have h2 : blockOf J (X.map σ).transpose = ((blockOf J X).map σ).transpose := by
    ext j l
    simp [blockOf]
  rw [← h2, ← h1, hX]
  exact blockOf_one J

end CFSG.EvenSporadicStandard.M24Std.CResH3
