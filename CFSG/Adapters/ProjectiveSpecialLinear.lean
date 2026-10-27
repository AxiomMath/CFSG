module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.Assembly.LowTwoRank

open Matrix

export CFSG.Open.StatedAPI (statedSL_eq_range_toGL)

@[expose] noncomputable def specialLinearGroupEquivStatedSL (n : ℕ) (K : Type) [Field K] :
    SpecialLinearGroup (Fin n) K ≃* StatedSL n K :=
  (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr (statedSL_eq_range_toGL n K).symm)

theorem specialLinearGroupEquivStatedSL_coe (n : ℕ) (K : Type) [Field K]
    (A : SpecialLinearGroup (Fin n) K) :
    ((specialLinearGroupEquivStatedSL n K A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = A :=
  rfl

theorem map_center_eq_statedScalars (n : ℕ) (K : Type) [Field K] :
    (Subgroup.center (SpecialLinearGroup (Fin n) K)).map
        (specialLinearGroupEquivStatedSL n K : SpecialLinearGroup (Fin n) K →* StatedSL n K) =
      (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) := by
  ext x
  obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL n K).surjective x
  have key : A ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) ↔
      specialLinearGroupEquivStatedSL n K A ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) := by
    rw [Subgroup.mem_subgroupOf, Matrix.SpecialLinearGroup.mem_center_iff, StatedScalars,
      MonoidHom.mem_range]
    constructor
    · rintro ⟨r, hr, hA⟩
      rcases isEmpty_or_nonempty (Fin n) with hn | hn
      · have := hn
        exact ⟨1, Units.ext (Subsingleton.elim _ _)⟩
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [Fintype.card_fin, zero_pow (Fin.pos_iff_nonempty.mpr hn).ne'] at hr
        exact zero_ne_one hr
      refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
      rw [GeneralLinearGroup.coe_scalar, specialLinearGroupEquivStatedSL_coe, ← hA]
      rfl
    · rintro ⟨c, hc⟩
      have hmat : (A : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) (c : K) := by
        rw [← specialLinearGroupEquivStatedSL_coe, ← hc, GeneralLinearGroup.coe_scalar]
      refine ⟨c, ?_, hmat.symm⟩
      have := A.prop
      rw [hmat, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ] at this
      exact this
  rw [← key, Subgroup.mem_map]
  constructor
  · rintro ⟨B, hB, hBA⟩
    rwa [(specialLinearGroupEquivStatedSL n K).injective hBA] at hB
  · intro h
    exact ⟨A, h, rfl⟩

@[expose] noncomputable def projectiveSpecialLinearGroupEquivStatedProj (n : ℕ) (K : Type) [Field K] :
    ProjectiveSpecialLinearGroup (Fin n) K ≃* StatedProj (StatedSL n K) :=
  QuotientGroup.congr _ _ (specialLinearGroupEquivStatedSL n K) (map_center_eq_statedScalars n K)

theorem statedClassicalModel_psl_two_of_mulEquiv (G : Type) [Group G] (p k : ℕ)
    [Fact p.Prime] (h5 : 5 ≤ p ^ k)
    (e : G ≃* ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :
    StatedClassicalModel G .PSL 2 p k := by
  have hp : p.Prime := Fact.out
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h5
  refine ⟨⟨hp, Nat.one_le_iff_ne_zero.mpr hk, le_rfl, ?_, ?_⟩,
    GaloisField p k, inferInstance, inferInstance, GaloisField.card p k hk,
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField p k))⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

end CFSG.Assembly.LowTwoRank
