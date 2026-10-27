module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

public section

namespace CFSG.LieType.TwoRank

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma mem_range_scalar_of_map_mem {R S : Type*} [CommRing R] [CommRing S]
    {σ : R →+* S} (hσ : Function.Injective σ)
    {B : Matrix n n R} (hB : B.map σ ∈ Set.range (Matrix.scalar n)) :
    B ∈ Set.range (Matrix.scalar n) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨0, Matrix.ext fun i _ => (IsEmpty.false i).elim⟩
  · obtain ⟨i⟩ := hn
    obtain ⟨c, hc⟩ := hB
    have hcii : c = σ (B i i) := by
      simpa [Matrix.scalar_apply] using congrFun (congrFun hc i) i
    refine ⟨B i i, Matrix.map_injective hσ ?_⟩
    show (Matrix.scalar n (B i i)).map σ = B.map σ
    rw [← hc, hcii]
    ext a b
    by_cases hab : a = b <;> simp [Matrix.scalar_apply, hab]

theorem projGenLinGroup_map_injective {F K : Type*} [Field F] [Field K] (f : F →+* K) :
    Function.Injective (ProjGenLinGroup.map (n := n) f) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  induction g using ProjGenLinGroup.induction_on with | mk A =>
  rw [ProjGenLinGroup.map_mk, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hg
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  exact mem_range_scalar_of_map_mem f.injective hg

end CFSG.LieType.TwoRank
