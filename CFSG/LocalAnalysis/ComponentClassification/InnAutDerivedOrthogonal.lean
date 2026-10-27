module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.RankThree.PartOne.OutStructure
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open scoped commutatorElement

theorem innAutDerived_le_orthD_of_matrixProjectiveImage_eq_top {K : Type} [Field K] [Finite K]
    {d : ℕ} (Q : QuadraticForm K (Fin d → K)) (htop : matrixProjectiveImage Q = ⊤) :
    innAutDerived (matrixProjectiveDerived Q) ≤ orthD Q := by
  refine sup_le (inner_le_orthD Q) ?_
  rw [commutator_def, Subgroup.commutator_le]
  intro γ _ α _
  obtain ⟨g, rfl⟩ := (mem_matrixProjectiveImage_iff Q γ).mp (htop ▸ Subgroup.mem_top γ)
  obtain ⟨h, rfl⟩ := (mem_matrixProjectiveImage_iff Q α).mp (htop ▸ Subgroup.mem_top α)
  exact comm_mem_orthD Q g h

theorem mem_inner_of_mem_innAutDerived_of_pow_eq_one {K : Type} [Field K] [Finite K]
    {d : ℕ} (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (hab : ∃ k : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ k)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (htop : matrixProjectiveImage Q = ⊤)
    {β : MulAut (matrixProjectiveDerived Q)}
    (hβ : β ∈ innAutDerived (matrixProjectiveDerived Q)) (hβp : β ^ p = 1) :
    β ∈ inner (matrixProjectiveDerived Q) := by
  have hβD := innAutDerived_le_orthD_of_matrixProjectiveImage_eq_top Q htop hβ
  have h1 : β ^ (p ^ 1) ∈ inner (matrixProjectiveDerived Q) := by
    rw [pow_one, hβp]
    exact one_mem _
  exact orthD_D2_of_bound' Q hQ hab hp hp2 hβD h1

theorem exists_pow_eq_one_of_mem_inner {S : Type} [Group S] (hZ : Subgroup.center S = ⊥)
    {p : ℕ} {β : MulAut S} (hβ : β ∈ inner S) (hβp : β ^ p = 1) :
    ∃ a : S, a ^ p = 1 ∧ β = MulAut.conj a := by
  obtain ⟨a, rfl⟩ := hβ
  refine ⟨a, ?_, rfl⟩
  have h : MulAut.conj (a ^ p) = 1 := by
    rw [map_pow]
    exact hβp
  exact CFSG.mulAutConj_injective_of_center_eq_bot hZ (h.trans (map_one _).symm)

end CFSG.ComponentClassification.OuterAutomorphisms

end
