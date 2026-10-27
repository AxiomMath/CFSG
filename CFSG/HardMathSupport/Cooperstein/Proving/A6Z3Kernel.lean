module

public import CFSG.HardMathSupport.Cooperstein.Proving.PCoreSup
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Cooperstein.Transport (pCore_eq_open_local)

section Subnormal

variable {Γ : Type} [Group Γ]

theorem pCoreOf_le_of_le_normalizer (p : ℕ) {H M : Subgroup Γ} (hHM : H ≤ M)
    (hMN : M ≤ Subgroup.normalizer (H : Set Γ)) :
    CFSG.Open.pCoreOf p H ≤ CFSG.Open.pCoreOf p M := by
  refine le_pCoreOf_of_normal_in (A := CFSG.Open.pCoreOf p H) (H := M) ?_ ?_ ?_
  · intro x hx
    obtain ⟨y, _, rfl⟩ := mem_pCoreOf_iff.mp hx
    exact hHM y.2
  · intro m hm a ha
    exact conj_mem_pCoreOf (hMN hm) ha
  · unfold CFSG.Open.pCoreOf
    exact CFSG.pCore_isPGroup.map _

theorem pCoreOf_le_pCoreOf_of_isSubnormal (p : ℕ) {H K : Subgroup Γ}
    (h : CFSG.Open.IsSubnormal H K) :
    CFSG.Open.pCoreOf p H ≤ CFSG.Open.pCoreOf p K := by
  induction h with
  | refl H => exact le_rfl
  | @step H M K hHM hnorm _ ih =>
    exact (pCoreOf_le_of_le_normalizer p hHM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hnorm)).trans ih

end Subnormal

end CFSG.HardMathSupport.Cooperstein.Proving
