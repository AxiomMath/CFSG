module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
import CFSG.LocalAnalysis.RankThreeUC.Focal
import CFSG.LocalAnalysis.RankThreeUC.AGL81CStrongEmb

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem commutator_le_of_index_prime {M : Type} [Group M] {N : Subgroup M} [N.Normal] {p : ℕ}
    (hp : p.Prime) (h : N.index = p) : commutator M ≤ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (M ⧸ N) = p := by
    rw [← Subgroup.index_eq_card]
    exact h
  haveI : IsCyclic (M ⧸ N) := isCyclic_of_prime_card hcard
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  have h1 : (QuotientGroup.mk ⁅x, y⁆ : M ⧸ N) = 1 := by
    rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      ((inferInstance : IsMulCommutative (M ⧸ N)).is_comm.comm _ _)
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem no_normal_index_p_of_strong {G : Type} [Group G] [Finite G] (hperf : commutator G = ⊤)
    {M : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M) (N : Subgroup ↥M) [N.Normal] :
    N.index ≠ p := by
  intro hidx
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : commutator ↥M ≤ N := commutator_le_of_index_prime hp hidx
  have hNM : N.map M.subtype ≤ M := Subgroup.map_subtype_le N
  have hMM : ⁅M, M⁆ ≤ N.map M.subtype := by
    rw [← Subgroup.map_subtype_commutator M]
    exact Subgroup.map_mono hcomm
  apply CFSG.RankThree.PartOne.IsStronglyPEmbedded.not_dvd_relIndex_of_commutator_le hperf hM hNM
    hMM
  have hrel : (N.map M.subtype).relIndex M = N.index := by
    have := Subgroup.relIndex_map_map_of_injective N ⊤ M.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.relIndex_top_right] at this
    exact this
  rw [hrel, hidx]

theorem no_normal_index_p_of_ctx_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M}
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂) {p : ℕ}
    (hp : p ∈ sigmaM G M) (N : Subgroup ↥M) [N.Normal] : N.index ≠ p := by
  haveI := ctx.cstar.simple
  exact no_normal_index_p_of_strong (commutator_eq_top_of_standing ctx.cstar.nonab)
    (sigmaA_prime p hp.1) (ctx.strong p hp) N

end CFSG.LocalAnalysis.RankThreeUC.S15
