module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Constrained

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

omit [Finite X] in
theorem isElemAbelian_of_le {E F : Subgroup X} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE

omit [Finite X] in
theorem card_eq_sq_of_relIndex {E F : Subgroup X} (hp : p.Prime) (hFE : F ≤ E)
    (hrel : F.relIndex E = p) (hcard : Nat.card E = p ^ 3) : Nat.card F = p ^ 2 := by
  have h1 : Nat.card (F.subgroupOf E) * F.relIndex E = Nat.card E := Subgroup.card_mul_index _
  have h2 : Nat.card (F.subgroupOf E) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv
  rw [h2, hrel, hcard] at h1
  have hp0 : 0 < p := hp.pos
  have : Nat.card F * p = p ^ 2 * p := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hp0 this

theorem normalizer_hyperplane_le (h : ReducedNongeneration p X R X₀) {E F : Subgroup X}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) (hER : E ≤ (R : Subgroup X))
    (hFE : F ≤ E) (hrel : F.relIndex E = p) : Subgroup.normalizer (F : Set X) ≤ X₀ := by
  have hp := h.prime
  have hFa : IsElemAbelian p F := isElemAbelian_of_le hE hFE
  have hFc : Nat.card F = p ^ 2 := card_eq_sq_of_relIndex hp hFE hrel hcard
  have h2 : 2 ≤ Open.pRank p F :=
    le_pRank_of_isElemAbelian_of_pow_le_card hp hFa le_rfl (by rw [hFc])
  have hEC : E ≤ F ⊔ ((R : Subgroup X) ⊓ Subgroup.centralizer (F : Set X)) := by
    intro x hx
    refine Subgroup.mem_sup_right ⟨hER hx, Subgroup.mem_centralizer_iff.2 fun f hf => ?_⟩
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨f, hFE hf⟩ ⟨x, hx⟩)
  have h3 : 3 ≤ Open.pRank p (F ⊔ ((R : Subgroup X) ⊓ Subgroup.centralizer (F : Set X))) :=
    le_pRank_of_isElemAbelian_of_pow_le_card hp hE hEC (by rw [hcard])
  refine le_trans ?_ h.weakCore_le
  exact le_sSup ⟨F, hFE.trans hER, h2, h3, rfl⟩

theorem false_of_le_closure_normalizers (h : ReducedNongeneration p X R X₀) {K E : Subgroup X}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) (hER : E ≤ (R : Subgroup X))
    (hEN : E ≤ (K ⊔ (R : Subgroup X)).normalCore)
    (hgen : K ≤ Subgroup.closure {k : X | ∃ F : Subgroup X, F ≤ E ∧ F.relIndex E = p ∧
      k ∈ Subgroup.normalizer (F : Set X)}) : False := by
  have hKX : K ≤ X₀ := by
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro k ⟨F, hFE, hrel, hk⟩
    exact normalizer_hyperplane_le h hE hcard hER hFE hrel hk
  have hNX : (K ⊔ (R : Subgroup X)).normalCore ≤ X₀ :=
    (Subgroup.normalCore_le _).trans (sup_le hKX h.sylow_le)
  have h2 := h.pRank_le_two_of_normal_le hNX
  have h3 := le_pRank_of_isElemAbelian_of_pow_le_card h.prime hE hEN (n := 3) (by rw [hcard])
  omega

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
