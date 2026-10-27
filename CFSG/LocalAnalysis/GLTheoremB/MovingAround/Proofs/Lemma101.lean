module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Conj

variable {G : Type} [Group G] [Finite G]

theorem gLBConj_eq_self_of_mem {M : Subgroup G} {y : G} (hy : y ∈ M) : GLBConj y M = M :=
  gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hy)

theorem isSCp_gLBConj_of_mem {p : ℕ} {M A : Subgroup G} {y : G} (hy : y ∈ M)
    (hA : IsSCp p M A) : IsSCp p M (GLBConj y A) := by
  refine ⟨?_, CFSG.SectionRank.isElemAbelian_map hA.2.1 _, ?_⟩
  · calc GLBConj y A ≤ GLBConj y M := gLBConj_mono y hA.1
      _ = M := gLBConj_eq_self_of_mem hy
  · intro E hEM hE hAE
    have hE' : GLBConj y⁻¹ E ≤ M := by
      calc GLBConj y⁻¹ E ≤ GLBConj y⁻¹ M := gLBConj_mono _ hEM
        _ = M := gLBConj_eq_self_of_mem (M.inv_mem hy)
    have hA' : A ≤ GLBConj y⁻¹ E := by
      have h := gLBConj_mono y⁻¹ hAE
      rwa [gLBConj_inv_gLBConj] at h
    have heq : GLBConj y⁻¹ E = A :=
      hA.2.2 _ hE' (CFSG.SectionRank.isElemAbelian_map hE _) hA'
    calc E = GLBConj y (GLBConj y⁻¹ E) := (gLBConj_gLBConj_inv y E).symm
      _ = GLBConj y A := by rw [heq]

end Conj

theorem lemma101_i_of_conj (hconj : IsUniquenessTwoLocal_conjStatement) : Lemma101_iStatement := by
  intro G _ _ m p B M h A F y hy hA hF
  have hp : 1 < p := h.standing.prime.one_lt
  have hstar : ∀ X : Subgroup G, IsSCstar p M X → IsSCstar p M (GLBConj y X) := fun X hX =>
    ⟨isSCp_gLBConj_of_mem hy hX.1, hX.2.trans
      (CFSG.SectionRank.pRank_le_map hp (MulAut.conj y⁻¹).toMonoidHom
        (MulAut.conj y⁻¹).injective X)⟩
  have hnot : ∀ X : Subgroup G, ¬ IsUniquenessTwoLocal p X M →
      ¬ IsUniquenessTwoLocal p (GLBConj y X) M := by
    intro X hX hc
    apply hX
    have h' := hconj hc (M.inv_mem hy)
    rwa [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at h'
  exact ⟨⟨hstar A hA.1, hconj hA.2 hy⟩, ⟨hstar F hF.1, hnot F hF.2⟩⟩

theorem lemma101_ii_holds : Lemma101_iiStatement := by
  intro G _ _ m p B M h
  have hS : GLStanding G m p := h.standing
  have hB : IsBOneMax p B := h.bOne
  have hsc : IsSCp p ⊤ B := lemma23_proved G m p hS B hB
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS hB h.pre
  have h3 : 3 ≤ CFSG.Open.pRank p B := by
    have h1 : m ≤ CFSG.Open.pRank p B :=
      CFSG.SectionRank.le_pRank hS.prime.one_lt le_rfl hsc.2.1 (hS.card_eq hB)
    have h2 : 4 ≤ m := hS.four_le
    omega
  exact ⟨⟨⟨hBM, hsc.2.1, fun E _ hE hBE => hsc.2.2 E le_top hE hBE⟩, h3⟩, h.uniq⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
