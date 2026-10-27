module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

theorem lemma102_holds : Lemma102Statement := by
  intro G _ _ m p B M h Q _hQM _hQ k hk hne hsub
  haveI : Fact p.Prime := ⟨h.standing.prime⟩
  intro x hx
  obtain ⟨E0, hE0⟩ := hne
  obtain ⟨D, hDE0, hDel, hDcard⟩ :=
    exists_le_isElemAbelian_card hE0.2.1 (n := 2) (by rw [hE0.2.2]; exact pow_dvd_pow p hk)
  have hD : IsPPlane p D := ⟨hDel, hDcard⟩
  set S : Subgroup G := Subgroup.zpowers x with hSdef
  have hSN : S ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.2 hx
  have hxS : x ∈ S := Subgroup.mem_zpowers x
  have key : ∀ y ∈ S, pCoreOf 2 M ≤ gammaStar p (GLBConj y D) ∧
      ∀ T : Subgroup G, pCoreOf 2 M ≤ T → T ≤ gammaStar p (GLBConj y D) →
        Subgroup.normalizer (T : Set G) ≤ M := by
    intro y hy
    have hQy : GLBConj y Q = Q := gLBConj_eq_of_mem_normalizer (hSN hy)
    have hEy : IsEkIn p k Q (GLBConj y E0) :=
      ⟨(gLBConj_mono y hE0.1).trans hQy.le, CFSG.SectionRank.isElemAbelian_map hE0.2.1 _, by
        rw [GLBConj, Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective]
        exact hE0.2.2⟩
    obtain ⟨A, hA, hEA⟩ := (hsub _ hEy).2.2
    exact hA.2.clause_c _ ((gLBConj_mono y hDE0).trans hEA) (isPPlane_gLBConj y hD)
  set T : Subgroup G := ⨅ (y : G) (_ : y ∈ S), gammaStar p (GLBConj y D) with hTdef
  have hmemT : ∀ t : G, t ∈ T ↔ ∀ y ∈ S, t ∈ gammaStar p (GLBConj y D) := by
    intro t
    simp only [hTdef, Subgroup.mem_iInf]
  have hcoreT : pCoreOf 2 M ≤ T := fun t ht => (hmemT t).2 fun y hy => (key y hy).1 ht
  have hTle : T ≤ gammaStar p (GLBConj 1 D) := fun t ht => (hmemT t).1 ht 1 S.one_mem
  have hconjF : ∀ y s : G, x * s * x⁻¹ ∈ gammaStar p (GLBConj y D) ↔
      s ∈ gammaStar p (GLBConj (y * x) D) := by
    intro y s
    rw [← mem_gLBConj, ← gammaStar_gLBConj, gLBConj_gLBConj]
  have hconjT : GLBConj x T = T := by
    ext t
    rw [mem_gLBConj, hmemT, hmemT]
    simp only [hconjF]
    constructor
    · intro h' y hy
      have h'' := h' (y * x⁻¹) (S.mul_mem hy (S.inv_mem hxS))
      rwa [inv_mul_cancel_right] at h''
    · intro h' y hy
      exact h' (y * x) (S.mul_mem hy hxS)
  have hxT : x ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_iff_gLBConj_eq.2 hconjT
  exact (key 1 S.one_mem).2 T hcoreT hTle hxT

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
