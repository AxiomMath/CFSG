module

public import CFSG.LocalAnalysis.GLTheoremA.Sec5A

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem exists_glaIsBmax {p : ℕ} (hp : 1 < p) (h : 0 < GLATwoLocalRank p G) :
    ∃ B : Subgroup G, GLAIsBmax p B := by
  classical
  set S : Set ℕ := {k | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank p H = k}
  have hS : GLATwoLocalRank p G = sSup S := rfl
  have hne : S.Nonempty := by
    by_contra hS'
    rw [Set.not_nonempty_iff_eq_empty] at hS'
    rw [hS, hS'] at h
    simp at h
  obtain ⟨H, hH, hHk⟩ := Nat.sSup_mem hne (bddAbove_twoLocalPRanks hp)
  obtain ⟨E, hEH, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp H
  obtain ⟨P, hP, hP2, rfl⟩ := hH
  refine ⟨E, hE, ?_, P, hP, hP2, hEH⟩
  rw [hEc, hHk, ← hS]

theorem four_le_glaTwoLocalRank_of_mem_mu {m : ℕ} (hctx : ThmACtx G m) {p : ℕ}
    (hp : p ∈ Mu G m) : 4 ≤ GLATwoLocalRank p G := by
  rw [hp.2.1]
  exact hctx.1.four_le

theorem sec5Ctx_of {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m) (hS3 : Stage3 G p)
    (hS4o : Stage4Order G p) (hS4 : Stage4 G p) (h183 : Input18_3_4) : Sec5Ctx G p where
  prime := hp.1.1
  odd := hp.1.2.1
  simple := hctx.1.simple
  nonabelian := hctx.1.nonabelian
  kProper := hctx.1.kProper
  stage3 := hS3
  stage4Order := hS4o
  stage4 := hS4
  input18_3_4 := h183

end CFSG.LocalAnalysis.GLTheoremA
