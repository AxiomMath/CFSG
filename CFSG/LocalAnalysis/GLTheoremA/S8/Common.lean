module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma31Proof

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace S8

variable {G : Type} [Group G] [Finite G]

theorem odd_core_of_big_rank {p : ℕ} (hp : p.Prime) {B C E : Subgroup G} (hB : GLAIsBmax p B)
    (hEC : E ≤ C) (hE : IsElemAbelian p E) (hbig : Nat.card B < Nat.card E) :
    Odd (Nat.card (GLAPPrimeCoreOf p C)) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p C)) := i183_coprime_card_glaPPrimeCoreOf hp C
  have hnorm : E ≤ Subgroup.normalizer (GLAPPrimeCoreOf p C : Set G) :=
    hEC.trans (le_normalizer_glaPPrimeCoreOf p C)
  obtain ⟨S, -, hS2, hSne, hES, -⟩ := S3.exists_invariant_sylow hp Nat.prime_two
    (isPGroup_of_isElemAbelian hE) hnorm hcop (even_iff_two_dvd.1 hodd)
  have h1 := card_le_pow_glaTwoLocalRank hp hE hSne hS2 hES
  rw [← hB.2.1] at h1
  omega

theorem sStarFacts {p : ℕ} (hc : S8Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) :
    GLAIsBmax p B ∧ x ∈ B ∧ x ≠ 1 ∧ GLAPComponent p (cx x) L ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧ (∀ b ∈ B, CentMod p L b ↔ b ∈ Subgroup.zpowers x) ∧
      CycModSylow p L ∧
      Odd (Nat.card (⁅L, GLAPPrimeCoreOf p (cx x)⁆ : Subgroup G)) := by
  have hS0M := h.1
  have hS0 := hS0M.1
  have hST := hS0.1
  exact ⟨hST.1, hST.2.1.1, hST.2.1.2.1, hST.2.2, hS0M.2.2, hc.stage5.2.1 B x L hS0M, h.2,
    hc.stage4.1 B x L hS0⟩

theorem isKGroup_cx {p : ℕ} (hc : S3Ctx G p) {x : G} (hx : x ≠ 1) : CFSG.Open.IsKGroup ↥(cx x) :=
  isKGroup_of_isKProper hc.kProper (centralizer_ne_top_of_ne_one hc.simple hc.nonabelian hx)

theorem catalog_of_component {p : ℕ} (hc : S3Ctx G p) {x : G} (hx : x ≠ 1) {L : Subgroup G}
    (hL : GLAPComponent p (cx x) L) :
    IsSimpleGroup (PSimple p L) ∧ (∃ a b : PSimple p L, a * b ≠ b * a) ∧
      IsCatalogGroup (PSimple p L) := by
  have hKC : CFSG.Open.IsKGroup ↥(cx x) := isKGroup_cx hc hx
  have hKJ : CFSG.Open.IsKGroup ↥L := CFSG.Open.IsKGroup.of_le hKC hL.1
  have hKq : CFSG.Open.IsKGroup (PQuot p L) := CFSG.Open.IsKGroup.quotient hKJ _
  have hq : CFSG.Open.IsQuasisimple (PQuot p L) := isQuasisimple_pQuot_of_glaPComponent hc.prime hL
  exact ⟨hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq,
    CFSG.HardMathSupport.Solomon.LocalBalance.isCatalogGroup_center_quotient_of_isKGroup hKq hq⟩

end S8

end CFSG.LocalAnalysis.GLTheoremA

