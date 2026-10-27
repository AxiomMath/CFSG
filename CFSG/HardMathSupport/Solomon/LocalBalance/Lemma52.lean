module

public import CFSG.HardMathSupport.Solomon.Proving.Basic
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

theorem glaPComponent_ne_bot {p : ℕ} {X L : Subgroup G} (h : GLAPComponent p X L) : L ≠ ⊥ := by
  intro hL
  have h3 := h.2.2.1
  subst hL
  have hbot : ((⊥ : Subgroup G).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = ⊥ := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

theorem lemma52_of_input (h : Input19_2_4) : Lemma52 := by
  intro G _ _ m hS hC B hB0
  have _ := hS.simple
  by_contra hno
  have hno' : ∀ b ∈ B, b ≠ 1 → upsilonOf B b = ⊥ := by
    intro b hb hb1
    by_contra hne
    exact hno ⟨b, hb, hb1, hne⟩
  have hnoU : ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L → ¬ IsUpsilonComponent B b L := by
    intro b hb hb1 L hL hU
    have hle : L ≤ upsilonOf B b := le_sSup hU
    rw [hno' b hb hb1] at hle
    exact glaPComponent_ne_bot hL (le_bot_iff.1 hle)
  have hΛ : ∀ b ∈ B, b ≠ 1 → lambdaOf 3 B b ≤ psiStarGroup 3 B := by
    intro b hb hb1
    refine sSup_le fun L hL => ?_
    by_contra hnle
    refine hnoU b hb hb1 L hL.1 ⟨hL.1, Or.inl ⟨le_sSup hL, hnle⟩⟩
  have hEq : lambdaStarGroup 3 B = psiStarGroup 3 B := by
    have hψ : ∀ b ∈ B, b ≠ 1 → psiStar 3 B b ≤ psiStarGroup 3 B := fun b hb hb1 =>
      le_iSup₂_of_le b hb (le_iSup (fun _ : b ≠ 1 => psiStar 3 B b) hb1)
    apply le_antisymm
    · refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
      exact sup_le (sup_le (hΛ b hb hb1) ((le_sup_right.trans le_sup_left).trans (hψ b hb hb1)))
        (le_sup_right.trans (hψ b hb hb1))
    · refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
      refine le_trans ?_ (le_iSup₂_of_le b hb (le_iSup (fun _ : b ≠ 1 => lambdaStar 3 B b) hb1))
      exact sup_le_sup_right (sup_le_sup_right (psiOf_le_lambdaOf 3 B b) _) _
  have hbal : IsBalancedWrt 3 2 B := by
    refine h G hS.nonabelian hS.kProper 3 Nat.prime_three (by norm_num) B hB0.1.1 2 (by norm_num) ?_
    intro D hD b hb hb1 J hJ
    have hJU := hnoU b hb hb1 J hJ
    have hcen : ⁅J, GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ GLAPPrimeCoreOf 3 J := by
      by_contra hcon
      exact hJU ⟨hJ, Or.inr ⟨D, hD, hcon⟩⟩
    rw [Subgroup.commutator_comm]
    exact hcen.trans (glaPPrimeCoreOf_le_of_isSubnormal 3 hJ.2.1)
  exact hC.2.2 ⟨B, CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (le_refl 3) hB0, hbal, hEq⟩

end CFSG.HardMathSupport.Solomon.LocalBalance
