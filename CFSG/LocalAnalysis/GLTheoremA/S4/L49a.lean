module

public import CFSG.LocalAnalysis.GLTheoremA.S4.StepTools
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem glaPLayer_closureIn_inf_centralizer_ne_bot {p : ℕ} (hp : p.Prime) (h183 : Input18_3_4)
    (hLB : LBalanceAt G p) (hKP : CFSG.Open.IsKProper G) {C L A B E : Subgroup G} (hC : C ≠ ⊤)
    (hL : GLAPComponent p C L) (hB : IsElemAbelian p B) (hBC : B ≤ C) (hAB : A ≤ B) (hEB : E ≤ B)
    (hne : GLAPLayer p (closureIn L B ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥) :
    GLAPLayer p (closureIn L A ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G)) ≠ ⊥ := by
  set K := closureIn L B with hKdef
  set H := closureIn L A with hHdef
  set F : Subgroup G := E ⊓ A with hFdef
  have hEel : IsElemAbelian p E := isElemAbelian_mono hB hEB
  have hEp : IsPGroup p E := isPGroup_of_isElemAbelian hEel
  have hFB : F ≤ B := inf_le_right.trans hAB
  have hFel : IsElemAbelian p F := isElemAbelian_mono hB hFB
  have hFC : F ≤ C := (inf_le_left.trans hEB).trans hBC
  have hBF : B ≤ Subgroup.centralizer (F : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun f hf => isElemAbelian_commute hB (hFB hf) hb
  have hEF : E ≤ Subgroup.centralizer (F : Set G) := hEB.trans hBF
  have hKC : K ≤ C := by
    rw [hKdef, closureIn_eq_iSup_gLBConj]
    refine iSup₂_le fun g hg => ?_
    have hgC : GLBConj g C = C :=
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hBC hg))
    exact (gLBConj_mono (g := g) hL.1).trans hgC.le
  have hHK : H ≤ K := by
    rw [hHdef, hKdef, closureIn_eq_iSup_gLBConj L A, closureIn_eq_iSup_gLBConj L B]
    exact iSup₂_le fun a ha => le_biSup (fun g => GLBConj g L) (hAB ha)
  have hEK : E ≤ Subgroup.normalizer (K : Set G) := hEB.trans (le_normalizer_closureIn L B)
  have hPX : E ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) : Set G) := by
    intro e he
    rw [mem_normalizer_iff_gLBConj_eq, gLBConj_inf, mem_normalizer_iff_gLBConj_eq.1 (hEK he),
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hEF he))]
  have hXC : (K ⊓ Subgroup.centralizer (F : Set G)) ⊔ E ≤ C :=
    sup_le (inf_le_left.trans hKC) (hEB.trans hBC)
  have hKG : CFSG.Open.IsKGroup ↥((K ⊓ Subgroup.centralizer (F : Set G)) ⊔ E) :=
    isKGroup_of_isKProper hKP (ne_top_of_le_ne_top hC hXC)
  have hCEF : Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer (F : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 inf_le_left)
  have hXE : K ⊓ Subgroup.centralizer (F : Set G) ⊓ Subgroup.centralizer (E : Set G) =
      K ⊓ Subgroup.centralizer (E : Set G) := by
    rw [inf_assoc, inf_eq_right.2 hCEF]
  have hle : GLAPLayer p (K ⊓ Subgroup.centralizer (F : Set G) ⊓ Subgroup.centralizer (E : Set G)) ≤
      GLAPLayer p (K ⊓ Subgroup.centralizer (F : Set G)) :=
    glaPLayer_inf_centralizer_le hp hLB hKG hEp hPX
  have hX : GLAPLayer p (K ⊓ Subgroup.centralizer (F : Set G)) ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← hXE]
    apply le_bot_iff.1
    rw [← hbot]
    exact hle
  obtain ⟨W, hW⟩ : ∃ W, GLAPComponent p (K ⊓ Subgroup.centralizer (F : Set G)) W := by
    by_contra hcon
    exact hX (le_bot_iff.1 (sSup_le fun a ha => (hcon ⟨a, ha⟩).elim))
  obtain ⟨𝓛, h𝓛def⟩ : ∃ 𝓛 : Set (Subgroup G), 𝓛 = {X | ∃ b ∈ B, GLBConj b L = X} :=
    ⟨_, rfl⟩
  have hmem : ∀ X, X ∈ 𝓛 ↔ ∃ b ∈ B, GLBConj b L = X := fun X => by
    rw [h𝓛def, Set.mem_setOf_eq]
  have h𝓛C : ∀ X ∈ 𝓛, GLAPComponent p C X := by
    intro X hX
    obtain ⟨b, hb, rfl⟩ := (hmem X).1 hX
    have := glaPComponent_gLBConj hL b
    rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hBC hb))] at this
  have hsup : sSup 𝓛 = K := by
    apply le_antisymm
    · refine sSup_le fun X hX => ?_
      obtain ⟨b, hb, rfl⟩ := (hmem _).1 hX
      rw [hKdef, closureIn_eq_iSup_gLBConj L B]
      exact le_biSup (fun g => GLBConj g L) hb
    · rw [hKdef, closureIn_eq_iSup_gLBConj L B]
      refine iSup₂_le fun b hb => ?_
      exact le_sSup ((hmem _).2 ⟨b, hb, rfl⟩)
  have hKsn : IsSubnormal K C := by
    rw [← hsup]
    exact isSubnormal_sSup_glaPComponent hp 𝓛 h𝓛C
  have hsn : IsSubnormal (K ⊓ Subgroup.centralizer (F : Set G))
      (C ⊓ Subgroup.centralizer (F : Set G)) :=
    hKsn.inf _
  have hW' : GLAPComponent p (C ⊓ Subgroup.centralizer (F : Set G)) W :=
    glaPComponent_of_isSubnormal' hp hsn hW
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, h𝒞tr⟩ :=
    h183 G C (isKGroup_of_isKProper hKP hC) p hp F hFC hFel W hW'
  have hGN : GLAPLayer p C ≤ Subgroup.normalizer (K : Set G) := by
    rw [← hsup]
    refine sSup_le fun Y hY => ?_
    intro y hy
    refine mem_normalizer_sSup fun X hX => ?_
    by_cases hXY : X = Y
    · subst hXY
      exact Subgroup.le_normalizer hy
    · exact CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp (h𝓛C X hX)
        (show GLAPComponent p C Y from hY) hXY hy
  have hsupK : (⨆ L' ∈ 𝒞, L') ≤ K := by
    rw [h𝒞sup]
    refine iSup₂_le fun g hg => ?_
    have hWK : W ≤ K := hW.1.trans inf_le_left
    exact (gLBConj_mono (g := g) hWK).trans (mem_normalizer_iff_gLBConj_eq.1 (hGN hg)).le
  have h𝒞𝓛 : ∀ L' ∈ 𝒞, L' ∈ 𝓛 := by
    intro L' hL'
    have hle' : L' ≤ sSup 𝓛 := by
      rw [hsup]
      exact (le_biSup (fun L'' => L'') hL').trans hsupK
    exact mem_of_le_sSup_glaPComponent hp 𝓛 h𝓛C (h𝒞c L' hL') hle'
  have hWsub : W ≤ ⨆ L' ∈ 𝒞, L' := by
    rw [h𝒞sup]
    have h1 : GLBConj 1 W ≤ ⨆ g ∈ GLAPLayer p C, GLBConj g W :=
      le_biSup (fun g => GLBConj g W) (Subgroup.one_mem _)
    rwa [gLBConj_one] at h1
  have hne𝒞 : 𝒞.Nonempty := by
    rcases Set.eq_empty_or_nonempty 𝒞 with h0 | h0
    · exfalso
      apply glaPComponent_ne_bot' hW'
      apply le_bot_iff.1
      have h2 : (⨆ L' ∈ 𝒞, L') = ⊥ := by simp [h0]
      exact hWsub.trans h2.le
    · exact h0
  obtain ⟨L₁, hL₁⟩ := hne𝒞
  obtain ⟨b, hb, hbL⟩ := (hmem L₁).1 (h𝒞𝓛 L₁ hL₁)
  have hcomm : ∀ a ∈ A, a * b = b * a := fun a ha => isElemAbelian_commute hB (hAB ha) hb
  have hWH : W ≤ closureIn L₁ A := by
    refine hWsub.trans (iSup₂_le fun L' hL' => ?_)
    obtain ⟨e, he, rfl⟩ := h𝒞tr L₁ hL₁ L' hL'
    rw [closureIn_eq_iSup_gLBConj L₁ A]
    exact le_biSup (fun g => GLBConj g L₁) (Subgroup.mem_inf.1 he).2
  have hL₁eq : closureIn L₁ A = GLBConj b H := by
    rw [hHdef, ← hbL, gLBConj_closureIn_of_commute hcomm]
  have hbK : GLBConj b H ≤ K :=
    (gLBConj_mono (g := b) hHK).trans (mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_closureIn L B hb)).le
  have hHC : GLBConj b H ⊓ Subgroup.centralizer (F : Set G) ≤ C ⊓ Subgroup.centralizer (F : Set G) :=
    inf_le_inf_right _ (hbK.trans hKC)
  have hW3 : W ≤ GLBConj b H ⊓ Subgroup.centralizer (F : Set G) :=
    le_inf (hWH.trans hL₁eq.le) (hW.1.trans inf_le_right)
  have hW4 : GLAPComponent p (GLBConj b H ⊓ Subgroup.centralizer (F : Set G)) W :=
    glaPComponent_of_le hp hW' hW3 hHC
  have hW5 := glaPComponent_gLBConj hW4 b⁻¹
  have hbC : b⁻¹ ∈ Subgroup.centralizer (F : Set G) := Subgroup.inv_mem _ (hBF hb)
  have hconjC : GLBConj b⁻¹ (Subgroup.centralizer (F : Set G)) = Subgroup.centralizer (F : Set G) :=
    mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hbC)
  have hconjX : GLBConj b⁻¹ (GLBConj b H ⊓ Subgroup.centralizer (F : Set G)) =
      H ⊓ Subgroup.centralizer (F : Set G) := by
    rw [gLBConj_inf, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one, hconjC]
  rw [hconjX] at hW5
  intro hbot
  have h1 : GLBConj b⁻¹ W ≤ GLAPLayer p (H ⊓ Subgroup.centralizer (F : Set G)) := le_sSup hW5
  rw [hbot] at h1
  exact glaPComponent_ne_bot' hW5 (le_bot_iff.1 h1)

end CFSG.LocalAnalysis.GLTheoremA
