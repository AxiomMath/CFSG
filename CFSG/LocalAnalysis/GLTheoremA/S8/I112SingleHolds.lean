module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma83Inputs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112a
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Levels
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxClaim

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

namespace S8.L83

theorem i112SingleAt_holds (G : Type) [Group G] [Finite G]
    : I112SingleAt G := by
  intro p hp hp2 X E J d hX hdE hEX hEel hr hJ hEJ hn
  obtain ⟨n, hn8, hnJ⟩ := hn
  classical
  have hZX : Subgroup.zpowers d ≤ X := Subgroup.zpowers_le.2 (hEX hdE)
  have hZE : Subgroup.zpowers d ≤ E := Subgroup.zpowers_le.2 hdE
  have hZel : IsElemAbelian p (Subgroup.zpowers d) := isElemAbelian_mono hEel hZE
  obtain ⟨𝒞, hC1, hC2, -, hC4⟩ :=
    input18_3_4_holds G X hX p hp (Subgroup.zpowers d) hZX hZel J hJ
  have hJW : J ≤ ⨆ L ∈ 𝒞, L := by
    rw [hC2]
    exact le_iSup₂_of_le 1 (GLAPLayer p X).one_mem (by rw [gLBConj_one])
  by_cases hA : ∃ L₀ ∈ 𝒞, d ∈ Subgroup.normalizer (L₀ : Set G)
  ·
    obtain ⟨L₀, hL₀, hdL₀⟩ := hA
    have hall : ∀ L ∈ 𝒞, L = L₀ := by
      intro L hL
      obtain ⟨e, he, hLe⟩ := hC4 L₀ hL₀ L hL
      have he' : e ∈ Subgroup.normalizer (L₀ : Set G) := (Subgroup.zpowers_le.2 hdL₀) he
      rw [← hLe, mem_normalizer_iff_gLBConj_eq.1 he']
    have hW : (⨆ L ∈ 𝒞, L) = L₀ :=
      le_antisymm (iSup₂_le fun L hL => (hall L hL).le) (le_iSup₂_of_le L₀ hL₀ le_rfl)
    refine ⟨L₀, hC1 L₀ hL₀, hW ▸ hJW, ?_⟩
    have hEN : E ≤ Subgroup.normalizer ((closureIn J (GLAPLayer p X) : Subgroup G) : Set G) :=
      L62.le_normalizer_closureIn_of_le hEJ
        (fun g hg => mem_normalizer_glaPLayer (Subgroup.le_normalizer (hEX hg)))
    rw [closureIn_eq_iSup_gLBConj, ← hC2, hW] at hEN
    exact hEN
  ·
    push Not at hA
    obtain ⟨L₁, hL₁mem⟩ : ∃ L₁, L₁ ∈ 𝒞 := by
      by_contra hne
      push Not at hne
      have h0 : (⨆ L ∈ 𝒞, L) = ⊥ := by
        simp only [iSup_eq_bot]
        intro L hL
        exact absurd hL (hne L)
      exact glaPComponent_ne_bot' hJ (le_bot_iff.1 (h0 ▸ hJW))
    have hL₁ : GLAPComponent p X L₁ := hC1 L₁ hL₁mem
    have hdn : d ∉ Subgroup.normalizer (L₁ : Set G) := hA L₁ hL₁mem
    have hnE : ¬ E ≤ Subgroup.normalizer (L₁ : Set G) := fun h => hdn (h hdE)
    have hr' : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p E :=
      CFSG.AGLEmbedding.le_pRank_of_pow_le_card hp le_rfl hEel hr
    obtain ⟨-, hcat⟩ := i112StarAt_holds G p hp hp2 X E L₁ hX hEX hEel hr' hL₁ hnE
    have hJle : J ≤ closureIn L₁ E := by
      refine hJW.trans (iSup₂_le fun L hL => ?_)
      obtain ⟨e, he, hLe⟩ := hC4 L₁ hL₁mem L hL
      rw [← hLe, closureIn_eq_iSup_gLBConj]
      exact le_iSup₂_of_le e (hZE he) le_rfl
    have hcl : closureIn L₁ E ≤ X := by
      rw [closureIn_eq_iSup_gLBConj]
      refine iSup₂_le fun e he => ?_
      calc GLBConj e L₁ ≤ GLBConj e X := gLBConj_mono (g := e) hL₁.1
        _ = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hEX he))
    have hJcomp : GLAPComponent p (closureIn L₁ E ⊓
        Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G)) J :=
      glaPComponent_of_le hp hJ (le_inf hJle (hJ.1.trans inf_le_right)) (inf_le_inf hcl le_rfl)
    rw [S3.centralizer_zpowers d] at hJcomp
    obtain ⟨e⟩ := hnJ
    exact (altNotWeakExcAt_holds n hn8 ((catalogIs_congr e).1 (hcat d hdE hdn J hJcomp))).elim

end S8.L83

end CFSG.LocalAnalysis.GLTheoremA
