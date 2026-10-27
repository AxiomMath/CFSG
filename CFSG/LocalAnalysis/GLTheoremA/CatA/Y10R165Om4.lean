module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks7

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks QuadraticMap Polynomial
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

namespace OmEngine


section Blocks

variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ} {Q : QuadraticForm F V}

def nonBotBlocks (p : ℕ) : Finset (Hyperplane A p) :=
  Finset.univ.filter fun D => blockSpace A D.1 ≠ ⊥

@[simp] theorem mem_nonBotBlocks (p : ℕ) {D : Hyperplane A p} :
    D ∈ nonBotBlocks A p ↔ blockSpace A D.1 ≠ ⊥ := by
  simp [nonBotBlocks]

private theorem finrank_blockSpace_pos [FiniteDimensional F V]
    {D : Hyperplane A p} (hD : blockSpace A D.1 ≠ ⊥) :
    0 < Module.finrank F ↥(blockSpace A D.1) := by
  rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
  exact hD

theorem exists_two_min_blocks (h2 : 2 ≤ (nonBotBlocks A p).card) :
    ∃ D E : Hyperplane A p, D ∈ nonBotBlocks A p ∧ E ∈ nonBotBlocks A p ∧ D ≠ E ∧
      (∀ G ∈ nonBotBlocks A p,
        Module.finrank F ↥(blockSpace A D.1) ≤ Module.finrank F ↥(blockSpace A G.1)) ∧
      (∀ G ∈ nonBotBlocks A p, G ≠ D →
        Module.finrank F ↥(blockSpace A E.1) ≤ Module.finrank F ↥(blockSpace A G.1)) := by
  classical
  have hne : (nonBotBlocks A p).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨D, hDS, hDmin⟩ := Finset.exists_min_image (nonBotBlocks A p)
    (fun D => Module.finrank F ↥(blockSpace A D.1)) hne
  have hpos : 0 < ((nonBotBlocks A p).erase D).card := by
    rw [Finset.card_erase_of_mem hDS]
    omega
  have hne' : ((nonBotBlocks A p).erase D).Nonempty := Finset.card_pos.mp hpos
  obtain ⟨E, hES, hEmin⟩ := Finset.exists_min_image ((nonBotBlocks A p).erase D)
    (fun E => Module.finrank F ↥(blockSpace A E.1)) hne'
  rw [Finset.mem_erase] at hES
  exact ⟨D, E, hDS, hES.2, hES.1.symm, hDmin, fun G hG hGD => hEmin G (by
    rw [Finset.mem_erase]
    exact ⟨hGD, hG⟩)⟩

private theorem finrank_three_blockSpace_le [FiniteDimensional F V] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A) {D E G : Hyperplane A p}
    (hDE : D ≠ E) (hDG : D ≠ G) (hEG : E ≠ G) :
    Module.finrank F ↥(blockSpace A D.1) + Module.finrank F ↥(blockSpace A E.1) +
        Module.finrank F ↥(blockSpace A G.1) ≤ Module.finrank F V := by
  classical
  have hdisj : ∀ i : Hyperplane A p, Disjoint (blockSpace A i.1)
      (⨆ j, ⨆ (_ : j ≠ i), blockSpace A j.1) :=
    iSupIndep_def.mp (iSupIndep_blockSpace A hp hpF hA)
  have hEGbot : blockSpace A E.1 ⊓ blockSpace A G.1 = ⊥ := by
    have h := disjoint_iff_inf_le.mp (hdisj E)
    refine le_bot_iff.mp (le_trans ?_ h)
    exact inf_le_inf_left _ (le_iSup₂ (f := fun j (_ : j ≠ E) => blockSpace A j.1) G
      (Ne.symm hEG))
  have hDbot : blockSpace A D.1 ⊓ (blockSpace A E.1 ⊔ blockSpace A G.1) = ⊥ := by
    have h := disjoint_iff_inf_le.mp (hdisj D)
    refine le_bot_iff.mp (le_trans ?_ h)
    refine inf_le_inf_left _ (sup_le ?_ ?_)
    · exact le_iSup₂ (f := fun j (_ : j ≠ D) => blockSpace A j.1) E (Ne.symm hDE)
    · exact le_iSup₂ (f := fun j (_ : j ≠ D) => blockSpace A j.1) G (Ne.symm hDG)
  have hEG : Module.finrank F ↥(blockSpace A E.1 ⊔ blockSpace A G.1) =
      Module.finrank F ↥(blockSpace A E.1) + Module.finrank F ↥(blockSpace A G.1) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (blockSpace A E.1) (blockSpace A G.1)
    rw [hEGbot, finrank_bot, add_zero] at h
    omega
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (blockSpace A D.1)
    (blockSpace A E.1 ⊔ blockSpace A G.1)
  rw [hDbot, finrank_bot, add_zero, hEG] at hsup
  have hle : Module.finrank F ↥(blockSpace A D.1 ⊔ (blockSpace A E.1 ⊔ blockSpace A G.1)) ≤
      Module.finrank F V := by
    have h := Submodule.finrank_mono (le_top : blockSpace A D.1 ⊔
      (blockSpace A E.1 ⊔ blockSpace A G.1) ≤ (⊤ : Submodule F V))
    rwa [finrank_top] at h
  omega

private theorem mul_card_le_sum_blockSpace (S : Finset (Hyperplane A p)) (m : ℕ)
    (h : ∀ H ∈ S, m ≤ Module.finrank F ↥(blockSpace A H.1)) :
    m * S.card ≤ ∑ H ∈ S, Module.finrank F ↥(blockSpace A H.1) := by
  have hconst : ∑ _H ∈ S, m = m * S.card := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  calc m * S.card = ∑ _H ∈ S, m := hconst.symm
    _ ≤ ∑ H ∈ S, Module.finrank F ↥(blockSpace A H.1) := Finset.sum_le_sum h

theorem exists_blocks_regimeI [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hpF : (p : F) ≠ 0) (hp2 : p ≠ 2)
    (hA : IsElemAbelian p A)
    (hB : ∀ a : ↥A, ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {n : ℕ} (hn : Nat.card F = 2 ^ n)
    (hm0 : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n)
    (h3 : 3 ≤ (nonBotBlocks A p).card) :
    ∃ D E : Hyperplane A p, D ∈ nonBotBlocks A p ∧ E ∈ nonBotBlocks A p ∧ D ≠ E ∧
      8 ≤ Module.finrank F ↥(fixedSpace (blockEnd A hp hpF hA t ht D)) ∧
      4 ≤ Module.finrank F ↥(fixedSpace
        (blockEnd A hp hpF hA t ht D * blockEnd A hp hpF hA t ht E)) := by
  classical
  have h2 : 2 ≤ (nonBotBlocks A p).card := by omega
  obtain ⟨D, E, hDS, hES, hDE, hDmin, hEmin⟩ := exists_two_min_blocks A (p := p) h2
  have hDne : blockSpace A D.1 ≠ ⊥ := (mem_nonBotBlocks A p).mp hDS
  have hEne : blockSpace A E.1 ≠ ⊥ := (mem_nonBotBlocks A p).mp hES
  have hES' : E ∈ (nonBotBlocks A p).erase D := by
    rw [Finset.mem_erase]
    exact ⟨Ne.symm hDE, hES⟩
  have hpos : 0 < (((nonBotBlocks A p).erase D).erase E).card := by
    rw [Finset.card_erase_of_mem hES', Finset.card_erase_of_mem hDS]
    omega
  obtain ⟨G, hGS⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_erase, Finset.mem_erase] at hGS
  have hGE : G ≠ E := hGS.1
  have hGD : G ≠ D := hGS.2.1
  have hGne : blockSpace A G.1 ≠ ⊥ := (mem_nonBotBlocks A p).mp hGS.2.2
  have h4 : ∀ H ∈ nonBotBlocks A p, 4 ≤ Module.finrank F ↥(blockSpace A H.1) := by
    intro H hH
    have hHne := (mem_nonBotBlocks A p).mp hH
    have hHpos := finrank_blockSpace_pos A hHne
    have hdvd := finrank_blockSpace_dvd_rk2Ord A hp hp2 hA t ht H hHne hn
    have hge3 : 3 ≤ Module.finrank F ↥(blockSpace A H.1) :=
      le_trans hm0 (Nat.le_of_dvd hHpos hdvd)
    have hev := even_finrank_blockSpace A (by
      have := CharP.cast_eq_zero F 2
      simpa using this) hQ hp hpF hA hB H
    obtain ⟨k, hk⟩ := hev
    omega
  have hdD4 := h4 D hDS
  have hdE4 := h4 E hES
  have hdG4 := h4 G hGS.2.2
  have hDEle : Module.finrank F ↥(blockSpace A D.1) ≤
      Module.finrank F ↥(blockSpace A E.1) := hDmin E hES
  have hsum3 := finrank_three_blockSpace_le A hp hpF hA hDE (Ne.symm hGD) (Ne.symm hGE)
  have hfixD := finrank_fixedSpace_blockEnd A hp hpF hA t ht D
  have hfixmul := le_finrank_fixedSpace_blockEnd_mul A hp hpF hA t ht (D := D) (E := E)
  refine ⟨D, E, hDS, hES, hDE, ?_, ?_⟩
  · rw [hfixD]; omega
  · omega

theorem exists_blocks_regimeII [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hpF : (p : F) ≠ 0) (hp2 : p ≠ 2)
    (hA : IsElemAbelian p A)
    (hB : ∀ a : ↥A, ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (ℓ : ℕ) (hdim : Module.finrank F V = 2 * ℓ) (h5 : 5 ≤ ℓ)
    (hr : ℓ - 1 ≤ (nonBotBlocks A p).card) :
    ∃ D E : Hyperplane A p, D ∈ nonBotBlocks A p ∧ E ∈ nonBotBlocks A p ∧ D ≠ E ∧
      Module.finrank F ↥(blockSpace A D.1) = 2 ∧
      Module.finrank F ↥(blockSpace A E.1) = 2 ∧
      8 ≤ Module.finrank F ↥(fixedSpace (blockEnd A hp hpF hA t ht D)) ∧
      6 ≤ Module.finrank F ↥(fixedSpace
        (blockEnd A hp hpF hA t ht D * blockEnd A hp hpF hA t ht E)) := by
  classical
  have h2 : 2 ≤ (nonBotBlocks A p).card := by omega
  obtain ⟨D, E, hDS, hES, hDE, hDmin, hEmin⟩ := exists_two_min_blocks A (p := p) h2
  have hDne : blockSpace A D.1 ≠ ⊥ := (mem_nonBotBlocks A p).mp hDS
  have hEne : blockSpace A E.1 ≠ ⊥ := (mem_nonBotBlocks A p).mp hES
  have h2le : ∀ H ∈ nonBotBlocks A p, 2 ≤ Module.finrank F ↥(blockSpace A H.1) := by
    intro H hH
    exact two_le_finrank_blockSpace A (by
      have := CharP.cast_eq_zero F 2
      simpa using this) hQ hp hpF hA hB H ((mem_nonBotBlocks A p).mp hH)
  have heven : ∀ H ∈ nonBotBlocks A p, Even (Module.finrank F ↥(blockSpace A H.1)) :=
    fun H _ => even_finrank_blockSpace A (by
      have := CharP.cast_eq_zero F 2
      simpa using this) hQ hp hpF hA hB H
  have hsum_univ : ∑ D : Hyperplane A p, Module.finrank F ↥(blockSpace A D.1) ≤
      Module.finrank F V := sum_finrank_blockSpace_le_finrank A hp hpF hA
  have hsumS : ∑ H ∈ nonBotBlocks A p, Module.finrank F ↥(blockSpace A H.1) =
      ∑ D : Hyperplane A p, Module.finrank F ↥(blockSpace A D.1) := by
    rw [Finset.sum_subset (Finset.subset_univ _)]
    intro x _ hx
    have hx' : blockSpace A x.1 = ⊥ := by
      by_contra h
      exact hx (by simp [nonBotBlocks, h])
    rw [hx', finrank_bot]
  have hdD : Module.finrank F ↥(blockSpace A D.1) = 2 := by
    by_contra hne
    have hpos := finrank_blockSpace_pos A hDne
    obtain ⟨k, hk⟩ := heven D hDS
    have h4 : 4 ≤ Module.finrank F ↥(blockSpace A D.1) := by omega
    have hlb : 4 * (nonBotBlocks A p).card ≤
        ∑ H ∈ nonBotBlocks A p, Module.finrank F ↥(blockSpace A H.1) :=
      mul_card_le_sum_blockSpace A (nonBotBlocks A p) 4 fun H hH => le_trans h4 (hDmin H hH)
    have hbound : 4 * (nonBotBlocks A p).card ≤ Module.finrank F V :=
      hlb.trans (hsumS.trans_le hsum_univ)
    rw [hdim] at hbound
    have := Nat.mul_le_mul_left 4 hr
    omega
  have hdE : Module.finrank F ↥(blockSpace A E.1) = 2 := by
    by_contra hne
    have hpos := finrank_blockSpace_pos A hEne
    obtain ⟨k, hk⟩ := heven E hES
    have h4 : 4 ≤ Module.finrank F ↥(blockSpace A E.1) := by omega
    have hlb : 2 + 4 * ((nonBotBlocks A p).card - 1) ≤
        ∑ H ∈ nonBotBlocks A p, Module.finrank F ↥(blockSpace A H.1) := by
      have hsplit := Finset.sum_erase_add (nonBotBlocks A p)
        (fun H => Module.finrank F ↥(blockSpace A H.1)) hDS
      have h4' : 4 * ((nonBotBlocks A p).erase D).card ≤
          ∑ H ∈ (nonBotBlocks A p).erase D,
            Module.finrank F ↥(blockSpace A H.1) := by
        refine mul_card_le_sum_blockSpace A ((nonBotBlocks A p).erase D) 4 fun H hH => ?_
        rw [Finset.mem_erase] at hH
        exact le_trans h4 (hEmin H hH.2 hH.1)
      have hcard : ((nonBotBlocks A p).erase D).card = (nonBotBlocks A p).card - 1 :=
        Finset.card_erase_of_mem hDS
      rw [hcard] at h4'
      have hD2 : 2 ≤ Module.finrank F ↥(blockSpace A D.1) := h2le D hDS
      omega
    have hbound : 2 + 4 * ((nonBotBlocks A p).card - 1) ≤ Module.finrank F V :=
      hlb.trans (hsumS.trans_le hsum_univ)
    rw [hdim] at hbound
    have := Nat.mul_le_mul_left 4 hr
    omega
  have hfixD := finrank_fixedSpace_blockEnd A hp hpF hA t ht D
  have hfixmul := le_finrank_fixedSpace_blockEnd_mul A hp hpF hA t ht (D := D) (E := E)
  refine ⟨D, E, hDS, hES, hDE, hdD, hdE, ?_, ?_⟩
  · rw [hfixD, hdim, hdD]; omega
  · omega

end Blocks

end OmEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
