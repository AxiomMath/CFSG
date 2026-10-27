module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Lemma126

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem prop123 (h : Cfg12 G m p B x L D K) (hin : Inputs123 G p) :
    ∃ (y : G) (J : Subgroup G), GLASHat p B y J ∧ GLANeighbor p x y J D K := by
  by_contra hne
  have hnn : NoNbr12 p B x L D K := fun y J hyJ => hne ⟨y, J, hyJ⟩
  have hT126 := lemma126 h hin hnn
  obtain ⟨D₁, K₁, KE, hstd₁, hE3, hKE, hT172, hnot126⟩ :=
    hin.i172 p B x L D K h.prime h.odd h.tri.star h.pow_four_le (h.tri.qs h.ctx) (h.tri.chev2 h.ctx)
      h.tri.split h.std (lemma121 h hin.l122.l121) hT126
  have h₁ : Cfg12 G m p B x L D₁ K₁ := ⟨h.ctx, h.tri, hstd₁⟩
  have hex : ∃ (y : G) (J : Subgroup G), GLASHat p B y J ∧ GLANeighbor p x y J D₁ K₁ := by
    by_contra hne₁
    have hnn₁ : NoNbr12 p B x L D₁ K₁ := fun y J hyJ => hne₁ ⟨y, J, hyJ⟩
    exact hnot126 _ (lemma126 h₁ hin hnn₁)
  obtain ⟨y, L₁, hS, hN⟩ := hex
  have hnb : NbrCfg G m p B x L D₁ K₁ y L₁ := ⟨h₁, hS, hN⟩
  have hc122 := prop122 hnb hin.l122
  have hKy := ky_pcomp_cent h₁ hin.l122.l121.common hnb.y_mem_D hnb.y_not_mem
  rw [ky_eq_J hnb hin.l122] at hKy
  obtain ⟨x', hx'D, hx'x, hx'⟩ := hin.compl B x L D K D₁ K₁ KE L₁ y h.tri.star h.pow_four_le h.tri.split h.std hE3 hKE
    hT172 hstd₁ hS hN hKy hc122
  obtain ⟨𝒞, hC1, hC2, -, -⟩ := ky_family h hin.l122.l121.common hx'D hx'x
  have hKne : K ≠ ⊥ := glaPComponent_ne_bot' (std_pcomp' h hin.l122.l121.common)
  obtain ⟨M, hM𝒞⟩ : 𝒞.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    subst hemp
    have h1 : K ≤ Ky p K x' := le_closureIn_self K _
    rw [← hC2] at h1
    simp at h1
    exact hKne h1
  have hMK : M ≤ Ky p K x' := by
    rw [← hC2]
    exact le_biSup (fun M' => M') hM𝒞
  obtain ⟨hS', hN'⟩ := nbr_of_not_centMod h hin.l122.l121.common hx'D hx'x (hC1 M hM𝒞) hMK (hx' M (hC1 M hM𝒞) hMK)
  exact hne ⟨x', M, hS', hN'⟩

end S12

end CFSG.LocalAnalysis.GLTheoremA
