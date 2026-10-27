module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011S5Bar
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011S5Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6.L2012 CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound

section Final

theorem l2011S5 (h31a : IVK.IVK_3_1a) (h31c : IVK.IVK_3_1c) (h31g : IVK.Proofs2.IVK_3_1g_fixed) :
    L2011S5 := by
  intro G _ _ z k S hctx hT t ht1 ht2 c hc
  have hSC : S ≤ Cen z := hctx.S_le_Cen
  obtain ⟨htS, htC, hKn⟩ := bar_mem_S1_iff.1 ht1
  obtain ⟨q, L₁, L₂, hP, hdiag⟩ : ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)),
      Stage1Pair G z S q L₁ L₂ ∧
      ∀ u : G, ∀ hu : u ∈ Cen z, u ∈ S → orderOf u = 2 →
        toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) →
        toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z)) → u ∉ LC z →
          PGLOver L₁ (zpowers (toBar z ⟨u, hu⟩)) q ∧ PGLOver L₂ (zpowers (toBar z ⟨u, hu⟩)) q := by
    rcases hT with ⟨ε, q, hk, L₁, L₂, h4⟩ | ⟨q, hk, L₁, L₂, hps⟩
    · exact ⟨q, L₁, L₂, h4.pair, pgl_pair_of_l4 hSC h4⟩
    · exact ⟨q, L₁, L₂, hps.pair, pgl_pair_of_psp4 hSC hps⟩
  have hL₁le : L₁ ≤ LBar z := hP.prod.1 ▸ le_sup_left
  have htN : toBar z ⟨t, htC⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)) :=
    hKn L₁ (isComponent_L₁ hP) hL₁le
  obtain ⟨l, hl, σ, hσ, d, hd, hcd⟩ :=
    frattini_bar h31a h31c h31g hctx hP hdiag htS htC ht2 htN (toBar z ⟨c, hc⟩)
  obtain ⟨l', hl'C, hl'L, hl'⟩ : ∃ l' : G, ∃ hl'C : l' ∈ Cen z, l' ∈ LC z ∧ toBar z ⟨l', hl'C⟩ = l := by
    have : l ∈ LBar z := hP.prod.1 ▸ hl
    obtain ⟨x, hx, hxL, hxl⟩ := bar_mem_barOf_iff.1 this
    exact ⟨x, hx, hxL, hxl⟩
  obtain ⟨σ', hσ'C, hσ'S, hσ'⟩ := bar_mem_barOf_iff.1 hσ
  have hd' : d ∈ barIn (Cen z) (Cen t) := by
    rw [← P34.centralizer_mk_eq (Cen z) ht2 htC]
    exact hd
  obtain ⟨d', hd'mem, hd'⟩ := Subgroup.mem_map.1 hd'
  have hd'C : (d' : G) ∈ Cen t := Subgroup.mem_subgroupOf.1 hd'mem
  have hxC : l' * σ' * (d' : G) ∈ Cen z :=
    (Cen z).mul_mem ((Cen z).mul_mem hl'C hσ'C) d'.2
  have himg : toBar z ⟨c, hc⟩ = toBar z ⟨l' * σ' * (d' : G), hxC⟩ := by
    have : (⟨l' * σ' * (d' : G), hxC⟩ : ↥(Cen z)) = ⟨l', hl'C⟩ * ⟨σ', hσ'C⟩ * d' := rfl
    have hd'' : toBar z d' = d := hd'
    rw [this, map_mul, map_mul, hl', hσ', hd'', hcd]
  have hA : (⟨c, hc⟩ : ↥(Cen z)) / ⟨l' * σ' * (d' : G), hxC⟩ ∈ pPrimeCore 2 ↥(Cen z) :=
    (QuotientGroup.eq_iff_div_mem).1 himg
  refine ⟨c * (l' * σ' * (d' : G))⁻¹, ⟨_, hA, by simp [div_eq_mul_inv]⟩, l', hl'L, σ', hσ'S, d',
    Subgroup.mem_inf.2 ⟨d'.2, hd'C⟩, ?_⟩
  group

end Final

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
