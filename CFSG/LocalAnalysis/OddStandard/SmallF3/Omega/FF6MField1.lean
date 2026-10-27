module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFieldAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem ff6m_layer_trivial :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (layerCent L s = ⊥ ↔
        InducesTypeSome L s 6 (-1) 4 1 ∨ ∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α) := by
  intro G _ _ L hL s hs2 hsn
  constructor
  · intro hl
    obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx2⟩ := ff6m_model_data hL hs2 hsn
    rcases ff6m_model_classify hQ hdim hsgn hx2 with h1 | h0 | hn1 | h2 | h3 | hn2 | h4
    · exact absurd hl (ff6m_central_layer hL
        ((ff6m_centralizer_iff_eq_one hL.1 hQ (by omega) e hs).mpr h1)).1
    · exact Or.inl ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, x, hdim, hsgn,
        hs, h0⟩
    · exact absurd hl (ff_isL29_ne_bot
        (ff6m_shape_L29 hL hdim hs hs2 (ff6m_N1_layerModel hQ hdim hsgn hn1)).1)
    · exact absurd hl (ff_isOmega5_ne_bot
        (ff6m_shape_Omega5 hL hdim hs hs2 (ff6m_K2_layerModel hQ hdim hsgn h2)).1)
    · obtain ⟨α, hα⟩ := h3
      exact Or.inr ⟨α, V, inferInstance, inferInstance, inferInstance, Q, hQ, e, x, hdim,
        hsgn, hs, hα⟩
    · exact absurd hl (ff_isU33_ne_bot
        (ff6m_shape_U33 hL hdim hs hs2 (ff6m_N2_layerModel hQ hdim hsgn hn2)).1)
    · exact absurd hl (ff_isL29_ne_bot
        (ff6m_shape_L29 hL hdim hs hs2 (ff6m_K4_layerModel hQ hdim hsgn hx2 h4)).1)
  · rintro (⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩ |
      ⟨α, V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩)
    · exact ff6m_bot_of_solvable hL hdim hs hs2 (ff6m_K0_solvable hQ hdim hsgn hx)
    · exact ff6m_bot_of_solvable hL hdim hs hs2 (ff6m_K3_solvable hQ hdim hsgn ⟨α, hx⟩)

theorem ff6m_layer_i4m :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      InducesTypeSome L s 6 (-1) 4 (-1) → IsL29 (layerCent L s) := by
  rintro G _ _ L hL s hs2 hsn ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩
  exact (ff6m_shape_L29 hL hdim hs hs2 (ff6m_N1_layerModel hQ hdim hsgn hx)).1

theorem ff6m_layer_rho :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      InducesProjective L 6 (-1) s → IsU33 (layerCent L s) := by
  rintro G _ _ L hL s hs2 hsn ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩
  exact (ff6m_shape_U33 hL hdim hs hs2 (ff6m_N2_layerModel hQ hdim hsgn hx)).1

theorem ff6m_layer_i1 :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 1 α) → IsOmega5 (layerCent L s) := by
  rintro G _ _ L hL s hs2 hsn ⟨α, V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩
  exact (ff6m_shape_Omega5 hL hdim hs hs2
    (ff6m_K2_layerModel hQ hdim hsgn ⟨α, hx⟩)).1

theorem ff6m_layer_gamma :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      InducesOutsideGStar L 6 (-1) s → IsL29 (layerCent L s) := by
  rintro G _ _ L hL s hs2 hsn ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx2, hx⟩
  exact (ff6m_shape_L29 hL hdim hs hs2 (ff6m_K4_layerModel hQ hdim hsgn hx2 hx)).1

theorem ff6m_xout_eq :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → layerCent L s ≠ ⊥ →
      XOut L s = layerCent L s := by
  intro G _ _ L hL s hs2 hsn hne
  obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx2⟩ := ff6m_model_data hL hs2 hsn
  rcases ff6m_model_classify hQ hdim hsgn hx2 with h1 | h0 | hn1 | h2 | h3 | hn2 | h4
  · exact (ff6m_central_layer hL
      ((ff6m_centralizer_iff_eq_one hL.1 hQ (by omega) e hs).mpr h1)).2
  · exact absurd (ff6m_bot_of_solvable hL hdim hs hs2 (ff6m_K0_solvable hQ hdim hsgn h0)) hne
  · exact (ff6m_shape_L29 hL hdim hs hs2 (ff6m_N1_layerModel hQ hdim hsgn hn1)).2
  · exact (ff6m_shape_Omega5 hL hdim hs hs2 (ff6m_K2_layerModel hQ hdim hsgn h2)).2
  · exact absurd (ff6m_bot_of_solvable hL hdim hs hs2 (ff6m_K3_solvable hQ hdim hsgn h3)) hne
  · exact (ff6m_shape_U33 hL hdim hs hs2 (ff6m_N2_layerModel hQ hdim hsgn hn2)).2
  · exact (ff6m_shape_L29 hL hdim hs hs2 (ff6m_K4_layerModel hQ hdim hsgn hx2 h4)).2

theorem ff6m_xout_i3 :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α) →
        XOut L s = CFSG.inSubgroup (CFSG.pCore 2) (twoRes (L ⊓ centralizer ({s} : Set G))) := by
  rintro G _ _ L hL s hs2 hsn ⟨α, V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩
  exact ff6m_xTwoCore_of hL hdim hs hs2 (ff6m_K3_xTwoCore hQ hdim hsgn ⟨α, hx⟩)

end CFSG.OddStandard.SmallF3.Omega
