module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5K1Data
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5K1E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5K1Desc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5LayerQS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverActConv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5DescKind
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5KindCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Tab5_layer_i4m_of (hS : Asc82SchurU43) (hM : Asc82Tab6M) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → Kind5 L s 1 →
        IsComponentIn (layerCent L s) (L ⊓ centralizer ({s} : Set G)) ∧ IsL29 (layerCent L s)
  := by
  intro G _ _ L hL s hs2 hs hk
  obtain ⟨t, ht, ht2⟩ := t5_exists_central_involution hL
  have hnc : s ∉ centralizer (L : Set G) :=
    asc82Tab5_kind_ne_central_of G L hL s hs2 hs (Or.inl hk)
  have hk' : KindM (DescL L t) (descElt L t s hs) 1 :=
    (t5_desc_kind_iff hM hL ht ht2 hs hs2 hnc (k := 1) (by norm_num)).mp hk
  have hs' : descElt L t s hs ∈ normalizer (DescL L t : Set (DescG L t)) :=
    t5_desc_mem_normalizer L t hs
  have hs2' : orderOf (descElt L t s hs) = 2 :=
    t5_desc_orderOf hL ht ht2 hs hs2 hnc
  have h29t : IsL29 (layerCent (DescL L t) (descElt L t s hs)) :=
    hM.layer_i4m (DescG L t) (DescL L t) (t5_isOm6M_descL hL ht ht2) (descElt L t s hs)
      hs2' hs' (show InducesTypeSome (DescL L t) (descElt L t s hs) 6 (-1) 4 (-1) from hk')
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, τ, hφ, hτ, hty, hact⟩ := t5_k1_data hS hL hk
  have htE : t ∉ layerCent L s := t5_k1_not_mem hL hφ hty hact ht ht2
  have h29 : IsL29 (layerCent L s) := t5_isL29_layerCent_of_desc hL ht ht2 hs htE h29t
  exact ⟨t5_isComponentIn_layer_of_isL29 (L ⊓ centralizer ({s} : Set G)) h29, h29⟩

theorem asc82Tab5_i4m_inv_of (hS : Asc82SchurU43) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → Kind5 L s 1 →
        ∀ u ∈ layerCent L s, orderOf u = 2 → ¬ IsI4PlusIn L u ∧ u ∉ centerIn L
  := by
  intro G _ _ L hL s hs2 hs hk u hu hu2
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, τ, hφ, hτ, hty, hact⟩ := t5_k1_data hS hL hk
  have hL_hC := Subgroup.mem_inf.mp (t5_layerCent_le_inf L s hu)
  have huL : u ∈ L := hL_hC.1
  obtain ⟨hvv, hv1, hvty⟩ := t5_k1_layer_type hL hφ hτ hty hact hu hu2 huL
  constructor
  · intro hP
    have hP' : IsI4PlusIn (⊤ : Subgroup ↥(omegaGroup hQ)) (φ ⟨u, huL⟩) :=
      (t5_isI4PlusIn_iff hL hφ huL hu2).mp hP
    have h4 : invType ((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) = (4, 1) :=
      (t5_isI4PlusIn_omega_iff hφ.finrank_eq hφ.quadSign_eq hvv hv1).mp hP'
    rw [hvty] at h4
    exact absurd h4 (by decide)
  · intro hcen
    have hpi : ((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) = piOrth Q :=
      hφ.map_central hL hcen hu2 huL
    have h6 : invType ((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) = (6, -1) := by
      rw [hpi, invType_piOrth hQ, hφ.finrank_eq, hφ.quadSign_eq]
    rw [hvty] at h6
    exact absurd h6 (by decide)

theorem asc82Tab5_prod_i4m_of (hS : Asc82SchurU43) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → Kind5 L s 1 →
        ∀ u ∈ layerCent L s, orderOf u = 2 → Kind5 L (s * u) 1
  := by
  intro G _ _ L hL s hs2 hs hk u hu hu2
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, τ, hφ, hτ, hty, hact⟩ := t5_k1_data hS hL hk
  have hL_hC := Subgroup.mem_inf.mp (t5_layerCent_le_inf L s hu)
  have huL : u ∈ L := hL_hC.1
  have hus : s * u = u * s :=
    (Subgroup.mem_centralizer_iff.mp hL_hC.2) s (Set.mem_singleton s)
  obtain ⟨hvv, hv1, hvty⟩ := t5_k1_layer_type hL hφ hτ hty hact hu hu2 huL
  have hcomm : τ * ((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) =
      ((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) * τ :=
    t5_k1_comm hact huL hus
  have hfix : fixSp τ ≤ fixSp ((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) :=
    t5_k1_layer_fix hφ hty hact hu huL
  have hHas : HasType (toProj Q
      (((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) * τ)) 4 (-1) :=
    t5_k1_hasType_prod hQ hφ.finrank_eq hφ.quadSign_eq hτ hty hvv hcomm hfix hvty
  have hact' : CoverAct L φ (s * u)
      (orthToSim Q (((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) * τ)) := by
    rw [hus]
    exact t5_coverAct_mul_left hact huL
  obtain ⟨e, he⟩ := t5_exists_model hL hφ
  have hind := t5_inducesViaP_of_coverAct he hact'
  exact ⟨V, i1, i2, i3, Q, hQ, e,
    QuotientGroup.mk (orthToSim Q (((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) * τ)),
    hφ.finrank_eq, hφ.quadSign_eq, hind,
    toProj Q (((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) * τ),
    projOrthToProjSim_toProj (((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) * τ), hHas⟩

end CFSG.OddStandard.SmallF3.Omega
