module

public import CFSG.GH74.Generic.BProg.B3.Thm9S45
public import CFSG.GH74.Generic.BProg.B3.Lemma212S45
public import CFSG.GH74.Generic.BProg.B3.FalseCtxS45Comp

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1Lemma282Aux

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification Subgroup

variable {G : Type} [Group G] [Finite G]

theorem pLayerOf_le_normalizer {a : G} {J : Subgroup G}
    (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J) :
    pLayerOf 2 (centralizer ({a} : Set G)) ≤ normalizer (J : Set G) := by
  refine sSup_le fun L hL => ?_
  by_cases hLJ : J = L
  · rw [← hLJ]
    exact Subgroup.le_normalizer
  · exact fun c hc => (FalseCtxS45Comp.le_cSec_of_ne hJ hL hLJ hc).1

theorem pumpUp_isPCompIn {x a : G} {K H : Subgroup G} (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hxa : a ∈ centralizer ({x} : Set G))
    (hH : IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) H)
    (hxL : x ∈ pLayerOf 2 (centralizer ({a} : Set G))) :
    IsPCompIn 2 (centralizer ({a} : Set G)) (pumpUp 2 H a) ∧ H ≤ pumpUp 2 H a ∧
      x ∈ normalizer ((pumpUp 2 H a : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxy : x ∈ centralizer ({a} : Set G) := TwoThin.mem_centralizer_symm hxa
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  set W : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({a} : Set G) with hW
  have hHX := TwoThin.isPCompIn_two_iff.mp hH
  have hsub : ((K ⊓ centralizer ({a} : Set G)).subgroupOf W).IsSubnormal :=
    B1.isSubnormal_subgroupOf_inf (S := centralizer ({a} : Set G)) (B1.isSubnormal_of_isPCompIn hK)
  have hHU : IsPCompIn 2 W H :=
    B1.isPCompIn_of_isSubnormal 2 (inf_le_inf_right _ hK.1) hsub hH
  have hHy : H ≤ centralizer ({a} : Set G) := hHX.1.trans inf_le_right
  set Yc : Subgroup G := centralizer ({a} : Set G) with hYc
  have hs : orderOf (⟨x, hxy⟩ : ↥Yc) = 2 := TwoThin.orderOf_mk_centralizer hxy hx
  have hΛC := TwoThin.le_centralizer_mk hHU.1 hxy
  have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hHU hxy
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hK'⟩ := TwoThin.pumpupY_structure hs hΛC hΛ2
  have hJeq : pumpUp 2 H a = (TwoThin.pumpupY (H.subgroupOf Yc)).map Yc.subtype := by
    rw [TwoThin.pumpUp_eq_map_pumpupY, inf_eq_left.2 hHy, Lemma212S45.pLayerOf_self hH]
  have hsE : (⟨x, hxy⟩ : ↥Yc) ∈ TwoLayer.subgroup ↥Yc := by
    have h1 := hxL
    rw [TwoThin.pLayerOf_two_eq_map] at h1
    obtain ⟨y', hy', hyy⟩ := h1
    have : y' = ⟨x, hxy⟩ := Subtype.ext hyy
    rwa [this] at hy'
  have hnormL : TwoThin.barMk ↥Yc ⟨x, hxy⟩ ∈ Subgroup.normalizer (L : Set (TwoThin.barQ ↥Yc)) := by
    have hg1 : TwoThin.barMk ↥Yc ⟨x, hxy⟩ ∈ CFSG.layer (TwoThin.barQ ↥Yc) :=
      TwoThin.map_twoLayer_le_layer ⟨_, hsE, rfl⟩
    have hg2 : TwoThin.barMk ↥Yc ⟨x, hxy⟩ ∈ Layer.subgroup (TwoThin.barQ ↥Yc) := by
      rwa [TwoThin.layer_subgroup_eq_layer]
    exact ClassicalInvolution.layer_le_normalizer_of_isComponentOf
      ((CFSG.isComponent_iff_open L).mp hL) hg2
  have hLinv : conjSub (TwoThin.barMk ↥Yc ⟨x, hxy⟩)⁻¹ L = L := by
    ext y
    rw [TwoThin.mem_conjSub_iff', inv_inv]
    exact (Subgroup.mem_normalizer_iff.1 hnormL y).symm
  refine ⟨?_, ?_, ?_⟩
  · rcases hcases with ⟨-, hΛL⟩ | ⟨hne, -, -⟩
    · have hJ2 := Thm9S45.pumpupY_isTwoComponent_of_vertical hΛC hΛ2 hJsub hL hΛL hLJ
      rw [hJeq]
      refine TwoThin.isPCompIn_two_iff.mpr ⟨Subgroup.map_subtype_le _, ?_⟩
      have hcm : ((TwoThin.pumpupY (H.subgroupOf Yc)).map Yc.subtype).subgroupOf Yc =
          TwoThin.pumpupY (H.subgroupOf Yc) :=
        Subgroup.comap_map_eq_self_of_injective Yc.subtype_injective _
      rw [hcm]
      exact hJ2
    · exact absurd hLinv hne
  · rw [hJeq]
    intro h hh
    exact ⟨⟨h, hHy hh⟩, TwoThin.subset_pumpupY _ (Subgroup.mem_subgroupOf.2 hh), rfl⟩
  ·
    have h1 := TwoThin.map_conj_pumpupY_le_of_le_centralizer (H.subgroupOf Yc) hΛC
    have hfwd : ∀ j ∈ pumpUp 2 H a, x * j * x⁻¹ ∈ pumpUp 2 H a := by
      intro j hj
      rw [hJeq] at hj ⊢
      obtain ⟨j', hj', rfl⟩ := hj
      have h2 := h1 ⟨j', hj', rfl⟩
      exact ⟨_, h2, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro j
    constructor
    · exact hfwd j
    · intro hj
      have := hfwd _ hj
      have e : x * (x * j * x⁻¹) * x⁻¹ = j := by
        have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
        rw [hxinv]
        calc x * (x * j * x) * x = (x * x) * j * (x * x) := by group
          _ = j := by rw [hx2]; group
      rwa [e] at this

theorem mem_normalizer_pumpUp {a c : G} {H : Subgroup G} (hHY : H ≤ centralizer ({a} : Set G))
    (hHself : pLayerOf 2 H = H) (hcY : c ∈ centralizer ({a} : Set G))
    (hcH : c ∈ normalizer (H : Set G)) :
    c ∈ normalizer ((pumpUp 2 H a : Subgroup G) : Set G) := by
  classical
  set Yc : Subgroup G := centralizer ({a} : Set G) with hYc
  have hJeq : pumpUp 2 H a = (TwoThin.pumpupY (H.subgroupOf Yc)).map Yc.subtype := by
    rw [TwoThin.pumpUp_eq_map_pumpupY, inf_eq_left.2 hHY, hHself]
  have key : ∀ c : G, c ∈ Yc → c ∈ normalizer (H : Set G) →
      ∀ j ∈ pumpUp 2 H a, c * j * c⁻¹ ∈ pumpUp 2 H a := by
    intro c hcY hcH j hj
    have hΛ : ∀ y ∈ H.subgroupOf Yc,
        (⟨c, hcY⟩ : ↥Yc) * y * (⟨c, hcY⟩ : ↥Yc)⁻¹ ∈ H.subgroupOf Yc := by
      intro y hy
      show c * (y : G) * c⁻¹ ∈ H
      exact (Subgroup.mem_normalizer_iff.1 hcH _).1 (Subgroup.mem_subgroupOf.1 hy)
    have h1 := TwoThin.map_conj_pumpupY_le_of_map_le (H.subgroupOf Yc) (s := ⟨c, hcY⟩) hΛ
    rw [hJeq] at hj ⊢
    obtain ⟨j', hj', rfl⟩ := hj
    exact ⟨_, h1 ⟨j', hj', rfl⟩, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro j
  constructor
  · exact key c hcY hcH j
  · intro hj
    have h2 := key c⁻¹ (inv_mem hcY) (inv_mem hcH) _ hj
    simpa [mul_assoc] using h2

end S1Lemma282Aux

end CFSG.GH74.Generic.BProg.B3
