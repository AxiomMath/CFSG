module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport
public import CFSG.LocalAnalysis.ComponentClassification.PComponentCentralizers

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

open CFSG CFSG.LocalCores

variable {G : Type*} [Group G]

theorem subgroupOf_isSubnormal_of_le {L C A : Subgroup G} (hCA : C ≤ A)
    (h : (L.subgroupOf A).IsSubnormal) : (L.subgroupOf C).IsSubnormal := by
  have h1 : ((L.subgroupOf A).subgroupOf (C.subgroupOf A)).IsSubnormal := h.subgroupOf
  have hcomap : L.subgroupOf C = ((L.subgroupOf A).subgroupOf (C.subgroupOf A)).comap
      (Subgroup.subgroupOfEquivOfLe hCA).symm.toMonoidHom := by
    ext x
    rfl
  rw [hcomap]
  exact h1.comap _

theorem subgroupOf_isSubnormal_iff {L C A : Subgroup G} (hLC : L ≤ C) (hCA : C ≤ A)
    (hC : (C.subgroupOf A).IsSubnormal) :
    (L.subgroupOf A).IsSubnormal ↔ (L.subgroupOf C).IsSubnormal := by
  refine ⟨subgroupOf_isSubnormal_of_le hCA, fun h => ?_⟩
  have hcomap : (L.subgroupOf A).subgroupOf (C.subgroupOf A) =
      (L.subgroupOf C).comap (Subgroup.subgroupOfEquivOfLe hCA).toMonoidHom := by
    ext x
    rfl
  have h1 : ((L.subgroupOf A).subgroupOf (C.subgroupOf A)).IsSubnormal := by
    rw [hcomap]
    exact h.comap _
  exact Subgroup.IsSubnormal.trans (fun x hx => hLC hx) h1 hC

theorem normalizer_le_normalizer_centralizer (V : Subgroup G) :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  have hfwd : ∀ g ∈ Subgroup.normalizer (V : Set G), ∀ c ∈ Subgroup.centralizer (V : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hw : g⁻¹ * v * g⁻¹⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) v).1 hv
    have hwc := Subgroup.mem_centralizer_iff.1 hc _ hw
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g⁻¹⁻¹)) * g⁻¹ := by rw [hwc]
      _ = g * c * g⁻¹ * v := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨hfwd g hg c, fun hc => ?_⟩
  have h := hfwd g⁻¹ (inv_mem hg) _ hc
  have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rwa [e] at h

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem pComponent_subgroupOf_iff_of_subnormal {L C A : Subgroup G} (hLC : L ≤ C) (hCA : C ≤ A)
    (hC : (C.subgroupOf A).IsSubnormal) :
    IsPComponent p (L.subgroupOf A) ↔ IsPComponent p (L.subgroupOf C) := by
  rw [pComponent_subgroupOf_iff p L A (hLC.trans hCA), pComponent_subgroupOf_iff p L C hLC,
    subgroupOf_isSubnormal_iff hLC hCA hC]

theorem pComponent_subgroupOf_of_le {L C A : Subgroup G} (hLC : L ≤ C) (hCA : C ≤ A)
    (h : IsPComponent p (L.subgroupOf A)) : IsPComponent p (L.subgroupOf C) := by
  rw [pComponent_subgroupOf_iff p L A (hLC.trans hCA)] at h
  rw [pComponent_subgroupOf_iff p L C hLC]
  exact ⟨subgroupOf_isSubnormal_of_le hCA h.1, h.2⟩

omit [Finite G] in
theorem badTwo_map_le_of_forall {Y W : Subgroup G}
    (h : ∀ L : Subgroup G, L ≤ Y → IsPComponent 2 (L.subgroupOf Y) →
      L ≤ W ∧ IsPComponent 2 (L.subgroupOf W)) :
    (badTwoComponentSubgroup Y).map Y.subtype ≤ (badTwoComponentSubgroup W).map W.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun X hX => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hXeq : (X.map Y.subtype).subgroupOf Y = X :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective X
  obtain ⟨hLW, hW⟩ := h (X.map Y.subtype) (Subgroup.map_subtype_le X) (by rw [hXeq]; exact hX.1)
  have hnq : ¬ IsQuasisimple ((X.map Y.subtype).subgroupOf W) := fun hq => hX.2
    (isQuasisimple_of_mulEquiv (((Subgroup.subgroupOfEquivOfLe hLW).trans
      (X.equivMapOfInjective Y.subtype Y.subtype_injective).symm)) hq)
  have hle : (X.map Y.subtype).subgroupOf W ≤ badTwoComponentSubgroup W := le_sSup ⟨hW, hnq⟩
  have hmap := Subgroup.map_mono (f := W.subtype) hle
  rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hLW] at hmap

omit [Finite G] in
theorem badTwo_map_le_top_of_forall {Y : Subgroup G}
    (h : ∀ L : Subgroup G, L ≤ Y → IsPComponent 2 (L.subgroupOf Y) → IsPComponent 2 L) :
    (badTwoComponentSubgroup Y).map Y.subtype ≤ badTwoComponentSubgroup G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun X hX => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hXeq : (X.map Y.subtype).subgroupOf Y = X :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective X
  have hL := h (X.map Y.subtype) (Subgroup.map_subtype_le X) (by rw [hXeq]; exact hX.1)
  have hnq : ¬ IsQuasisimple (X.map Y.subtype) := fun hq => hX.2
    (isQuasisimple_of_mulEquiv (X.equivMapOfInjective Y.subtype Y.subtype_injective).symm hq)
  exact le_sSup ⟨hL, hnq⟩

theorem pComponent_iff_centralizer_of_le_normalizer {V A : Subgroup G} (hVp : IsPGroup p V)
    (hVA : V ≤ A) (hAN : A ≤ Subgroup.normalizer (V : Set G))
    (hCA : Subgroup.centralizer (V : Set G) ≤ A) (L : Subgroup G) :
    (L ≤ A ∧ IsPComponent p (L.subgroupOf A)) ↔
      (L ≤ Subgroup.centralizer (V : Set G) ∧
        IsPComponent p (L.subgroupOf (Subgroup.centralizer (V : Set G)))) := by
  have hCn : ((Subgroup.centralizer (V : Set G)).subgroupOf A).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hCA).2
      (hAN.trans (normalizer_le_normalizer_centralizer V))).isSubnormal
  constructor
  · rintro ⟨hLA, hL⟩
    have hVAn : (V.subgroupOf A).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVA).2 hAN
    have hVAp : IsPGroup p (V.subgroupOf A) := hVp.comap_of_injective _ A.subtype_injective
    have hcomm := p_component_normal_p_centralizer hL hVAn hVAp
    have hLC : L ≤ Subgroup.centralizer (V : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
        (show (⟨l, hLA hl⟩ : A) ∈ L.subgroupOf A from hl)
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 h1 ⟨v, hVA hv⟩ hv)
    exact ⟨hLC, (pComponent_subgroupOf_iff_of_subnormal hLC hCA hCn).1 hL⟩
  · rintro ⟨hLC, hL⟩
    exact ⟨hLC.trans hCA, (pComponent_subgroupOf_iff_of_subnormal hLC hCA hCn).2 hL⟩

theorem central_p_enlargement_normalizer_components {S Z : Subgroup G} (hS : IsPGroup p S)
    (hZ : Z ≤ Subgroup.center G) (hZp : IsPGroup p Z) (L : Subgroup G) :
    (L ≤ Subgroup.normalizer (S : Set G) ∧
        IsPComponent p (L.subgroupOf (Subgroup.normalizer (S : Set G)))) ↔
      (L ≤ Subgroup.normalizer ((S ⊔ Z : Subgroup G) : Set G) ∧
        IsPComponent p (L.subgroupOf (Subgroup.normalizer ((S ⊔ Z : Subgroup G) : Set G)))) := by
  have hZn : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.1 (hZ hz) g, mul_inv_cancel_right]
    exact hz⟩
  have hVp : IsPGroup p (S ⊔ Z : Subgroup G) := hS.to_sup_of_normal_right hZp
  have hconj : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ v ∈ (S ⊔ Z : Subgroup G),
      g * v * g⁻¹ ∈ (S ⊔ Z : Subgroup G) := by
    intro g hg v hv
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hv
    obtain ⟨s, hs, z, hz, rfl⟩ := hv
    have hgs : g * s * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hg s).1 hs
    have hgz : g * z * g⁻¹ = z := by
      rw [Subgroup.mem_center_iff.1 (hZ hz) g, mul_inv_cancel_right]
    have e : g * (s * z) * g⁻¹ = (g * s * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e, hgz]
    exact mul_mem (Subgroup.mem_sup_left hgs) (Subgroup.mem_sup_right hz)
  have hHJ : Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((S ⊔ Z : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨hconj g hg v, fun hv => ?_⟩
    have h := hconj g⁻¹ (inv_mem hg) _ hv
    have e : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
    rwa [e] at h
  have hVH : (S ⊔ Z : Subgroup G) ≤ Subgroup.normalizer (S : Set G) := by
    refine sup_le Subgroup.le_normalizer fun z hz => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [← Subgroup.mem_center_iff.1 (hZ hz) s, mul_inv_cancel_right]
  have hCH : Subgroup.centralizer ((S ⊔ Z : Subgroup G) : Set G) ≤
      Subgroup.normalizer (S : Set G) :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  rw [pComponent_iff_centralizer_of_le_normalizer hVp hVH hHJ hCH L,
    pComponent_iff_centralizer_of_le_normalizer hVp Subgroup.le_normalizer le_rfl
      (Subgroup.centralizer_le_normalizer _) L]

theorem central_two_enlargement_normalizer_badTwo {S Z : Subgroup G} (hS : IsPGroup 2 S)
    (hZ : Z ≤ Subgroup.center G) (hZp : IsPGroup 2 Z) :
    (badTwoComponentSubgroup (Subgroup.normalizer (S : Set G))).map
        (Subgroup.normalizer (S : Set G)).subtype =
      (badTwoComponentSubgroup (Subgroup.normalizer ((S ⊔ Z : Subgroup G) : Set G))).map
        (Subgroup.normalizer ((S ⊔ Z : Subgroup G) : Set G)).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (badTwo_map_le_of_forall fun L hL hLc => ?_)
    (badTwo_map_le_of_forall fun L hL hLc => ?_)
  · exact (central_p_enlargement_normalizer_components hS hZ hZp L).1 ⟨hL, hLc⟩
  · exact (central_p_enlargement_normalizer_components hS hZ hZp L).2 ⟨hL, hLc⟩

end CFSG.ComponentClassification.CatalogueBPrimeJoin
