module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Transport

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.EvenSporadicStandard.RuStd

variable {X Y : Type} [Group X] [Group Y]

theorem RuTwoBFacts.of_mulEquiv (e : X ≃* Y) (h : RuTwoBFacts X) : RuTwoBFacts Y where
  elt5 v hv hc := by
    obtain ⟨u, rfl⟩ := e.surjective v
    rw [card_centralizer_equiv] at hc
    rw [MulEquiv.orderOf_eq] at hv
    obtain ⟨f, hf, hf5⟩ := h.elt5 u hv hc
    refine ⟨e f, ?_, by rw [MulEquiv.orderOf_eq]; exact hf5⟩
    rw [derivedCentralizer_map]
    exact ⟨f, hf, rfl⟩
  centralInv v hv hc := by
    obtain ⟨u, rfl⟩ := e.surjective v
    rw [card_centralizer_equiv] at hc
    rw [MulEquiv.orderOf_eq] at hv
    obtain ⟨u', hu', hne, hcomm⟩ := h.centralInv u hv hc
    refine ⟨e u', by rwa [MulEquiv.orderOf_eq], fun h' => hne (e.injective h'), ?_⟩
    intro x hx
    rw [centralizer_singleton_map] at hx
    obtain ⟨x0, hx0, rfl⟩ := hx
    change e x0 * e u' = e u' * e x0
    rw [← map_mul, ← map_mul, hcomm x0 hx0]

theorem RuFiveFacts.of_mulEquiv (e : X ≃* Y) (h : RuFiveFacts X) : RuFiveFacts Y where
  exp5 g hg := by
    obtain ⟨x, rfl⟩ := e.surjective g
    have hx : IsPGroup 5 (zpowers x) := by
      have := hg.map e.symm.toMonoidHom
      rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at this
    rw [← map_pow, h.exp5 x hx, map_one]
  typeAB f hf := by
    obtain ⟨x, rfl⟩ := e.surjective f
    rw [MulEquiv.orderOf_eq] at hf
    have hk : HasKlein ((centralizer ({e x} : Set Y) : Subgroup Y) : Set Y) ↔
        HasKlein ((centralizer ({x} : Set X) : Subgroup X) : Set X) := by
      rw [centralizer_singleton_map, Subgroup.coe_map]
      exact hasKlein_image_iff e _
    rw [card_centralizer_equiv, hk]
    exact h.typeAB x hf
  typeA f hf hc := by
    obtain ⟨x, rfl⟩ := e.surjective f
    rw [MulEquiv.orderOf_eq] at hf
    rw [card_centralizer_equiv] at hc
    obtain ⟨D, ⟨eD⟩, hD, hC, hdisj⟩ := h.typeA x hf hc
    have hz : zpowers (e x) = (zpowers x).map e.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      rfl
    refine ⟨D.map e.toMonoidHom,
      ⟨(Subgroup.equivMapOfInjective D e.toMonoidHom e.injective).symm.trans eD⟩, ?_, ?_, ?_⟩
    · rw [centralizer_singleton_map]
      exact Subgroup.map_mono hD
    · rw [centralizer_singleton_map, hC, Subgroup.map_sup, hz]
    · rw [disjoint_iff, hz, ← Subgroup.map_inf _ _ _ e.injective, disjoint_iff.1 hdisj,
        Subgroup.map_bot]
  conjA f g hf hg hcf hcg := by
    obtain ⟨x, rfl⟩ := e.surjective f
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [MulEquiv.orderOf_eq] at hf hg
    rw [card_centralizer_equiv] at hcf hcg
    obtain ⟨c, k, hck⟩ := h.conjA x y hf hg hcf hcg
    refine ⟨e c, k, ?_⟩
    rw [← map_pow, ← hck, map_mul, map_mul, map_inv]
  typeB f hf hc := by
    obtain ⟨x, rfl⟩ := e.surjective f
    rw [MulEquiv.orderOf_eq] at hf
    rw [card_centralizer_equiv] at hc
    obtain ⟨φ, hφ⟩ := h.typeB x hf hc
    obtain ⟨ρ, hρ⟩ := exists_hom_of_inj φ hφ
    have hC := centralizer_singleton_map e x
    let ε : ↥(centralizer ({e x} : Set Y)) ≃* ↥(centralizer ({x} : Set X)) :=
      (MulEquiv.subgroupCongr hC).trans
        (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).symm
    refine exists_inj_of_hom (ρ.comp ε.toMonoidHom) ?_
    rw [← MonoidHom.comap_ker]
    exact hρ.comap_of_injective _ ε.injective
  count f hf hc F hF hcard := by
    obtain ⟨x, rfl⟩ := e.surjective f
    rw [MulEquiv.orderOf_eq] at hf
    rw [card_centralizer_equiv] at hc
    set F0 : Subgroup X := F.comap e.toMonoidHom with hF0
    have hF0le : F0 ≤ centralizer ({x} : Set X) := by
      intro z hz
      have h1 : e z ∈ F := hz
      have h2 := hF h1
      rw [centralizer_singleton_map] at h2
      obtain ⟨y, hy, hye⟩ := h2
      have : y = z := e.injective hye
      rw [← this]
      exact hy
    have hcard0 : Nat.card F0 = 25 := by
      rw [← hcard]
      exact Nat.card_congr (e.toEquiv.subtypeEquiv (fun z => Iff.rfl))
    have key := h.count x hf hc F0 hF0le hcard0
    have hequiv : Nat.card {z : X // z ∈ F0 ∧ z ≠ 1 ∧
        Nat.card (centralizer ({z} : Set X)) = 1000} =
        Nat.card {z : Y // z ∈ F ∧ z ≠ 1 ∧ Nat.card (centralizer ({z} : Set Y)) = 1000} := by
      refine Nat.card_congr (e.toEquiv.subtypeEquiv (fun z => ?_))
      change _ ↔ (e z ∈ F ∧ e z ≠ 1 ∧ Nat.card (centralizer ({e z} : Set Y)) = 1000)
      rw [card_centralizer_equiv]
      exact and_congr Iff.rfl (and_congr (e.map_ne_one_iff).symm Iff.rfl)
    rw [← hequiv]
    exact key

end CFSG.EvenSporadicStandard.RuStd.S2
