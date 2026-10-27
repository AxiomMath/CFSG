module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Facts

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup

section Iso

variable {X Y : Type} [Group X] [Group Y]

theorem derivedCentralizer_eq (u : X) :
    derivedCentralizer u = ⁅centralizer ({u} : Set X), centralizer ({u} : Set X)⁆ :=
  Subgroup.map_subtype_commutator _

theorem centralizer_singleton_map (e : X ≃* Y) (u : X) :
    centralizer ({e u} : Set Y) = (centralizer ({u} : Set X)).map e.toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    show e.symm y ∈ centralizer ({u} : Set X)
    rw [mem_centralizer_singleton_iff] at hy ⊢
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ centralizer ({u} : Set X) := hx
    rw [mem_centralizer_singleton_iff] at hx'
    show e x ∈ centralizer ({e u} : Set Y)
    rw [mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, hx']

theorem derivedCentralizer_map (e : X ≃* Y) (u : X) :
    derivedCentralizer (e u) = (derivedCentralizer u).map e.toMonoidHom := by
  rw [derivedCentralizer_eq, derivedCentralizer_eq, centralizer_singleton_map,
    Subgroup.map_commutator]

theorem card_centralizer_equiv (e : X ≃* Y) (u : X) :
    Nat.card (centralizer ({e u} : Set Y)) = Nat.card (centralizer ({u} : Set X)) := by
  rw [centralizer_singleton_map,
    Subgroup.card_map_of_injective e.injective]

theorem card_inf_centralizer_equiv (e : X ≃* Y) (u v : X) :
    Nat.card ↥(centralizer ({e u} : Set Y) ⊓ centralizer ({e v} : Set Y)) =
      Nat.card ↥(centralizer ({u} : Set X) ⊓ centralizer ({v} : Set X)) := by
  have h : centralizer ({e u} : Set Y) ⊓ centralizer ({e v} : Set Y) =
      (centralizer ({u} : Set X) ⊓ centralizer ({v} : Set X)).map e.toMonoidHom := by
    rw [centralizer_singleton_map, centralizer_singleton_map,
      Subgroup.map_inf _ _ _ e.injective]
  rw [h, Subgroup.card_map_of_injective e.injective]

theorem RuFacts.of_mulEquiv (e : X ≃* Y) (h : RuFacts X) : RuFacts Y where
  card_eq := by rw [Nat.card_congr e.toEquiv.symm]; exact h.card_eq
  card_centralizer v hv := by
    obtain ⟨u, rfl⟩ := e.surjective v
    rw [card_centralizer_equiv]
    exact h.card_centralizer u (by rwa [MulEquiv.orderOf_eq] at hv)
  isConj_A v w hv hw hcv hcw := by
    obtain ⟨u, rfl⟩ := e.surjective v
    obtain ⟨u', rfl⟩ := e.surjective w
    rw [card_centralizer_equiv] at hcv hcw
    rw [MulEquiv.orderOf_eq] at hv hw
    exact e.toMonoidHom.map_isConj (h.isConj_A u u' hv hw hcv hcw)
  isConj_B v w hv hw hcv hcw := by
    obtain ⟨u, rfl⟩ := e.surjective v
    obtain ⟨u', rfl⟩ := e.surjective w
    rw [card_centralizer_equiv] at hcv hcw
    rw [MulEquiv.orderOf_eq] at hv hw
    exact e.toMonoidHom.map_isConj (h.isConj_B u u' hv hw hcv hcw)
  sq_A v hv hcv := by
    obtain ⟨u, rfl⟩ := e.surjective v
    rw [card_centralizer_equiv] at hcv
    rw [MulEquiv.orderOf_eq] at hv
    obtain ⟨y, hy⟩ := h.sq_A u hv hcv
    exact ⟨e y, by rw [← map_pow, hy]⟩
  pair := by
    obtain ⟨u, a, hu2, huB, ha2, haA, hau, ha_der, h256⟩ := h.pair
    refine ⟨e u, e a, by rwa [MulEquiv.orderOf_eq], by rwa [card_centralizer_equiv],
      by rwa [MulEquiv.orderOf_eq], by rwa [card_centralizer_equiv],
      by rw [← map_mul, ← map_mul, hau], ?_, by rwa [card_inf_centralizer_equiv]⟩
    rw [derivedCentralizer_map]
    exact ⟨a, ha_der, rfl⟩
  no_256 p q hp hq hpq hpq' hcp hcq := by
    obtain ⟨p', rfl⟩ := e.surjective p
    obtain ⟨q', rfl⟩ := e.surjective q
    rw [card_centralizer_equiv] at hcp hcq
    rw [MulEquiv.orderOf_eq] at hp hq
    rw [card_inf_centralizer_equiv]
    refine h.no_256 p' q' hp hq (fun h' => hpq (by rw [h'])) ?_ hcp hcq
    apply e.injective
    rw [map_mul, map_mul]
    exact hpq'

end Iso

end CFSG.EvenSporadicStandard.RuStd
