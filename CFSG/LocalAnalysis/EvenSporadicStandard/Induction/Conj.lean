module

import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {G : Type} [Group G]

theorem map_conj_map_conj (K : Subgroup G) (a x : G) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      K.map (MulAut.conj (x * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

section MulEquiv

variable {A B : Type} [Group A] [Group B]

theorem mem_normalizer_map_mulEquiv (e : A ≃* B) (K : Subgroup A) (a : A) :
    e a ∈ normalizer ((K.map e.toMonoidHom : Subgroup B) : Set B) ↔ a ∈ normalizer (K : Set A) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h k
    have := h (e k)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at this
    simpa using this
  · intro h b
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simpa using h (e.symm b)

theorem stdBare_map_mulEquiv (e : A ≃* B) {K : Subgroup A} (h : StdBare K) :
    StdBare (K.map e.toMonoidHom) := by
  refine ⟨fun b => ?_, fun b hb => ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective b
    rw [← CFSG.StandardSubgroupAPI.map_conj_map_mulEquiv, ← Subgroup.map_commutator]
    intro hbot
    exact h.1 a ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hbot)
  · obtain ⟨a, rfl⟩ := e.surjective b
    have ha : a ∉ normalizer (K : Set A) := fun hn =>
      hb ((mem_normalizer_map_mulEquiv e K a).2 hn)
    have hodd := h.2 a ha
    have heq : centralizer ((K.map e.toMonoidHom : Subgroup B) : Set B) ⊓
        (centralizer ((K.map e.toMonoidHom : Subgroup B) : Set B)).map
          (MulAut.conj (e a)).toMonoidHom =
        (centralizer (K : Set A) ⊓ (centralizer (K : Set A)).map
          (MulAut.conj a).toMonoidHom).map e.toMonoidHom := by
      rw [CFSG.StandardSubgroupAPI.centralizer_map_mulEquiv,
        ← CFSG.StandardSubgroupAPI.map_conj_map_mulEquiv, Subgroup.map_inf _ _ _ e.injective]
    rw [heq, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact hodd

end MulEquiv

theorem StdBare.map_conj {K : Subgroup G} (h : StdBare K) (a : G) :
    StdBare (K.map (MulAut.conj a).toMonoidHom) :=
  stdBare_map_mulEquiv (MulAut.conj a) h

theorem isCompIn_map_conj_of_mem_normalizer {M X : Subgroup G} (h : IsCompIn M X) {x : G}
    (hx : x ∈ normalizer (X : Set G)) : IsCompIn (M.map (MulAut.conj x).toMonoidHom) X := by
  set φ : MulAut ↥X := Subgroup.normalizerMonoidHom X ⟨x, hx⟩ with hφ
  have hφapp : ∀ y : ↥X, ((φ y : ↥X) : G) = x * y * x⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨x, hx⟩ y
  have hle : M.map (MulAut.conj x).toMonoidHom ≤ X := by
    rintro _ ⟨m, hm, rfl⟩
    have := (φ ⟨m, h.1 hm⟩).2
    rw [hφapp] at this
    exact this
  refine ⟨hle, ?_⟩
  have hc := CFSG.LocalCores.isComponent_map_mulEquiv φ h.2
  have heq : (M.map (MulAut.conj x).toMonoidHom).subgroupOf X =
      (M.subgroupOf X).map φ.toMonoidHom := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, hmy⟩
      refine ⟨⟨m, h.1 hm⟩, hm, Subtype.ext ?_⟩
      show ((φ ⟨m, h.1 hm⟩ : ↥X) : G) = y
      rw [hφapp]
      exact hmy
    · rintro ⟨m, hm, hmy⟩
      refine ⟨(m : G), hm, ?_⟩
      have := congrArg Subtype.val hmy
      change ((φ m : ↥X) : G) = y at this
      rw [hφapp] at this
      exact this
  rw [heq]
  exact hc

end CFSG.EvenSporadicStandard.Induction
