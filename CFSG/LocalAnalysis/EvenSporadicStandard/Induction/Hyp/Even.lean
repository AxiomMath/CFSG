module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.EvenCoverOutHered

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def MonsterNoCover : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → IsSporadic (L ⧸ center L) .M →
    center L = ⊥

theorem evenCoverExcl_of_odd {s' : TauCeti.SporadicName}
    (h : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
      IsSporadic (X ⧸ center X) s' → Odd (Nat.card (center X))) : EvenCoverExclHered s' := by
  intro Y _ _ _ N' hN hidx hkp L' hsol hq hcq hodd
  exact absurd (h ↥L' hq hcq) hodd

theorem evenCoverExcl_M (hM : MonsterNoCover) : EvenCoverExclHered .M := by
  intro Y _ _ _ N' hN hidx hkp L' hsol hq hcq hodd
  exfalso
  apply hodd
  have hc := hM ↥L' hq hcq
  rw [hc]
  have : Nat.card ↥(⊥ : Subgroup ↥L') = 1 := by simp
  rw [this]
  exact odd_one

theorem map_centralizer_singleton {A B : Type} [Group A] [Group B] (e : A ≃* B) (t : A) :
    (centralizer ({t} : Set A)).map e.toMonoidHom = centralizer ({e t} : Set B) := by
  ext z
  rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply e.symm.injective
    simpa [map_mul] using h
  · intro h
    have := congrArg e.symm h
    simpa [map_mul] using this

theorem isCompIn_map_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {M X : Subgroup A}
    (h : IsCompIn M X) : IsCompIn (M.map e.toMonoidHom) (X.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, ?_⟩
  let φ : ↥X ≃* ↥(X.map e.toMonoidHom) := Subgroup.equivMapOfInjective X e.toMonoidHom e.injective
  have hc := CFSG.LocalCores.isComponent_map_mulEquiv φ h.2
  have heq : (M.subgroupOf X).map φ.toMonoidHom =
      (M.map e.toMonoidHom).subgroupOf (X.map e.toMonoidHom) := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(w : A), hw, rfl⟩
    · rintro ⟨m, hm, hmz⟩
      obtain ⟨x, hx, hxz⟩ := z.2
      have hmx : m = x := e.injective (hmz.trans hxz.symm)
      refine ⟨⟨m, hmx ▸ hx⟩, hm, ?_⟩
      apply Subtype.ext
      exact hmz
  rwa [heq] at hc

end CFSG.EvenSporadicStandard.Induction.Hyp
