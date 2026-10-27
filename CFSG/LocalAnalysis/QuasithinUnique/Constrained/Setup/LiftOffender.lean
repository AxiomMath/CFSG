module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect3

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section WLevel

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}
  (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
  (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I)

theorem actOn_L_mk (l : ↥L) (u : ↥I) :
    actOn L A I hAn hI L le_sup_left l (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I hI
        ⟨l, Subgroup.mem_sup_left l.2⟩ u) :=
  actW_mk hAn hI ⟨l, Subgroup.mem_sup_left l.2⟩ u

theorem lbar_irreducible (hirr : IsIrrQuot (MonoidHom.id (V ≃ₗ[ZMod 2] V)) L I) :
    Nontrivial (↥I ⧸ fixIn L I) ∧
      ∀ U : Submodule (ZMod 2) (↥I ⧸ fixIn L I),
        (∀ x ∈ Lbar L A I hAn hI, ∀ u ∈ U, x u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  have hZ : ∀ (i : ↥I), (Submodule.Quotient.mk i : ↥I ⧸ fixIn L I) = 0 ↔
      ∀ l ∈ L, l (i : V) = i := fun i => by
    rw [Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl
  refine ⟨?_, fun U hU => ?_⟩
  · obtain ⟨i, hiI, hi⟩ : ∃ i ∈ I, i ∉ fixGL L := by
      by_contra hcon
      push Not at hcon
      exact hirr.1 hcon
    exact ⟨⟨Submodule.Quotient.mk ⟨i, hiI⟩, 0, fun h => hi ((hZ ⟨i, hiI⟩).1 h)⟩⟩
  · set Ũ : Submodule (ZMod 2) V :=
      (U.comap (fixIn L I).mkQ).map I.subtype with hŨ
    have hmemŨ : ∀ v, v ∈ Ũ ↔ ∃ h : v ∈ I, (Submodule.Quotient.mk ⟨v, h⟩ : ↥I ⧸ fixIn L I) ∈ U := by
      intro v
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i.2, hi⟩
      · rintro ⟨h, hv⟩
        exact ⟨⟨v, h⟩, hv, rfl⟩
    have hinv : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) L Ũ := by
      intro l hl u hu
      obtain ⟨hu1, hu2⟩ := (hmemŨ u).1 hu
      have hlI : (MonoidHom.id (V ≃ₗ[ZMod 2] V)) l u ∈ I :=
        hI l (Subgroup.mem_sup_left hl) u hu1
      refine (hmemŨ _).2 ⟨hlI, ?_⟩
      have h1 := hU (actOn L A I hAn hI L le_sup_left ⟨l, hl⟩) ⟨⟨l, hl⟩, rfl⟩ _ hu2
      rw [actOn_L_mk hAn hI] at h1
      have e : (⟨(MonoidHom.id (V ≃ₗ[ZMod 2] V)) l u, hlI⟩ : ↥I) =
          resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I hI ⟨l, Subgroup.mem_sup_left hl⟩
            ⟨u, hu1⟩ :=
        Subtype.ext (resSub_apply (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I hI
          ⟨l, Subgroup.mem_sup_left hl⟩ ⟨u, hu1⟩).symm
      rw [e]
      exact h1
    have hlow : I ⊓ fixSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) L ≤ Ũ := by
      intro z hz
      refine (hmemŨ z).2 ⟨hz.1, ?_⟩
      have : (Submodule.Quotient.mk ⟨z, hz.1⟩ : ↥I ⧸ fixIn L I) = 0 := (hZ ⟨z, hz.1⟩).2 hz.2
      rw [this]
      exact U.zero_mem
    have hle : Ũ ≤ I := by
      rintro _ ⟨i, -, rfl⟩
      exact i.2
    rcases hirr.2 Ũ hinv hlow hle with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨i, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      have : (i : V) ∈ Ũ := (hmemŨ _).2 ⟨i.2, hw⟩
      rw [h] at this
      exact (Submodule.mem_bot _).2 ((hZ i).2 this.2)
    · right
      rw [eq_top_iff]
      intro w _
      obtain ⟨i, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      have : (i : V) ∈ Ũ := by rw [h]; exact i.2
      obtain ⟨h', hmem⟩ := (hmemŨ _).1 this
      exact hmem

theorem abar_le_normalizer_lbar :
    Abar L A I hAn hI ≤ Subgroup.normalizer (Lbar L A I hAn hI : Set _) := by
  have key : ∀ x ∈ Abar L A I hAn hI, ∀ y ∈ Lbar L A I hAn hI, x * y * x⁻¹ ∈ Lbar L A I hAn hI := by
    rintro _ ⟨a, rfl⟩ _ ⟨l, rfl⟩
    refine ⟨⟨(a : V ≃ₗ[ZMod 2] V) * l * (a : V ≃ₗ[ZMod 2] V)⁻¹,
      conj_mem_of_mem_normalizer (hAn a.2) l.2⟩, ?_⟩
    have h1 : actOn L A I hAn hI L le_sup_left
        ⟨(a : V ≃ₗ[ZMod 2] V) * l * (a : V ≃ₗ[ZMod 2] V)⁻¹, conj_mem_of_mem_normalizer (hAn a.2) l.2⟩ =
        actW L A I hAn hI ⟨(a : V ≃ₗ[ZMod 2] V), Subgroup.mem_sup_right a.2⟩ *
          actW L A I hAn hI ⟨(l : V ≃ₗ[ZMod 2] V), Subgroup.mem_sup_left l.2⟩ *
          (actW L A I hAn hI ⟨(a : V ≃ₗ[ZMod 2] V), Subgroup.mem_sup_right a.2⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    exact h1
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact key x hx y hy
  · intro hy
    have h1 := key x⁻¹ (Subgroup.inv_mem _ hx) _ hy
    have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rw [e] at h1
    exact h1

end WLevel

end CFSG.QuasithinUnique.Setup.Lift
