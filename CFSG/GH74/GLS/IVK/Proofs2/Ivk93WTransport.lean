module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93W

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint CFSG.ComponentClassification
open scoped commutatorElement

theorem Ivk93W.of_equiv {J J' : Type} [Group J] [Finite J] [Group J'] [Finite J'] (Φ : J ≃* J')
    {x : J} {q : ℕ} {B : Subgroup J} (h : Ivk93W x q B) :
    Ivk93W (Φ x) q (B.map Φ.toMonoidHom) := by
  have hc := map_centralizer_singleton_equiv' Φ x
  refine ⟨isCentralInvolution_of_equiv Φ h.cen, h.odd, h.five, ?_, ⟨x, h.mem, rfl⟩, ?_, ?_⟩
  · rw [← hc]
    exact ⟨Subgroup.map_mono h.le, (isPComponent_subgroupOf_map_iff' Φ h.le).1 h.comp.2⟩
  · obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h.sl
    exact ⟨F, hF, hFin, hq, ⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (B.equivMapOfInjective Φ.toMonoidHom Φ.injective)).symm.trans e⟩⟩
  · intro M' hM'
    have hcs := map_centralizer_singleton_equiv' Φ.symm (Φ x)
    rw [MulEquiv.symm_apply_apply] at hcs
    have hM'le : M' ≤ centralizer ({Φ x} : Set J') := hM'.1
    have hMle : M'.map Φ.symm.toMonoidHom ≤ centralizer ({x} : Set J) := by
      rw [← hcs]
      exact Subgroup.map_mono hM'le
    have hMcomp : IsPCompIn 2 (centralizer ({x} : Set J)) (M'.map Φ.symm.toMonoidHom) := by
      refine ⟨hMle, ?_⟩
      have := (isPComponent_subgroupOf_map_iff' Φ.symm hM'le).1 hM'.2
      rwa [hcs] at this
    have hMB := h.uniq _ hMcomp
    ext y
    constructor
    · intro hy
      have : Φ.symm y ∈ M'.map Φ.symm.toMonoidHom := ⟨y, hy, rfl⟩
      rw [hMB] at this
      exact ⟨Φ.symm y, this, by simp⟩
    · rintro ⟨b, hb, rfl⟩
      rw [← hMB] at hb
      obtain ⟨m, hm, rfl⟩ := hb
      simpa using hm

theorem Ivk93WBound.of_equiv {J J' : Type} [Group J] [Group J'] (Φ : J ≃* J') {q : ℕ}
    (h : Ivk93WBound J q) : Ivk93WBound J' q := by
  unfold Ivk93WBound at *
  rwa [← Nat.card_congr Φ.toEquiv]

theorem Ivk93WQuat.of_equiv {J J' : Type} [Group J] [Group J'] (Φ : J ≃* J') {x : J} {B : Subgroup J}
    (h : Ivk93WQuat x B) : Ivk93WQuat (Φ x) (B.map Φ.toMonoidHom) := by
  obtain ⟨Q, hQC, hxQ, hQ8, ⟨a, ha, b, hb, hax, hbx, hab⟩, hcomm⟩ := h
  refine ⟨Q.map Φ.toMonoidHom, ?_, ⟨x, hxQ, rfl⟩, ?_,
    ⟨Φ a, ⟨a, ha, rfl⟩, Φ b, ⟨b, hb, rfl⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [← map_centralizer_singleton_equiv' Φ x]
    exact Subgroup.map_mono hQC
  · rw [Subgroup.card_map_of_injective Φ.injective]
    exact hQ8
  · rw [← map_mul, hax]
  · rw [← map_mul, hbx]
  · intro hc
    apply hab
    apply Φ.injective
    rw [map_mul, map_mul]
    exact hc
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 := hcomm a ha b hb
    have hmap : pPrimeCoreOf 2 (B.map Φ.toMonoidHom) =
        (pPrimeCoreOf 2 B).map Φ.toMonoidHom := by
      unfold pPrimeCoreOf
      rw [Subgroup.map_map, ← CFSG.pPrimeCore_map_iso 2
        (B.equivMapOfInjective Φ.toMonoidHom Φ.injective), Subgroup.map_map]
      rfl
    rw [hmap]
    refine ⟨⁅a, b⁆, h1, ?_⟩
    simp [commutatorElement_def]

end CFSG.GH74.GLS.IVK.Proofs2
