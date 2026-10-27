module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

@[expose] def IsTwoGenQuasi (Q : Type*) [Group Q] : Prop :=
  primeResidual 2 Q = ⊤ ∧ IsQuasisimple (Q ⧸ pPrimeCore 2 Q)

theorem nonempty_quotPPrimeCore_equiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') :
    Nonempty (Q ⧸ pPrimeCore 2 Q ≃* Q' ⧸ pPrimeCore 2 Q') :=
  ⟨QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)⟩

theorem IsTwoGenQuasi.congr {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : IsTwoGenQuasi Q) : IsTwoGenQuasi Q' := by
  refine ⟨?_, ?_⟩
  · rw [← primeResidual_map_equiv 2 e, h.1]
    exact Subgroup.map_equiv_top e
  · obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv e
    exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr f).1 h.2

theorem isTwoGenQuasi_congr_iff {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') :
    IsTwoGenQuasi Q ↔ IsTwoGenQuasi Q' :=
  ⟨IsTwoGenQuasi.congr e, IsTwoGenQuasi.congr e.symm⟩

theorem isPComponent_two_iff {X : Type*} [Group X] [Finite X] {L : Subgroup X} :
    IsPComponent 2 L ↔ L.IsSubnormal ∧ IsTwoGenQuasi ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pComponent_iff_subnormal_generated_quasisimple 2 L]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

theorem isTwoGenQuasi_subgroupOf_iff {X : Type*} [Group X] {A D : Subgroup X} (hAD : A ≤ D) :
    IsTwoGenQuasi ↥(A.subgroupOf D) ↔ IsTwoGenQuasi ↥A :=
  isTwoGenQuasi_congr_iff (Subgroup.subgroupOfEquivOfLe hAD)

theorem isPComponent_subgroupOf_mono {X : Type*} [Group X] [Finite X] {A D D' : Subgroup X}
    (hAD' : A ≤ D') (hD'D : D' ≤ D) (h : IsPComponent 2 (A.subgroupOf D)) :
    IsPComponent 2 (A.subgroupOf D') := by
  have hAD : A ≤ D := hAD'.trans hD'D
  rw [isPComponent_two_iff] at h ⊢
  refine ⟨?_, (isTwoGenQuasi_subgroupOf_iff hAD').2 ((isTwoGenQuasi_subgroupOf_iff hAD).1 h.2)⟩
  have := h.1.comap (Subgroup.inclusion hD'D)
  rwa [Subgroup.comap_inclusion_subgroupOf] at this

theorem isPComponent_subgroupOf_of_le {X : Type*} [Group X] [Finite X] {A D : Subgroup X}
    (hAD : A ≤ D) (h : IsPComponent 2 A) : IsPComponent 2 (A.subgroupOf D) := by
  rw [isPComponent_two_iff] at h ⊢
  exact ⟨h.1.subgroupOf, (isTwoGenQuasi_subgroupOf_iff hAD).2 h.2⟩

theorem isPComponent_subgroupOf_map_iff {G G' : Type*} [Group G] [Group G'] (p : ℕ)
    (f : G →* G') (hf : Function.Injective f) {A D : Subgroup G} (hAD : A ≤ D) :
    IsPComponent p ((A.map f).subgroupOf (D.map f)) ↔ IsPComponent p (A.subgroupOf D) := by
  let ψ : D ≃* D.map f := D.equivMapOfInjective f hf
  have key : (A.subgroupOf D).map ψ.toMonoidHom = (A.map f).subgroupOf (D.map f) := by
    ext ⟨x, hx⟩
    rw [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨⟨c, hc⟩, hcA, hceq⟩
      exact ⟨c, hcA, congrArg Subtype.val hceq⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hAD hm⟩, hm, rfl⟩
  rw [← key]
  constructor
  · intro h
    have h2 := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent p ψ.symm h
    rwa [Subgroup.map_map, show ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id _ from by
      ext x; simp, Subgroup.map_id] at h2
  · exact LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent p ψ

theorem centralizer_singleton_subgroup {X : Type*} [Group X] {H : Subgroup X} {t : X}
    (htH : t ∈ H) :
    centralizer ({(⟨t, htH⟩ : ↥H)} : Set ↥H) = (centralizer ({t} : Set X)).subgroupOf H := by
  ext x
  simp only [mem_centralizer_singleton_iff, mem_subgroupOf]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem isPComponent_subgroupOf_subgroupOf_iff {X : Type*} [Group X] {A D H : Subgroup X}
    (hAD : A ≤ D) (hAH : A ≤ H) :
    IsPComponent 2 ((A.subgroupOf H).subgroupOf (D.subgroupOf H)) ↔
      IsPComponent 2 (A.subgroupOf (D ⊓ H)) := by
  have h1 : (A.subgroupOf H) ≤ D.subgroupOf H := Subgroup.subgroupOf_mono H hAD
  have h := isPComponent_subgroupOf_map_iff 2 H.subtype H.subtype_injective h1
  rw [Subgroup.map_subgroupOf_eq_of_le hAH, Subgroup.subgroupOf_map_subtype] at h
  exact h.symm

end CFSG.OddStandard.Solomon75
