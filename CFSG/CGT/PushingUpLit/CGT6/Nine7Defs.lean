module

public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentTransport
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Nine7

open CFSG (conjugate)
open CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_centralizer_single {a x : G} :
    x ∈ Subgroup.centralizer ({a} : Set G) ↔ a * x = x * a := by
  rw [Subgroup.mem_centralizer_iff]
  simp

theorem mem_conjugate {X : Subgroup G} {g x : G} : x ∈ conjugate X g ↔ g * x * g⁻¹ ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem conjugate_one (X : Subgroup G) : conjugate X 1 = X := by
  ext x
  simp [mem_conjugate]

theorem conjugate_conjugate_inv (X : Subgroup G) (g : G) : conjugate (conjugate X g) g⁻¹ = X := by
  rw [CFSG.GroupTheory.conjugate_conjugate, mul_inv_cancel, conjugate_one]

theorem conjugate_inv_conjugate (X : Subgroup G) (g : G) : conjugate (conjugate X g⁻¹) g = X := by
  rw [CFSG.GroupTheory.conjugate_conjugate, inv_mul_cancel, conjugate_one]

theorem conjugate_commutator (X Y : Subgroup G) (g : G) :
    ⁅conjugate X g, conjugate Y g⁆ = conjugate ⁅X, Y⁆ g :=
  (Subgroup.map_commutator _ _ _).symm

theorem conjugate_bot (g : G) : conjugate (⊥ : Subgroup G) g = ⊥ := by
  ext x
  simp [mem_conjugate, Subgroup.mem_bot]

theorem conjugate_iSup {ι : Sort*} (X : ι → Subgroup G) (g : G) :
    conjugate (⨆ i, X i) g = ⨆ i, conjugate (X i) g :=
  Subgroup.map_iSup _ _

theorem card_conjugate (X : Subgroup G) (g : G) : Nat.card (conjugate X g) = Nat.card X :=
  Nat.card_congr (X.equivMapOfInjective _ (MulAut.conj g⁻¹).injective).symm.toEquiv

theorem conjugate_centralizer_singleton (a g : G) :
    conjugate (Subgroup.centralizer ({a} : Set G)) g =
      Subgroup.centralizer ({g⁻¹ * a * g} : Set G) := by
  ext x
  rw [mem_conjugate, mem_centralizer_single, mem_centralizer_single]
  constructor
  · intro h
    calc g⁻¹ * a * g * x = g⁻¹ * (a * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * a) * g := by rw [h]
      _ = x * (g⁻¹ * a * g) := by group
  · intro h
    calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * a := by group

theorem conjugate_centralizer (X : Subgroup G) (g : G) :
    conjugate (Subgroup.centralizer (X : Set G)) g =
      Subgroup.centralizer (conjugate X g : Set G) := by
  ext x
  rw [mem_conjugate, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have hy' : g * y * g⁻¹ ∈ X := mem_conjugate.1 hy
    have h1 := h _ hy'
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h1]
      _ = x * y := by group
  · intro h y hy
    have hy' : g⁻¹ * y * g ∈ conjugate X g :=
      mem_conjugate.2 (by simpa [mul_assoc] using hy)
    have h1 := h _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * y := by group

theorem conjugate_normalizer (X : Subgroup G) (g : G) :
    conjugate (Subgroup.normalizer (X : Set G)) g =
      Subgroup.normalizer (conjugate X g : Set G) := by
  ext x
  rw [mem_conjugate, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (g * y * g⁻¹)
    rw [mem_conjugate, mem_conjugate]
    constructor
    · intro hy
      have : g * (x * y * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact h1.1 hy
    · intro hy
      have : g * (x * y * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
      rw [this] at hy
      exact h1.2 hy
  · intro h y
    have h1 := h (g⁻¹ * y * g)
    rw [mem_conjugate, mem_conjugate] at h1
    have e1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    have e2 : g * (x * (g⁻¹ * y * g) * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * y * (g * x * g⁻¹)⁻¹ := by group
    rw [e1, e2] at h1
    exact h1

theorem orderOf_conjugate_elt (a g : G) : orderOf (g⁻¹ * a * g) = orderOf a := by
  have := (MulAut.conj g⁻¹).orderOf_eq a
  simpa [MulAut.conj_apply] using this

abbrev QS (L : Subgroup G) : Prop := CFSG.Open.IsQuasisimple ↥L

theorem qs_conjugate {L : Subgroup G} (hL : QS L) (g : G) : QS (conjugate L g) :=
  Components.quasisimple_of_equiv
    (L.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm hL

@[expose] def IsCompIn (L X : Subgroup G) : Prop :=
  L ≤ X ∧ (L.subgroupOf X).IsSubnormal ∧ QS L

theorem IsCompIn.qs {L X : Subgroup G} (h : IsCompIn L X) : QS L := h.2.2

theorem IsCompIn.of_le {L X Y : Subgroup G} (h : IsCompIn L X) (hLY : L ≤ Y) (hYX : Y ≤ X) :
    IsCompIn L Y :=
  ⟨hLY, CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hYX h.2.1, h.2.2⟩

theorem IsCompIn.trans {L Y X : Subgroup G} (h : IsCompIn L Y) (hYX : (Y.subgroupOf X).IsSubnormal)
    (hle : Y ≤ X) : IsCompIn L X :=
  ⟨h.1.trans hle, CFSG.GroupTheory.isSubnormal_subgroupOf_trans h.1 hle h.2.1 hYX, h.2.2⟩

theorem isCompIn_of_normal {L X : Subgroup G} (hLX : L ≤ X) (hn : (L.subgroupOf X).Normal)
    (hq : QS L) : IsCompIn L X :=
  ⟨hLX, hn.isSubnormal, hq⟩

theorem IsCompIn.cj {L X : Subgroup G} (h : IsCompIn L X) (g : G) :
    IsCompIn (conjugate L g) (conjugate X g) :=
  ⟨Subgroup.map_mono h.1, CFSG.GroupTheory.isSubnormal_subgroupOf_conjugate g h.2.1,
    qs_conjugate h.2.2 g⟩

theorem commute_of_isCompIn_ne [Finite G] {L₁ L₂ X : Subgroup G} (h₁ : IsCompIn L₁ X)
    (h₂ : IsCompIn L₂ X) (hne : L₁ ≠ L₂) : ⁅L₁, L₂⁆ = ⊥ := by
  have c₁ : CFSG.Open.IsComponentOf (L₁.subgroupOf X) ⊤ :=
    (OrdinaryComponentTransport.subgroupOf_iff L₁ X h₁.1).2 ⟨h₁.2.1, h₁.2.2⟩
  have c₂ : CFSG.Open.IsComponentOf (L₂.subgroupOf X) ⊤ :=
    (OrdinaryComponentTransport.subgroupOf_iff L₂ X h₂.1).2 ⟨h₂.2.1, h₂.2.2⟩
  have hne' : L₁.subgroupOf X ≠ L₂.subgroupOf X := by
    intro h
    apply hne
    have := congrArg (Subgroup.map X.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le h₁.1, Subgroup.map_subgroupOf_eq_of_le h₂.1] at this
  have h3 := congrArg (Subgroup.map X.subtype) (LocalComponents.commute_of_ne _ _ c₁ c₂ hne')
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h₁.1,
    Subgroup.map_subgroupOf_eq_of_le h₂.1, Subgroup.map_bot] at h3

theorem even_card_of_qs [Finite G] {L : Subgroup G} (hL : QS L) : Even (Nat.card ↥L) := by
  have hperf : Group.IsPerfect ↥L := ⟨hL.1⟩
  have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2
  have hnt : Nontrivial ↥L :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  by_contra hodd
  have hsolv : Group.IsSolvable ↥L := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd)
  exact Group.IsPerfect.not_isSolvable ↥L hsolv

theorem exists_involution_of_qs [Finite G] {L : Subgroup G} (hL : QS L) :
    ∃ t ∈ L, orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp (even_card_of_qs hL))
  exact ⟨x, x.2, by rw [← hx]; exact Subgroup.orderOf_coe x⟩

@[expose] def Star (A : Subgroup G) : Prop :=
  ∀ a : G, orderOf a = 2 → A ≤ Subgroup.centralizer ({a} : Set G) →
    (A.subgroupOf (Subgroup.centralizer ({a} : Set G))).IsSubnormal

@[expose] def ConjCl (A : Subgroup G) : Set (Subgroup G) := {B | ∃ g : G, B = conjugate A g}

@[expose] def Rel (B B' : Subgroup G) : Prop := B = B' ∨ ⁅B, B'⁆ = ⊥

@[expose] def Dgrp (A B : Subgroup G) : Subgroup G :=
  ⨆ (B' : Subgroup G) (_ : B' ∈ ConjCl A ∧ Rel B B'), B'

@[expose] def Delta (A X : Subgroup G) : Subgroup G :=
  ⨆ (B : Subgroup G) (_ : B ∈ ConjCl A ∧ B ≤ X ∧ (B.subgroupOf X).IsSubnormal), B

theorem star_conjugate {A : Subgroup G} (h : Star A) (g : G) : Star (conjugate A g) := by
  intro a ha hAa
  have h0 : orderOf (g * a * g⁻¹) = 2 := by
    have := orderOf_conjugate_elt a g⁻¹
    simpa [inv_inv] using this.trans ha
  have hA : A ≤ Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
    intro x hx
    rw [mem_centralizer_single]
    have hx' : g⁻¹ * x * g ∈ conjugate A g := by
      rw [mem_conjugate]
      simpa [mul_assoc] using hx
    have := mem_centralizer_single.1 (hAa hx')
    calc g * a * g⁻¹ * x = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * a) * g⁻¹ := by rw [this]
      _ = x * (g * a * g⁻¹) := by group
  have hsub := CFSG.GroupTheory.isSubnormal_subgroupOf_conjugate g (h _ h0 hA)
  have e : conjugate (Subgroup.centralizer ({g * a * g⁻¹} : Set G)) g =
      Subgroup.centralizer ({a} : Set G) := by
    rw [conjugate_centralizer_singleton]
    congr 2
    group
  rwa [e] at hsub

theorem mem_ConjCl_self (A : Subgroup G) : A ∈ ConjCl A := ⟨1, (conjugate_one A).symm⟩

theorem ConjCl.cj {A B : Subgroup G} (hB : B ∈ ConjCl A) (g : G) :
    conjugate B g ∈ ConjCl A := by
  obtain ⟨x, rfl⟩ := hB
  exact ⟨x * g, CFSG.GroupTheory.conjugate_conjugate A x g⟩

theorem ConjCl.star {A B : Subgroup G} (hA : Star A) (hB : B ∈ ConjCl A) : Star B := by
  obtain ⟨x, rfl⟩ := hB
  exact star_conjugate hA x

theorem ConjCl.qs {A B : Subgroup G} (hA : QS A) (hB : B ∈ ConjCl A) : QS B := by
  obtain ⟨x, rfl⟩ := hB
  exact qs_conjugate hA x

theorem Rel.refl (B : Subgroup G) : Rel B B := Or.inl rfl

theorem Rel.symm {B B' : Subgroup G} (h : Rel B B') : Rel B' B := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (by rw [Subgroup.commutator_comm]; exact h)

theorem Rel.cj {B B' : Subgroup G} (h : Rel B B') (g : G) :
    Rel (conjugate B g) (conjugate B' g) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · refine Or.inr ?_
    rw [conjugate_commutator, h, conjugate_bot]

end CFSG.CGT.PushingUpLit.CGT6.Nine7
