module

public import CFSG.ClassicalInvolution.Q3.Exact
public import CFSG.ClassicalInvolution.Balance.BootstrapFunctor

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

@[expose] def LieSystemOddCentralizer3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Λ : Set (Subgroup Y)), LieSystemMod3 Λ →
    ∀ a : Y, orderOf a = 2 →
      oddCoreIn (Subgroup.centralizer ({a} : Set Y)) ≤ classicalInvolutionOddCore Y

section Local

variable {G : Type} [Group G] [Finite G]

@[expose] def LocalOddCentralizer3 (Ω : Set (Subgroup G)) : Prop :=
  ∀ b : G, b ∉ Subgroup.center G → ∀ a ∈ centralizingLayer Ω {b}, orderOf a = 2 →
    oddCoreIn (centralizingLayer Ω {b} ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      oddCoreIn (centralizingLayer Ω {b})

omit [Finite G] in
theorem map_oddCoreIn_subtype {Y : Subgroup G} (C : Subgroup ↥Y) :
    (oddCoreIn C).map Y.subtype = oddCoreIn (C.map Y.subtype) := by
  let e : ↥C ≃* ↥(C.map Y.subtype) := C.equivMapOfInjective Y.subtype Y.subtype_injective
  have hO : (componentClassificationOddCore ↥C).map e.toMonoidHom =
      componentClassificationOddCore ↥(C.map Y.subtype) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  have hcomp : Y.subtype.comp C.subtype = (C.map Y.subtype).subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [oddCoreIn, oddCoreIn, ← hO, Subgroup.map_map, Subgroup.map_map, hcomp]

omit [Finite G] in
theorem map_centralizer_subtype {Y : Subgroup G} {a : G} (ha : a ∈ Y) :
    (Subgroup.centralizer ({(⟨a, ha⟩ : ↥Y)} : Set ↥Y)).map Y.subtype =
      Y ⊓ Subgroup.centralizer ({a} : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))⟩
  · rintro ⟨hxY, hxa⟩
    exact ⟨⟨x, hxY⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxa)), rfl⟩

theorem localOddCentralizer3_of_lieSystem {Ω : Set (Subgroup G)}
    (hMF : LieSystemOddCentralizer3) (hIH : LocalLieSystems3 Ω) : LocalOddCentralizer3 Ω := by
  intro b hb a haY ha2
  have hLie := hIH {b} (fun h => hb (Set.singleton_subset_iff.mp h))
  have h1 := hMF ↥(centralizingLayer Ω {b})
    (restrictFamily (centralizingMembers Ω {b}) (centralizingLayer Ω {b})) hLie ⟨a, haY⟩
    (by rw [Subgroup.orderOf_mk]; exact ha2)
  have h2 := Subgroup.map_mono (f := (centralizingLayer Ω {b}).subtype) h1
  rw [map_oddCoreIn_subtype, map_centralizer_subtype haY] at h2
  exact h2

end Local

section WeakBalance

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem commutator_mem_involutionOddCore_of_localOddCentralizer3 (hΩ : ConjInvariant Ω)
    (hO : LocalOddCentralizer3 Ω) {a b : G} (hb : b ∉ Subgroup.center G)
    (haY : a ∈ centralizingLayer Ω {b}) (ha2 : orderOf a = 2)
    {r g : G} (hr : r ∈ involutionOddCore a ⊓ Subgroup.centralizer ({b} : Set G))
    (hg : g ∈ centralizingLayer Ω {b} ⊓ Subgroup.centralizer ({a} : Set G)) :
    ⁅r, g⁆ ∈ involutionOddCore b := by
  set Y : Subgroup G := centralizingLayer Ω {b} with hY
  set R : Subgroup G := involutionOddCore a ⊓ Subgroup.centralizer ({b} : Set G) with hR
  have hYb : Y ≤ Subgroup.centralizer ({b} : Set G) := centralizingLayer_le_centralizer Ω {b}
  have hgY : g ∈ Y := hg.1
  have hga : g ∈ Subgroup.centralizer ({a} : Set G) := hg.2
  have hRconj : ∀ u ∈ Subgroup.centralizer ({a} : Set G),
      u ∈ Subgroup.centralizer ({b} : Set G) → ∀ x ∈ R, u * x * u⁻¹ ∈ R := by
    intro u hua hub x hx
    exact ⟨conj_mem_oddCoreIn hua hx.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hub hx.2) (Subgroup.inv_mem _ hub)⟩
  have hrCb : r ∈ Subgroup.centralizer ({b} : Set G) := hr.2
  have hgCb : g ∈ Subgroup.centralizer ({b} : Set G) := hYb hgY
  have hcommR : ⁅r, g⁆ ∈ R := by
    have h1 : g * r⁻¹ * g⁻¹ ∈ R := hRconj g hga hgCb r⁻¹ (R.inv_mem hr)
    have : ⁅r, g⁆ = r * (g * r⁻¹ * g⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact R.mul_mem hr h1
  have hcommY : ⁅r, g⁆ ∈ Y := by
    have : ⁅r, g⁆ = (r * g * r⁻¹) * g⁻¹ := by
      simp only [commutatorElement_def]
    rw [this]
    exact Y.mul_mem (conj_mem_centralizingLayer hΩ hrCb hgY) (Y.inv_mem hgY)
  have hRY : (R ⊓ Y) ≤ oddCoreIn (Y ⊓ Subgroup.centralizer ({a} : Set G)) := by
    refine le_oddCoreIn_of_normalizes ?_ ?_ ?_
    · intro x hx
      exact ⟨hx.2, involutionOddCore_le_centralizer a hx.1.1⟩
    · intro u hu
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hub : u ∈ Subgroup.centralizer ({b} : Set G) := hYb hu.1
      have hub' : u⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := Subgroup.inv_mem _ hub
      have hua' : u⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := Subgroup.inv_mem _ hu.2
      constructor
      · rintro ⟨hyR, hyY⟩
        exact ⟨hRconj u hu.2 hub y hyR, conj_mem_centralizingLayer hΩ hub hyY⟩
      · rintro ⟨hyR, hyY⟩
        have h1 := hRconj u⁻¹ hua' hub' _ hyR
        have h2 := conj_mem_centralizingLayer hΩ hub' hyY
        simp only [mul_assoc, inv_inv, inv_mul_cancel_left] at h1 h2 ⊢
        refine ⟨?_, ?_⟩
        · simpa [mul_assoc] using h1
        · simpa [mul_assoc] using h2
    · exact (odd_card_oddCoreIn (Subgroup.centralizer ({a} : Set G))).of_dvd_nat
        (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left))
  have h3 : ⁅r, g⁆ ∈ oddCoreIn Y := hO b hb a haY ha2 (hRY ⟨hcommR, hcommY⟩)
  exact oddCoreIn_centralizingLayer_le hΩ b h3

theorem weakBalanced_of_localOddCentralizer3 (hΩ : ConjInvariant Ω) (hO : LocalOddCentralizer3 Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAY : ∀ b ∈ A, b ≠ 1 → A ≤ centralizingLayer Ω {b})
    (hnc : ∀ b ∈ A, b ≠ 1 → b ∉ Subgroup.center G) : WeakBalanced A := by
  intro a ha ha1 b hb hb1
  rw [Subgroup.commutator_le]
  intro r hr g hg
  refine commutator_mem_involutionOddCore_of_localOddCentralizer3 hΩ hO (hnc b hb hb1)
    (hAY b hb hb1 ha) (orderOf_eq_prime (hA.2 a ha) ha1) hr ⟨hAY b hb hb1 hg, ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.is_comm.comm (⟨g, hg⟩ : A) ⟨a, ha⟩))

end WeakBalance

end CFSG.ClassicalInvolution.Q3
