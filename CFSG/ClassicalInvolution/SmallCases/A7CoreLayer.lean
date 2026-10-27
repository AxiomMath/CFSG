module

public import CFSG.ClassicalInvolution.SmallCases.A7CoreDiag
public import CFSG.ClassicalInvolution.SmallCases.A7CoreBasic

public section

namespace CFSG.ClassicalInvolution.A7Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ComponentClassification
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem le_normalizer_of_balance {u r : F} (hr2 : r * r = 1) (hr1 : r ≠ 1) (hur : u * r = r * u)
    {L : Subgroup F}
    (hLR : L ≤ Subgroup.centralizer ({r} : Set F) ⊓ Subgroup.centralizer ({u} : Set F))
    (hLsub : (L.subgroupOf (Subgroup.centralizer ({r} : Set F) ⊓
      Subgroup.centralizer ({u} : Set F))).IsSubnormal)
    (hLperf : ⁅L, L⁆ = L) (hLqs : CFSG.IsQuasisimple (L ⧸ CFSG.pPrimeCore 2 L))
    {I : Subgroup F} (hI : IsClassical2A7 ⊤ I u) : L ≤ Subgroup.normalizer (I : Set F) := by
  classical
  set Y : Subgroup F := Subgroup.centralizer ({u} : Set F) with hY
  set R : Subgroup F := Subgroup.centralizer ({r} : Set F) ⊓ Y with hR
  have hRY : R ≤ Y := inf_le_right
  have hLY : L ≤ Y := hLR.trans hRY
  have hIY : I ≤ Y := hI.le_centralizer
  have hrY : r ∈ Y := Subgroup.mem_centralizer_singleton_iff.mpr hur.symm
  set a₀ : ↥Y := ⟨r, hrY⟩ with ha₀
  have hA2 : IsPGroup 2 (Subgroup.zpowers a₀) :=
    isPGroup_zpowers_of_mul_self_eq_one (Subtype.ext hr2) (fun h => hr1 (congrArg Subtype.val h))
  have hcentA : Subgroup.centralizer ((Subgroup.zpowers a₀ : Subgroup ↥Y) : Set ↥Y) =
      R.subgroupOf Y := by
    ext x
    constructor
    · intro hx
      have h1 : a₀ * x = x * a₀ := Subgroup.mem_centralizer_iff.mp hx a₀ (Subgroup.mem_zpowers a₀)
      refine ⟨?_, x.2⟩
      show (x : F) ∈ Subgroup.centralizer ({r} : Set F)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val h1).symm
    · intro hx
      have hxr : (x : F) * r = r * (x : F) :=
        Subgroup.mem_centralizer_singleton_iff.mp hx.1
      have hcm : Commute a₀ x := Subtype.ext hxr.symm
      refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left hcm k).eq
  set LY : Subgroup ↥Y := L.subgroupOf Y with hLYdef
  have hLA : LY ≤ Subgroup.centralizer ((Subgroup.zpowers a₀ : Subgroup ↥Y) : Set ↥Y) := by
    rw [hcentA]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hLR (Subgroup.mem_subgroupOf.mp hx))
  have hLsubY : IsSubnormal LY
      (Subgroup.centralizer ((Subgroup.zpowers a₀ : Subgroup ↥Y) : Set ↥Y)) := by
    rw [hcentA]
    have h1 : IsSubnormal (L.subgroupOf R) ⊤ := Components.chain_of_mathlib_subnormal hLsub
    have h2 := Components.chain_map (Subgroup.inclusion hRY) h1
    have e1 : (L.subgroupOf R).map (Subgroup.inclusion hRY) = LY := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        have hxL : (x : F) ∈ L := hx
        exact ⟨⟨x, hLR hxL⟩, hxL, rfl⟩
    have e2 : (⊤ : Subgroup ↥R).map (Subgroup.inclusion hRY) = R.subgroupOf Y := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    rwa [e1, e2] at h2
  have e : ↥LY ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
  have hLperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
  have hLYperf : commutator ↥LY = ⊤ := by
    have : Group.IsPerfect ↥LY :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hLq0 : CFSG.Open.IsQuasisimple (↥L ⧸ componentClassificationOddCore ↥L) :=
    Components.quasisimple_of_equiv
      (QuotientGroup.quotientMulEquivOfEq
        (CatalogueBAlternating.primeCore_two_eq_oddCore ↥L).symm)
      (CatalogueBAlternating.quasisimple_iff_native.mp hLqs)
  have hLYq : CFSG.Open.IsQuasisimple (↥LY ⧸ componentClassificationOddCore LY) :=
    Components.quasisimple_of_equiv
      (QuotientGroup.congr (componentClassificationOddCore LY) (componentClassificationOddCore L)
        e (OddCore.equiv_invariant e)) hLq0
  have hLYlayer : LY ≤ TwoLayer.subgroup ↥Y :=
    Balance.le_twoLayer_of_l2PrimeBalance l2PrimeBalance hA2 hLA hLsubY hLYperf hLYq
  have hnorm : TwoLayer.subgroup ↥Y ≤
      Subgroup.normalizer ((I.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    refine sSup_le fun K' hK' => ?_
    by_cases hKI : K' = I.subgroupOf Y
    · rw [hKI]
      exact Subgroup.le_normalizer
    · exact (TwoComponentInteraction.mutual_normalization_core_commutation _ _ (isTwoComponent hI)
        hK' (Ne.symm hKI)).1
  intro g hg
  have hgY : g ∈ Y := hLY hg
  have h1 := hnorm (hLYlayer (show (⟨g, hgY⟩ : ↥Y) ∈ LY from hg))
  have h2 : (⟨g, hgY⟩ : ↥Y) ∈ (Subgroup.normalizer (I : Set F)).subgroupOf Y := by
    rw [Subgroup.subgroupOf_normalizer_eq hIY]
    exact h1
  exact Subgroup.mem_subgroupOf.mp h2

theorem diag_mem_normalizer {Q : Subgroup F} {r u : F} (hQ : IsClassical2A7 ⊤ Q r)
    (hu2 : u * u = 1) (hur : u * r = r * u) (hne : Q ≠ conjSub u Q) {I : Subgroup F}
    (hI : IsClassical2A7 ⊤ I u) {q : F} (hqQ : q ∈ Q) (hq2 : IsPGroup 2 (Subgroup.zpowers q))
    (hcomm : q * (u * q * u⁻¹) = (u * q * u⁻¹) * q) :
    q * (u * q * u⁻¹) ∈ Subgroup.normalizer (I : Set F) := by
  obtain ⟨L, hLM, hLfix, hLperf, hLqs, hLsub, hL2⟩ :=
    exists_twin_diagonal_two hQ hu2 hur hne
  obtain ⟨hQ'mem, -, -, -⟩ := twin_facts_a7 hQ hur hne
  have hr1 : r ≠ 1 := (isUniqueInvolution hQ).ne_one
  have hLR : L ≤ Subgroup.centralizer ({r} : Set F) ⊓ Subgroup.centralizer ({u} : Set F) := by
    intro x hx
    refine ⟨sup_le hQ.le_centralizer hQ'mem.le_centralizer (hLM hx), ?_⟩
    show x ∈ Subgroup.centralizer ({u} : Set F)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hLfix x hx
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  exact le_normalizer_of_balance (isUniqueInvolution hQ).sq hr1 hur hLR hLsub hLperf hLqs hI
    (hL2 q hqQ hq2 hcomm)

end CFSG.ClassicalInvolution.A7Core
