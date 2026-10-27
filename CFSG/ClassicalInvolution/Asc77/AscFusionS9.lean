module

public import CFSG.ClassicalInvolution.Asc77.AscFusionS8

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups Pointwise

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K₀ : Subgroup G} {z₀ : G}

theorem diag_centralizes_of_bad (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h₀ : IsClassicalMember p f K₀ z₀) {Q : Subgroup G} {r u : G}
    (hQ : Q ∈ CoreAssembly.conjClass K₀) (hQr : IsUniqueInvolution Q r) (hu2 : u * u = 1)
    (hur : u * r = r * u) (hne : Q ≠ conjSub u Q) {I : Subgroup G}
    (hI : I ∈ CoreAssembly.conjClass K₀) (hIu : IsUniqueInvolution I u) {q : G} (hqQ : q ∈ Q)
    (hq2 : IsPGroup 2 (Subgroup.zpowers q))
    (hcomm : q * (u * q * u⁻¹) = (u * q * u⁻¹) * q)
    (hrI : r ∈ Subgroup.normalizer (I : Set G))
    (hbad : ∀ x ∈ I, orderOf x = 4 → r * x = x * r → False) :
    ∀ j ∈ I, ⁅q * (u * q * u⁻¹), j⁆ ∈ oddCoreOf I := by
  classical
  obtain ⟨L, hLM, hLfix, hLperf, hLqs, hLsub, -, hL2⟩ :=
    exists_twin_diagonal' hp2 hq h₀ hQ hQr hu2 hur hne
  have hg : q * (u * q * u⁻¹) ∈ L := hL2 q hqQ hq2 hcomm
  obtain ⟨hQ'mem, hQ'r, -, -, -⟩ := twin_facts_conj hp2 hq h₀ hQ hQr hur hne
  have hQmem : IsClassicalMember p f Q r := isClassicalMember_of_mem_conjClass hp2 hq h₀ hQ hQr
  have hQ'mem' : IsClassicalMember p f (conjSub u Q) r :=
    isClassicalMember_of_mem_conjClass hp2 hq h₀ hQ'mem hQ'r
  have hQHr : Q ≤ Subgroup.centralizer ({r} : Set G) := isSubnormal_le hQmem.subnormal
  have hQ'Hr : conjSub u Q ≤ Subgroup.centralizer ({r} : Set G) :=
    isSubnormal_le hQ'mem'.subnormal
  set Y : Subgroup G := Subgroup.centralizer ({u} : Set G) with hY
  set R : Subgroup G := Subgroup.centralizer ({r} : Set G) ⊓ Y with hR
  have hRY : R ≤ Y := inf_le_right
  have hLR : L ≤ R := by
    intro x hx
    refine ⟨sup_le hQHr hQ'Hr (hLM hx), ?_⟩
    show x ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hLfix x hx
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hLY : L ≤ Y := hLR.trans hRY
  have hImem : IsClassicalMember p f I u := isClassicalMember_of_mem_conjClass hp2 hq h₀ hI hIu
  have hIY : I ≤ Y := isSubnormal_le hImem.subnormal
  have hIcomp : TwoComponents.IsTwoComponent (I.subgroupOf Y) :=
    isTwoComponent_subgroupOf_of_perfect hImem.subnormal hImem.perfect.commutator_eq_top
      (isQuasisimple_oddQuot hq hImem)
  have hrY : r ∈ Y := Subgroup.mem_centralizer_singleton_iff.mpr hur.symm
  set a₀ : ↥Y := ⟨r, hrY⟩ with ha₀
  have hA2 : IsPGroup 2 (Subgroup.zpowers a₀) :=
    isPGroup_zpowers_of_mul_self_eq_one (Subtype.ext hQr.sq) (fun h => hQr.ne_one
      (congrArg Subtype.val h))
  have hcentA : Subgroup.centralizer ((Subgroup.zpowers a₀ : Subgroup ↥Y) : Set ↥Y) =
      R.subgroupOf Y := by
    ext x
    constructor
    · intro hx
      have h1 : a₀ * x = x * a₀ := Subgroup.mem_centralizer_iff.mp hx a₀ (Subgroup.mem_zpowers a₀)
      refine ⟨?_, x.2⟩
      show (x : G) ∈ Subgroup.centralizer ({r} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val h1).symm
    · intro hx
      have hxr : (x : G) * r = r * (x : G) :=
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
        have hxL : (x : G) ∈ L := hx
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
  have hLinner : ∀ x ∈ L, x ∈ Subgroup.normalizer (I : Set G) ∧
      ∃ b ∈ I, ∀ y ∈ I, x * y * x⁻¹ * (b * y * b⁻¹)⁻¹ ∈ oddCoreOf I := fun x hx =>
    layer_acts_inner_sub hIY hIcomp (hLY hx) (hLYlayer (show (⟨x, hLY hx⟩ : ↥Y) ∈ LY from hx))
  have hLz : ∀ x ∈ L, r * x = x * r := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLR hx).1).symm
  have hall := perfect_trivial_of_bad hp2 hq hImem hQr.sq hrI hbad hLperf
    (fun x hx => (hLinner x hx).1) hLz (fun x hx => (hLinner x hx).2)
  exact hall _ hg

end CFSG.ClassicalInvolution.Asc77.AscFusion
