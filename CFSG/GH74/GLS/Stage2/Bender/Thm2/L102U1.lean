module

public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Def
import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Simple
import CFSG.ClassicalInvolution.Balance.Layer
public import CFSG.Open.OrderForm

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L102

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS
open scoped commutatorElement

theorem commutator_oddCore_centralizer_le (hB2 : B_B2_g4) {B : Type} [Group B] [Finite B]
    (hK : IsKGroupNative B) (hg : Gen4 B) {s : B} (hs : orderOf s = 2) {J : Subgroup B}
    (hJle : J ≤ centralizer ({s} : Set B)) (hJperf : ⁅J, J⁆ = J)
    (hJsub : (J.subgroupOf (centralizer ({s} : Set B))).IsSubnormal)
    (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J))
    {a : B} (ha : a ∈ pPrimeCoreOf 2 (centralizer ({s} : Set B))) {l : B} (hl : l ∈ J) :
    ⁅a, l⁆ ∈ pPrimeCore 2 B := by
  set C : Subgroup B := centralizer ({s} : Set B)
  set L : Subgroup ↥C := J.subgroupOf C with hL
  have hLperf : ⁅L, L⁆ = L := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, hL, Subgroup.map_subgroupOf_eq_of_le hJle, hJperf]
  have hLperf' : commutator ↥L = ⊤ := by
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
    exact Group.IsPerfect.commutator_eq_top
  have hLq : CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.Open.componentClassificationOddCore ↥L) := by
    let e : ↥L ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJle
    exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (QuotientGroup.congr (CFSG.Open.componentClassificationOddCore ↥L) (pPrimeCore 2 ↥J) e
        ((CFSG.ComponentClassification.OddCore.equiv_invariant e).trans
          (CFSG.ComponentClassification.CatalogueBAlternating.primeCore_two_eq_oddCore ↥J).symm))
      (CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp hJq)
  have hLsub : CFSG.Open.IsSubnormal L ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hJsub
  have hLlayer : L ≤ CFSG.ComponentClassification.TwoLayer.subgroup ↥C :=
    CFSG.ClassicalInvolution.Balance.le_twoLayer_of_perfect_of_isSubnormal hLsub hLperf' hLq
  have hKb : IsKGroupNative (TwoThin.barQ B) :=
    isKGroupNative_of_surjective (X := B) hK ⊤ ((TwoThin.barMk B).comp (⊤ : Subgroup B).subtype)
      (TwoThin.barMk_surjective.comp fun m => ⟨⟨m, trivial⟩, rfl⟩)
  have hcore : pPrimeCore 2 (TwoThin.barQ B) = ⊥ := by
    have := TwoThin.oddCore_barQ (Y := B)
    rwa [← CFSG.ComponentClassification.CatalogueBAlternating.primeCore_two_eq_oddCore] at this
  have hgb : Gen4 (TwoThin.barQ B) := Gen4.quotient _ hg
  have hsb : orderOf (TwoThin.barMk B s) = 2 := TwoThin.orderOf_barMk hs
  have hcomp := isComponent_of_B2' hB2 hgb hKb hcore hsb
  have hB : ∀ M : Subgroup ↥(centralizer ({TwoThin.barMk B s} : Set (TwoThin.barQ B))),
      CFSG.ComponentClassification.TwoComponents.IsTwoComponent M →
        CFSG.Open.IsQuasisimple M ∨ ⁅M, L.map (TwoThin.barMkCentralizer hs)⁆ = ⊥ := by
    intro M hM
    left
    have hM' : CFSG.IsPComponent 2 M :=
      (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_two_iff M).mpr hM
    exact CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp
      (hcomp M hM').1
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  have ha'' : a' ∈ CFSG.Open.componentClassificationOddCore ↥C := by
    rwa [← CFSG.ComponentClassification.CatalogueBAlternating.primeCore_two_eq_oddCore]
  have hl' : (⟨l, hJle hl⟩ : ↥C) ∈ L := Subgroup.mem_subgroupOf.mpr hl
  have key := CFSG.ClassicalInvolution.Balance.map_commutatorElement_eq_one_of_le_twoLayer
    (TwoThin.barMkCentralizer hs) (TwoThin.barMkCentralizer_surjective hs)
    (TwoThin.odd_card_ker_barMkCentralizer hs) hLperf hLlayer hB ha'' hl'
  have key2 := congrArg Subtype.val key
  rw [TwoThin.barMkCentralizer_apply] at key2
  rw [← QuotientGroup.eq_one_iff]
  simpa [commutatorElement_def] using key2

theorem commutator_oddCore_centralizer_le' (hB2 : B_B2_g4) {G : Type} [Group G] [Finite G]
    {B₀ : Subgroup G} (hK : IsKGroupNative ↥B₀) (hg : Gen4 ↥B₀) {s : G} (hsB : s ∈ B₀)
    (hs : orderOf s = 2) {J : Subgroup G} (hJle : J ≤ B₀ ⊓ centralizer ({s} : Set G))
    (hJperf : ⁅J, J⁆ = J)
    (hJsub : (J.subgroupOf (B₀ ⊓ centralizer ({s} : Set G))).IsSubnormal)
    (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J))
    {a : G} (ha : a ∈ pPrimeCoreOf 2 (B₀ ⊓ centralizer ({s} : Set G))) {l : G} (hl : l ∈ J) :
    ⁅a, l⁆ ∈ pPrimeCoreOf 2 B₀ := by
  set D : Subgroup G := B₀ ⊓ centralizer ({s} : Set G) with hD
  have hJB : J ≤ B₀ := hJle.trans inf_le_left
  set s' : ↥B₀ := ⟨s, hsB⟩
  have hs'2 : orderOf s' = 2 := by
    rw [← hs]
    exact Subgroup.orderOf_mk s hsB
  set J' : Subgroup ↥B₀ := J.subgroupOf B₀ with hJ'
  have hcen : centralizer ({s'} : Set ↥B₀) = D.subgroupOf B₀ := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, hD, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨x.2, congrArg Subtype.val h⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  let ψ : ↥(centralizer ({s'} : Set ↥B₀)) ≃* ↥D :=
    (MulEquiv.subgroupCongr hcen).trans (Subgroup.subgroupOfEquivOfLe inf_le_left)
  have hψ : ∀ x : ↥(centralizer ({s'} : Set ↥B₀)), ((ψ x : ↥D) : G) = ((x : ↥B₀) : G) :=
    fun x => rfl
  have hJle' : J' ≤ centralizer ({s'} : Set ↥B₀) := by
    rw [hcen]
    intro x hx
    exact hJle hx
  have hJperf' : ⁅J', J'⁆ = J' := by
    apply Subgroup.map_injective B₀.subtype_injective
    rw [Subgroup.map_commutator, hJ', Subgroup.map_subgroupOf_eq_of_le hJB, hJperf]
  have hJsub' : (J'.subgroupOf (centralizer ({s'} : Set ↥B₀))).IsSubnormal := by
    have h := hJsub.comap ψ.toMonoidHom
    convert h using 1
    ext x
    rfl
  have hJq' : IsQuasisimple (↥J' ⧸ pPrimeCore 2 ↥J') := by
    let e : ↥J' ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJB
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (CFSG.ComponentClassification.UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e).symm
      hJq
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp ha
  have hdB : (d : G) ∈ B₀ := d.2.1
  have ha₀ : (⟨(d : G), hdB⟩ : ↥B₀) ∈ pPrimeCoreOf 2 (centralizer ({s'} : Set ↥B₀)) := by
    refine Subgroup.mem_map.mpr ⟨ψ.symm d, ?_, ?_⟩
    · have h2 : d ∈ (pPrimeCore 2 ↥(centralizer ({s'} : Set ↥B₀))).map ψ.toMonoidHom := by
        rw [CFSG.pPrimeCore_map_iso 2 ψ]
        exact hd
      exact Subgroup.mem_map_equiv.mp h2
    · apply Subtype.ext
      have h3 := hψ (ψ.symm d)
      rw [ψ.apply_symm_apply] at h3
      exact h3.symm
  have key := commutator_oddCore_centralizer_le hB2 hK hg hs'2 hJle' hJperf' hJsub' hJq' ha₀
    (l := ⟨l, hJB hl⟩) (Subgroup.mem_subgroupOf.mpr hl)
  exact ⟨_, key, rfl⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L102
