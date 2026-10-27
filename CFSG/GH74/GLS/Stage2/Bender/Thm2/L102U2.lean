module

public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Def
import CFSG.GH74.GLS.Stage2.Bender.Thm2.L102Simple
import CFSG.ClassicalInvolution.Balance.Layer
public import CFSG.Open.OrderForm

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L102

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS
open scoped commutatorElement

private theorem isQuasisimple_of_isTwoComponent_bar (hB2 : B_B2_g4) {B : Type} [Group B] [Finite B]
    (hK : IsKGroupNative B) (hg : Gen4 B) {z : B} (hz : orderOf z = 2)
    (M : Subgroup ↥(centralizer ({TwoThin.barMk B z} : Set (TwoThin.barQ B))))
    (hM : CFSG.ComponentClassification.TwoComponents.IsTwoComponent M) :
    CFSG.Open.IsQuasisimple M := by
  have hX : IsKGroupNative (TwoThin.barQ B) :=
    isKGroupNative_of_surjective hK ⊤ ((TwoThin.barMk B).comp (⊤ : Subgroup B).subtype)
      (TwoThin.barMk_surjective.comp fun m => ⟨⟨m, trivial⟩, rfl⟩)
  have hg4 : Gen4 (TwoThin.barQ B) := Gen4.quotient _ hg
  have hcore : pPrimeCore 2 (TwoThin.barQ B) = ⊥ := by
    have := TwoThin.oddCore_barQ (Y := B)
    rwa [← CFSG.ComponentClassification.CatalogueBAlternating.primeCore_two_eq_oddCore] at this
  have hc := isComponent_of_B2' hB2 hg4 hX hcore (TwoThin.orderOf_barMk hz) M
    ((CFSG.ComponentClassification.CatalogueBAlternating.pComponent_two_iff M).mpr hM)
  exact CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp hc.1

private theorem subgroupOf_le_twoLayer {B : Type} [Group B] [Finite B] {z t : B} (ht : orderOf t = 2)
    (hzt : z * t = t * z) {J : Subgroup B}
    (hJle : J ≤ centralizer ({z} : Set B) ⊓ centralizer ({t} : Set B)) (hJperf : ⁅J, J⁆ = J)
    (hJsub : (J.subgroupOf (centralizer ({z} : Set B) ⊓ centralizer ({t} : Set B))).IsSubnormal)
    (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J)) :
    J.subgroupOf (centralizer ({z} : Set B)) ≤
      CFSG.ComponentClassification.TwoLayer.subgroup ↥(centralizer ({z} : Set B)) := by
  set W : Subgroup B := centralizer ({z} : Set B)
  set D : Subgroup B := centralizer ({z} : Set B) ⊓ centralizer ({t} : Set B)
  have hJW : J ≤ W := hJle.trans inf_le_left
  have htW : t ∈ W := Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  set x : ↥W := ⟨t, htW⟩
  have hx2 : orderOf x = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hA : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hx2)
  have hcentA : centralizer ((zpowers x : Subgroup ↥W) : Set ↥W) = D.subgroupOf W := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      TwoThin.centralizer_singleton_eq_subgroupOf htW, inf_comm]
  have hLA : J.subgroupOf W ≤ centralizer ((zpowers x : Subgroup ↥W) : Set ↥W) := by
    rw [hcentA]
    exact fun y hy => hJle hy
  have hLsub : CFSG.Open.IsSubnormal (J.subgroupOf W)
      (centralizer ((zpowers x : Subgroup ↥W) : Set ↥W)) := by
    have h1 : CFSG.Open.IsSubnormal (J.subgroupOf D) ⊤ :=
      CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hJsub
    have h2 : CFSG.Open.IsSubnormal J D :=
      (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hJle).mp h1
    have h3 := CFSG.ComponentClassification.LBalance.subnormal_subgroupOf h2 W
    rwa [← hcentA] at h3
  have hJperf' : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJperf
  let e : ↥(J.subgroupOf W) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJW
  have hLperf' : Group.IsPerfect ↥(J.subgroupOf W) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hLperf : commutator ↥(J.subgroupOf W) = ⊤ := Group.IsPerfect.commutator_eq_top
  have hq1 : CFSG.IsQuasisimple (↥(J.subgroupOf W) ⧸ pPrimeCore 2 ↥(J.subgroupOf W)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (CFSG.ComponentClassification.UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e).symm
      hJq
  have hq2 : CFSG.Open.IsQuasisimple
      (↥(J.subgroupOf W) ⧸ CFSG.Open.componentClassificationOddCore ↥(J.subgroupOf W)) := by
    have h := CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp hq1
    have key : ∀ (R : Subgroup ↥(J.subgroupOf W)) [R.Normal],
        R = CFSG.Open.componentClassificationOddCore ↥(J.subgroupOf W) →
        CFSG.Open.IsQuasisimple (↥(J.subgroupOf W) ⧸ R) →
        CFSG.Open.IsQuasisimple
          (↥(J.subgroupOf W) ⧸ CFSG.Open.componentClassificationOddCore ↥(J.subgroupOf W)) := by
      intro R _ hR
      subst hR
      exact id
    exact key _ (CFSG.ComponentClassification.CatalogueBAlternating.primeCore_two_eq_oddCore _) h
  exact CFSG.ClassicalInvolution.Balance.le_twoLayer_of_l2PrimeBalance
    CFSG.ClassicalInvolution.l2PrimeBalance hA hLA hLsub hLperf hq2

theorem commutator_oddCore_le_oddCore (hB2 : B_B2_g4) {B : Type} [Group B] [Finite B]
    (hK : IsKGroupNative B) (hg : Gen4 B) {z t : B} (hz : orderOf z = 2) (ht : orderOf t = 2)
    (hzt : z * t = t * z) {J : Subgroup B}
    (hJle : J ≤ centralizer ({z} : Set B) ⊓ centralizer ({t} : Set B)) (hJperf : ⁅J, J⁆ = J)
    (hJsub : (J.subgroupOf (centralizer ({z} : Set B) ⊓ centralizer ({t} : Set B))).IsSubnormal)
    (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J))
    {a : B} (ha : a ∈ pPrimeCoreOf 2 (centralizer ({z} : Set B))) {l : B} (hl : l ∈ J) :
    ⁅a, l⁆ ∈ pPrimeCore 2 B := by
  set W : Subgroup B := centralizer ({z} : Set B)
  have hJW : J ≤ W := hJle.trans inf_le_left
  have hLle := subgroupOf_le_twoLayer ht hzt hJle hJperf hJsub hJq
  have hLperf : ⁅J.subgroupOf W, J.subgroupOf W⁆ = J.subgroupOf W := by
    have hJperf' : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJperf
    let e : ↥(J.subgroupOf W) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJW
    have : Group.IsPerfect ↥(J.subgroupOf W) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Subgroup.commutator_eq_self
  obtain ⟨a', ha', rfl⟩ := ha
  have ha'' : a' ∈ CFSG.Open.componentClassificationOddCore ↥W := by
    rw [← CFSG.ComponentClassification.CatalogueBAlternating.primeCore_two_eq_oddCore]
    exact ha'
  have h := CFSG.ClassicalInvolution.Balance.map_commutatorElement_eq_one_of_le_twoLayer
    (TwoThin.barMkCentralizer hz) (TwoThin.barMkCentralizer_surjective hz)
    (TwoThin.odd_card_ker_barMkCentralizer hz) hLperf hLle
    (fun M hM => Or.inl (isQuasisimple_of_isTwoComponent_bar hB2 hK hg hz M hM)) ha''
    (l := ⟨l, hJW hl⟩) hl
  have h2 := congrArg Subtype.val h
  rw [TwoThin.barMkCentralizer_apply] at h2
  exact (QuotientGroup.eq_one_iff _).mp h2

theorem commutator_oddCore_le_oddCore' (hB2 : B_B2_g4) {G : Type} [Group G] [Finite G]
    {B₀ : Subgroup G} (hK : IsKGroupNative ↥B₀) (hg : Gen4 ↥B₀) {z t : G} (hzB : z ∈ B₀)
    (htB : t ∈ B₀) (hz : orderOf z = 2) (ht : orderOf t = 2) (hzt : z * t = t * z)
    {J : Subgroup G} (hJle : J ≤ B₀ ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G))
    (hJperf : ⁅J, J⁆ = J)
    (hJsub : (J.subgroupOf (B₀ ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G))).IsSubnormal)
    (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J))
    {a : G} (ha : a ∈ pPrimeCoreOf 2 (B₀ ⊓ centralizer ({z} : Set G))) {l : G} (hl : l ∈ J) :
    ⁅a, l⁆ ∈ pPrimeCoreOf 2 B₀ := by
  set D₀ : Subgroup G := B₀ ⊓ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) with hD₀
  set X₀ : Subgroup G := B₀ ⊓ centralizer ({z} : Set G) with hX₀
  have hJB : J ≤ B₀ := fun j hj => (hJle hj).1.1
  have hXB : X₀ ≤ B₀ := inf_le_left
  have hz' : orderOf (⟨z, hzB⟩ : ↥B₀) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have ht' : orderOf (⟨t, htB⟩ : ↥B₀) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hzt' : (⟨z, hzB⟩ : ↥B₀) * ⟨t, htB⟩ = ⟨t, htB⟩ * ⟨z, hzB⟩ := Subtype.ext hzt
  have hcz : centralizer ({(⟨z, hzB⟩ : ↥B₀)} : Set ↥B₀) = X₀.subgroupOf B₀ := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, hX₀, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨y.2, congrArg Subtype.val h⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  have hczt : centralizer ({(⟨z, hzB⟩ : ↥B₀)} : Set ↥B₀) ⊓
      centralizer ({(⟨t, htB⟩ : ↥B₀)} : Set ↥B₀) = D₀.subgroupOf B₀ := by
    ext y
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, hD₀, Subgroup.mem_inf,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y.2, congrArg Subtype.val h1⟩, congrArg Subtype.val h2⟩
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨Subtype.ext h1, Subtype.ext h2⟩
  have hJ'le : J.subgroupOf B₀ ≤ centralizer ({(⟨z, hzB⟩ : ↥B₀)} : Set ↥B₀) ⊓
      centralizer ({(⟨t, htB⟩ : ↥B₀)} : Set ↥B₀) := by
    rw [hczt]
    exact fun y hy => hJle hy
  let e : ↥(J.subgroupOf B₀) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJB
  have hJ'perf : ⁅J.subgroupOf B₀, J.subgroupOf B₀⁆ = J.subgroupOf B₀ := by
    have hJperf' : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJperf
    have : Group.IsPerfect ↥(J.subgroupOf B₀) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Subgroup.commutator_eq_self
  have hJ'sub : ((J.subgroupOf B₀).subgroupOf (centralizer ({(⟨z, hzB⟩ : ↥B₀)} : Set ↥B₀) ⊓
      centralizer ({(⟨t, htB⟩ : ↥B₀)} : Set ↥B₀))).IsSubnormal := by
    have h1 : CFSG.Open.IsSubnormal (J.subgroupOf D₀) ⊤ :=
      CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hJsub
    have h2 : CFSG.Open.IsSubnormal J D₀ :=
      (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hJle).mp h1
    have h3 := CFSG.ComponentClassification.LBalance.subnormal_subgroupOf h2 B₀
    rw [← hczt] at h3
    have h4 := (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hJ'le).mpr h3
    exact CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h4 .top
  have hJ'q : IsQuasisimple (↥(J.subgroupOf B₀) ⧸ pPrimeCore 2 ↥(J.subgroupOf B₀)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (CFSG.ComponentClassification.UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e).symm
      hJq
  have ha' : ∃ a' ∈ pPrimeCoreOf 2 (centralizer ({(⟨z, hzB⟩ : ↥B₀)} : Set ↥B₀)), (a' : G) = a := by
    rw [TwoThin.pPrimeCoreOf_eq_map_subgroupOf hXB, ← hcz] at ha
    exact ha
  obtain ⟨a', ha', rfl⟩ := ha'
  have h := commutator_oddCore_le_oddCore hB2 hK hg hz' ht' hzt' hJ'le hJ'perf hJ'sub hJ'q ha'
    (l := ⟨l, hJB hl⟩) hl
  exact ⟨_, h, rfl⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L102
