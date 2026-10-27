module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EM01
public import CFSG.ClassicalInvolution.Asc77.AscThmA173
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34Basic

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7E
namespace Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

theorem _root_.CFSG.ClassicalInvolution.Hat2A7E.HM.le_of_forall_isSylow2In {G : Type} [Group G]
    [Finite G] {Ω : Set (Subgroup G)} (hΩ : HM Ω) {J M : Subgroup G} (hJ : J ∈ Ω)
    (hM : ∀ V : Subgroup G, IsSylow2In V J → V ≤ M) : J ≤ M := by
  obtain ⟨z, hz⟩ := hΩ.classical J hJ
  exact le_of_forall_isSylow2In_of_isPerfect
    (hz.perfect Uniform.MemberType.not_isSolvableType_twoA7) hM

end Asc77

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace AscThmA
open CFSG.ClassicalInvolution.Asc77.AscThmA
open CFSG CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.LocalCores
open scoped commutatorElement MatrixGroups
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem exists_sylow_mem_RSet [Finite G] (hΩ : HM Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    ∃ V : Subgroup G, IsSylow2In V K ∧ V ∈ RSet Ω ∧ z ∈ V := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := K)
    (IsPGroup.of_card (n := 0) (by simp)) bot_le
  have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
  have h8 : 8 ≤ Nat.card V := hΩ.eight_le_of_mem_RSet hVR
  exact ⟨V, hV, hVR, mem_of_uniqueInvolution hz hV.1 hV.2.1 (by omega)⟩

private theorem isPGroup_zpowers_mk [Finite G] {C V : Subgroup G} (hV : IsPGroup 2 V)
    (hVC : V ≤ C) {v : G}
    (hv : v ∈ V) : IsPGroup 2 (Subgroup.zpowers (⟨v, hVC hv⟩ : ↥C)) := by
  obtain ⟨n, hn⟩ := (hV.to_le (Subgroup.zpowers_le.mpr hv)).exists_card_eq
  refine IsPGroup.of_card (n := n) ?_
  rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← Nat.card_zpowers]
  exact hn

theorem le_or_commutator_le_oddCoreOf [Finite G] (hΩ : HM Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z)
    (N : Subgroup G) [N.Normal] :
    K ≤ N ∨ ⁅K, N ⊓ Subgroup.centralizer ({z} : Set G)⁆ ≤
      oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hKC : K ≤ C := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hw).symm
  obtain ⟨z', hz'⟩ := hΩ.classical K hK
  have hzsq : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'.orderOf_eq_two, pow_two] at this
  have hzne : z' ≠ 1 := by
    intro h
    have := hz'.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  obtain rfl : z' = z := (hz.unique z' hz'.mem hzsq).resolve_left hzne
  have hsubH : (K.subgroupOf C).IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
      ((CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hKC).mpr hz'.subnormal)
      Subgroup.IsSubnormal.top
  let π : ↥C →* ↥C ⧸ classicalInvolutionOddCore ↥C :=
    QuotientGroup.mk' (classicalInvolutionOddCore ↥C)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  let ψ : ↥K →* ↥((K.subgroupOf C).map π) :=
    (π.comp (Subgroup.inclusion hKC)).codRestrict ((K.subgroupOf C).map π)
      fun x => ⟨Subgroup.inclusion hKC x, x.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨(a : G), ha⟩, rfl⟩
  have hψker : ψ.ker = classicalInvolutionOddCore ↥K := by
    ext x
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    have h1 := CFSG.ComponentClassification.OddCore.subnormal_mem_iff hz'.subnormal (x : G) x.2
    have h2 : (π (Subgroup.inclusion hKC x) = 1) ↔
        (Subgroup.inclusion hKC x) ∈ classicalInvolutionOddCore ↥C :=
      QuotientGroup.eq_one_iff _
    constructor
    · intro h
      refine h1.mpr ⟨hKC x.2, ?_⟩
      exact h2.mp h
    · intro h
      obtain ⟨hup, h3⟩ := h1.mp h
      exact h2.mpr h3
  let e' : ↥((K.subgroupOf C).map π) ≃* ↥K ⧸ classicalInvolutionOddCore ↥K :=
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hψker)
  have hqs : CFSG.IsQuasisimple ↥((K.subgroupOf C).map π) :=
    CFSG.ComponentClassification.AS76b.Lemma34.isQuasisimple_of_open
      (CFSG.ComponentClassification.Components.quasisimple_of_equiv e' hz'.witness.1)
  have hcomp : CFSG.IsComponent ((K.subgroupOf C).map π) := ⟨hqs, hsubH.map hπs⟩
  have hNn : ((N.subgroupOf C).map π).Normal :=
    (Subgroup.Normal.subgroupOf (inferInstance : N.Normal) C).map π hπs
  rcases component_normal_subgroup hcomp hNn with h | h
  · left
    have hle : K.subgroupOf C ≤ N.subgroupOf C ⊔ classicalInvolutionOddCore ↥C := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := h (Subgroup.mem_map_of_mem π hx)
      have h5 : y⁻¹ * x ∈ classicalInvolutionOddCore ↥C := by
        have : π y = π x := hyx
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
        exact this
      have h6 : x = y * (y⁻¹ * x) := by group
      rw [h6]
      exact Subgroup.mul_mem_sup hy h5
    refine hΩ.le_of_forall_isSylow2In hK fun V hV v hv => ?_
    have hv' : (⟨v, hKC (hV.1 hv)⟩ : ↥C) ∈ K.subgroupOf C := hV.1 hv
    exact mem_of_isPGroup_of_mem_sup_of_odd (CFSG.ComponentClassification.OddCore.odd_card ↥C)
      (isPGroup_zpowers_mk hV.2.1 (hV.1.trans hKC) hv) (hle hv')
  · right
    refine Subgroup.commutator_le.mpr fun k hk y hy => ?_
    have h1 : ⁅π ⟨k, hKC hk⟩, π ⟨y, hy.2⟩⁆ ∈
        ⁅(K.subgroupOf C).map π, (N.subgroupOf C).map π⁆ :=
      Subgroup.commutator_mem_commutator
        (Subgroup.mem_map_of_mem π (show _ ∈ K.subgroupOf C from hk))
        (Subgroup.mem_map_of_mem π (show _ ∈ N.subgroupOf C from hy.1))
    rw [h, Subgroup.mem_bot, ← map_commutatorElement, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    have hkyC : ⁅k, y⁆ ∈ C := by
      rw [commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem (hKC hk) hy.2) (C.inv_mem (hKC hk))) (C.inv_mem hy.2)
    exact mem_oddCoreOf_iff.mpr ⟨hkyC, h1⟩

theorem le_or_commutator_eq_bot_of_normal_component [Finite G] (hΩ : HM Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {N : Subgroup G} (hN : IsComponent N) (hNn : N.Normal)
    (hNz : N ≤ Subgroup.centralizer ({z} : Set G)) : K ≤ N ∨ ⁅K, N⁆ = ⊥ := by
  rcases le_or_commutator_le_oddCoreOf hΩ hK hz N with h | h
  · exact Or.inl h
  · right
    rw [inf_eq_left.mpr hNz] at h
    refine commutator_eq_bot_of_le_oddCoreOf_component hN hNn ?_
    have h1 : ⁅K, N⁆ ≤ N := Subgroup.commutator_le_right K N
    have h2 : N ⊓ oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤ oddCoreOf N :=
      inf_le_oddCoreOf_of_le_normalizer
        (fun g hg => mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hNz hg)))
        ((oddCoreOf_odd_natCard _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    exact fun x hx => h2 ⟨h1 hx, h hx⟩

end AscThmA
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace AscThmA
open CFSG.ClassicalInvolution.Asc77.AscThmA
open CFSG CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.LocalCores
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem thmA_on [Finite G] (hΩ : HM Ω)
    (h613 : Comm613On Ω) {K : Subgroup G} (hK : K ∈ Ω) {L : Subgroup G} (hL : IsComponent L)
    {k : G} (hk : k ∈ K) : conjSub k L = L := by
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
  have hEn : (layer G).Normal := normal_layer
  by_cases hzE : z ∈ layer G
  · rcases le_or_commutator_le_oddCoreOf hΩ hK hz (layer G) with hKE | hcomm
    · exact mem_normalizer_iff_conjSub_eq.mp (layer_le_normalizer hL (hKE hk))
    · by_contra hne
      have hL' : IsComponent (conjSub k L) := isComponent_conjSub hL k
      have hLc : ⁅L, conjSub k L⁆ = ⊥ := by
        rcases distinct_components_commute hL hL' with h | h
        · exact absurd h.symm hne
        · exact h
      have hLk : ∀ y ∈ L, ∀ w ∈ conjSub k L, y * w = w * y := fun y hy w hw =>
        (Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLc hy) w hw).symm
      obtain ⟨x, hx⟩ := exists_layerMul_eq hzE
      set a : G := (x ⟨L, hL⟩ : G) with ha
      have haL : a ∈ L := (x ⟨L, hL⟩).2
      have hacom : Commute a z := by
        rw [← hx]
        exact (commute_layerMul_iff x ⟨L, hL⟩ haL).mpr (Commute.refl a)
      have haEH : a ∈ layer G ⊓ Subgroup.centralizer ({z} : Set G) :=
        ⟨component_le_layer hL haL, Subgroup.mem_centralizer_singleton_iff.mpr hacom.eq⟩
      have ha2 : ∀ y ∈ L, y * (a * a) = (a * a) * y := by
        intro y hy
        have hz2 : layerMul G (x * x) = 1 := by
          rw [map_mul, hx]
          exact hz.sq
        have h1 : Commute y (layerMul G (x * x)) := by rw [hz2]; exact Commute.one_right y
        exact ((commute_layerMul_iff (x * x) ⟨L, hL⟩ hy).mp h1).eq
      have hka := hcomm (Subgroup.commutator_mem_commutator hk haEH)
      have hbL : ∀ y ∈ L, y * (k * a * k⁻¹) = (k * a * k⁻¹) * y := fun y hy =>
        hLk y hy _ (conj_mem_conjSub haL)
      have hcdef : ⁅k, a⁆ = (k * a * k⁻¹) * a⁻¹ := by rw [commutatorElement_def]
      set m : ℕ := orderOf ⁅k, a⁆ with hm
      have hmodd : Odd m :=
        (oddCoreOf_odd_natCard (Subgroup.centralizer ({z} : Set G))).of_dvd_nat
          (Subgroup.orderOf_dvd_natCard _ hka)
      have hba : Commute (k * a * k⁻¹) a := (hLk a haL _ (conj_mem_conjSub haL)).symm
      have hcomm_ba : Commute (k * a * k⁻¹) a⁻¹ := hba.inv_right
      have hpow : (k * a * k⁻¹) ^ m = a ^ m := by
        have h1 : ⁅k, a⁆ ^ m = 1 := pow_orderOf_eq_one _
        rw [hcdef, hcomm_ba.mul_pow, inv_pow] at h1
        exact mul_inv_eq_one.mp h1
      have ham : ∀ y ∈ L, y * a ^ m = a ^ m * y := by
        intro y hy
        rw [← hpow]
        exact ((show Commute y (k * a * k⁻¹) from hbL y hy).pow_right m).eq
      obtain ⟨j, hj⟩ := hmodd
      have hacen : ∀ y ∈ L, y * a = a * y := by
        intro y hy
        have h1 : Commute y (a ^ m) := ham y hy
        have h2 : Commute y ((a * a) ^ j) := ((show Commute y (a * a) from ha2 y hy).pow_right j)
        have h3 : a = ((a * a) ^ j)⁻¹ * a ^ m := by
          rw [hj, pow_succ, pow_mul, ← pow_two]
          group
        rw [h3]
        exact (h2.inv_right.mul_right h1).eq
      have hzL : ∀ y ∈ L, y * z = z * y := by
        intro y hy
        rw [← hx]
        exact ((commute_layerMul_iff x ⟨L, hL⟩ hy).mpr (hacen y hy)).eq
      have hLEH : L ≤ layer G ⊓ Subgroup.centralizer ({z} : Set G) := fun y hy =>
        ⟨component_le_layer hL hy, Subgroup.mem_centralizer_singleton_iff.mpr (hzL y hy)⟩
      have hk2 : ∀ y ∈ L, IsPGroup 2 (Subgroup.zpowers y) → k * y = y * k := by
        intro y hy hy2
        have hcy : ⁅k, y⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
          hcomm (Subgroup.commutator_mem_commutator hk (hLEH hy))
        have hby : Commute (k * y * k⁻¹) y⁻¹ :=
          ((show Commute y (k * y * k⁻¹) from hLk y hy _ (conj_mem_conjSub hy)).symm).inv_right
        have hby2 : IsPGroup 2 (Subgroup.zpowers (k * y * k⁻¹)) := by
          obtain ⟨n, hn⟩ := hy2.exists_card_eq
          refine IsPGroup.of_card (n := n) ?_
          have hord : orderOf (k * y * k⁻¹) = orderOf y := by
            have := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective y
            simpa using this
          rw [Nat.card_zpowers, hord, ← Nat.card_zpowers]
          exact hn
        have hyi2 : IsPGroup 2 (Subgroup.zpowers y⁻¹) := by
          rw [Subgroup.zpowers_inv]
          exact hy2
        have hc2 : IsPGroup 2 (Subgroup.zpowers ⁅k, y⁆) := by
          rw [commutatorElement_def]
          exact isPGroup_zpowers_mul hby hby2 hyi2
        have h1 := eq_one_of_isPGroup_of_mem_odd
          (oddCoreOf_odd_natCard (Subgroup.centralizer ({z} : Set G))) hcy hc2
        rw [commutatorElement_def] at h1
        calc k * y = (k * y * k⁻¹ * y⁻¹) * (y * k) := by group
          _ = y * k := by rw [h1, one_mul]
      have hLk' : L ≤ Subgroup.centralizer ({k} : Set G) := by
        refine le_of_forall_isSylow2In_of_isPerfect hL.1.1 fun V hV y hy => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hk2 y (hV.1 hy) (hV.2.1.to_le (Subgroup.zpowers_le.mpr hy))).symm
      have hkc : ∀ y ∈ L, k * y = y * k := fun y hy =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hLk' hy)).symm
      have hZL : Commutes (Subgroup.zpowers k) L := by
        intro a ha y hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        exact (Commute.zpow_left (show Commute k y from hkc y hy) n).eq
      exact hne (conjSub_eq_of_mem_of_commutes (Subgroup.mem_zpowers k) hZL)
  · have hV : ∀ V : Subgroup G, IsSylow2In V K → V ≤ Subgroup.centralizer (layer G : Set G) := by
      intro V hV
      have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
      have hVE : V ⊓ layer G = ⊥ :=
        inf_eq_bot_of_uniqueInvolution_not_mem hz hV.1 hV.2.1 hzE
      have h1 : ⁅V, layer G⁆ ≤ oddCoreOf (layer G) := h613 V hVR (layer G) hEn hVE
      have h2 : ⁅V, layer G⁆ = ⊥ :=
        commutator_eq_bot_of_le_oddCoreOf (𝒮 := {K | IsComponent K}) (fun B hB => hB) hEn h1
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
    have hKc : K ≤ Subgroup.centralizer (layer G : Set G) :=
      hΩ.le_of_forall_isSylow2In hK hV
    have hKL : Commutes K L := fun y hy w hw =>
      (Subgroup.mem_centralizer_iff.mp (hKc hy) w (component_le_layer hL hw)).symm
    exact conjSub_eq_of_mem_of_commutes hk hKL

end AscThmA
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace AscThmA
open CFSG.ClassicalInvolution.Asc77.AscThmA
open CFSG CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.LocalCores
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem mem_component_of_not_commutes [Finite G] (hΩ : HM Ω)
    (h613 : Comm613On Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {L : Subgroup G} (hL : IsComponent L) (hLn : L.Normal)
    (hnc : ¬ ∀ y ∈ L, y * z = z * y) : z ∈ L := by
  by_contra hzL
  obtain ⟨V, hV, hVR, hzV⟩ := exists_sylow_mem_RSet hΩ hK hz
  have hVL : V ⊓ L = ⊥ := inf_eq_bot_of_uniqueInvolution_not_mem hz hV.1 hV.2.1 hzL
  have h2 : ⁅V, L⁆ = ⊥ :=
    commutator_eq_bot_of_le_oddCoreOf_component hL hLn (h613 V hVR L hLn hVL)
  exact hnc fun y hy =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2 hzV) y hy

structure Hyp173 (Ω : Set (Subgroup G)) : Prop where
  hΩ : HM Ω
  h613 : Comm613On Ω
  thmA : ThmAOn Ω
  hsolv : ∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N = ⊥
  hgen : (⨆ J ∈ Ω, J) = ⊤

namespace Hyp173
open CFSG.ClassicalInvolution.Asc77.AscThmA.Hyp173
variable [Finite G] (S : Hyp173 Ω)
include S

theorem centralizer_layer : Subgroup.centralizer (layer G : Set G) = ⊥ :=
  centralizer_layer_eq_bot S.hsolv

omit [Finite G] in
theorem component_normal {L : Subgroup G} (hL : IsComponent L) : L.Normal :=
  normal_of_forall_le_normalizer S.hgen fun J hJ k hk =>
    mem_normalizer_iff_conjSub_eq.mpr (S.thmA J hJ L hL k hk)

theorem exists_normal_component {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) :
    ∃ L : Subgroup G, IsComponent L ∧ L.Normal ∧ z ∈ L ∧ ¬ ∀ y ∈ L, y * z = z * y := by
  obtain ⟨L, hL, hnc⟩ := exists_component_not_commute S.centralizer_layer hz.ne_one
  have hLn := S.component_normal hL
  exact ⟨L, hL, hLn, mem_component_of_not_commutes S.hΩ S.h613 hK hz hL hLn hnc, hnc⟩

theorem eq_one_of_central_in_component {L : Subgroup G} (hL : IsComponent L) {a : G} (ha : a ∈ L)
    (hcen : ∀ w ∈ L, w * a = a * w) : a = 1 := by
  have hle : layer G ≤ Subgroup.centralizer ({a} : Set G) := by
    refine sSup_le fun M hM y hy => Subgroup.mem_centralizer_singleton_iff.mpr ?_
    by_cases hML : M = L
    · subst hML
      exact hcen y hy
    · exact mul_comm_of_ne hM hL hML hy ha
  have hmem : a ∈ Subgroup.centralizer (layer G : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  rw [S.centralizer_layer, Subgroup.mem_bot] at hmem
  exact hmem

theorem commutes_of_not_mem {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z t : G}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) {L : Subgroup G}
    (hL : IsComponent L) (hzL : z ∈ L) (hnc : ¬ ∀ y ∈ L, y * z = z * y) (htL : t ∉ L) :
    Commutes K J := by
  have hLn : L.Normal := S.component_normal hL
  obtain ⟨L', hL', hL'n, htL', -⟩ := S.exists_normal_component hJ ht
  have hne : L ≠ L' := fun h => htL (h ▸ htL')
  have htc : ∀ y ∈ L, y * t = t * y := fun y hy => mul_comm_of_ne hL hL' hne hy htL'
  have hzL' : z ∉ L' := fun h => hnc fun y hy => mul_comm_of_ne hL hL' hne hy h
  have hLle : L ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (htc x hx)
  have hJL : ∀ y ∈ J, ∀ x ∈ L, y * x = x * y := by
    rcases le_or_commutator_eq_bot_of_normal_component S.hΩ hJ ht hL hLn hLle with h | h
    · exact absurd (h ht.mem) htL
    · intro y hy x hx
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hy) x hx).symm
  have hL'le : L' ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_comm_of_ne hL' hL hne.symm hx hzL)
  have hKL' : ∀ y ∈ K, ∀ x ∈ L', y * x = x * y := by
    rcases le_or_commutator_eq_bot_of_normal_component S.hΩ hK hz hL' hL'n hL'le with
      h | h
    · exact absurd (h hz.mem) hzL'
    · intro y hy x hx
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hy) x hx).symm
  have hKJ : K ≠ J := by
    intro h
    subst h
    exact htL (hz.eq ht ▸ hzL)
  have hJz : J ≤ Subgroup.centralizer ({z} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hJL y hy z hzL)
  have hKt : K ≤ Subgroup.centralizer ({t} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hKL' y hy t htL')
  have hJN : J ≤ Subgroup.normalizer (K : Set G) := by
    refine S.hΩ.le_of_forall_isSylow2In hJ fun V hV => ?_
    have h8 := S.hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hJ hV)
    exact S.hΩ.le_normalizer_of_le_centralizer hK hJ hKJ hz hV.1 hV.2.1 (by omega)
      (hV.1.trans hJz)
  have hKN : K ≤ Subgroup.normalizer (J : Set G) := by
    refine S.hΩ.le_of_forall_isSylow2In hK fun V hV => ?_
    have h8 := S.hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hK hV)
    exact S.hΩ.le_normalizer_of_le_centralizer hJ hK hKJ.symm ht hV.1 hV.2.1 (by omega)
      (hV.1.trans hKt)
  have hKJbot : K ⊓ J = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwK, hwJ⟩ := Subgroup.mem_inf.mp hw
    have hle : layer G ≤ Subgroup.centralizer ({w} : Set G) := by
      refine sSup_le fun M hM y hy => Subgroup.mem_centralizer_singleton_iff.mpr ?_
      by_cases hML : M = L
      · subst hML
        exact (hJL w hwJ y hy).symm
      · have hMn : M.Normal := S.component_normal hM
        have hMz : ∀ y ∈ M, y * z = z * y := fun y hy => mul_comm_of_ne hM hL hML hy hzL
        have hMle : M ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
          Subgroup.mem_centralizer_singleton_iff.mpr (hMz x hx)
        rcases le_or_commutator_eq_bot_of_normal_component S.hΩ hK hz hM hMn hMle with
          h | h
        · exact absurd (fun y hy => mul_comm_of_ne hL hM (Ne.symm hML) hy (h hz.mem)) hnc
        · exact Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hwK) y hy
    have hmem : w ∈ Subgroup.centralizer (layer G : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
    rw [S.centralizer_layer, Subgroup.mem_bot] at hmem
    exact hmem
  intro x hx y hy
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ K ⊓ J := by
    constructor
    · have h2 : y * x⁻¹ * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hJN hy) x⁻¹).mp (K.inv_mem hx)
      have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [this]
      exact K.mul_mem hx h2
    · have h2 : x * y * x⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hKN hx) y).mp hy
      exact J.mul_mem h2 (J.inv_mem hy)
  rw [hKJbot, Subgroup.mem_bot] at h1
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

theorem simple_of_forall_mem {L : Subgroup G} (hL : IsComponent L)
    (hall : ∀ J ∈ Ω, ∀ t : G, IsUniqueInvolution J t → t ∈ L) :
    IsSimpleGroup ↥L ∧ Subgroup.centralizer (L : Set G) = ⊥ := by
  have hEL : layer G = L := by
    refine le_antisymm (sSup_le fun M hM => ?_) (component_le_layer hL)
    by_contra hML0
    have hML : M ≠ L := fun h => hML0 (h ▸ le_rfl)
    have hMn : M.Normal := S.component_normal hM
    have hJM : ∀ J ∈ Ω, J ≤ Subgroup.centralizer (M : Set G) := by
      intro J hJ
      obtain ⟨t, ht⟩ := S.hΩ.exists_uniqueInvolution hJ
      have htL : t ∈ L := hall J hJ t ht
      have hMle : M ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (mul_comm_of_ne hM hL hML hx htL)
      rcases le_or_commutator_eq_bot_of_normal_component S.hΩ hJ ht hM hMn hMle with
        h | h
      · exfalso
        have htM : t ∈ M := h ht.mem
        exact ht.ne_one (S.eq_one_of_central_in_component hL htL fun w hw =>
          mul_comm_of_ne hL hM (Ne.symm hML) hw htM)
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer (M : Set G) := by
      rw [← S.hgen]
      exact iSup₂_le hJM
    have hM1 : M = ⊥ := by
      have hperf : ⁅M, M⁆ = M := Subgroup.isPerfect_iff.mp hM.1.1
      rw [← hperf, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      intro x hx
      exact htop (Subgroup.mem_top x)
    have : Nontrivial ↥M := isQuasisimple_nontrivial hM.1
    exact (Subgroup.nontrivial_iff_ne_bot M).mp this hM1
  have hC : Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [← hEL]
    exact S.centralizer_layer
  refine ⟨?_, hC⟩
  have hZ : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx1 : (x : G) = 1 := S.eq_one_of_central_in_component hL x.2 fun w hw =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨w, hw⟩)
    rw [Subgroup.mem_bot]
    exact Subtype.ext hx1
  have e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  exact e.symm.isSimpleGroup

theorem l17_3 {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    ∃ L : Subgroup G, IsComponent L ∧ L.Normal ∧ z ∈ L ∧
      (∀ J ∈ Ω, ∀ t : G, IsUniqueInvolution J t → t ∉ L → Commutes K J) ∧
      (((∀ J ∈ Ω, ∃ g : G, conjSub g K = J) ∨
          ∀ J ∈ Ω, ∀ t : G, IsUniqueInvolution J t → t ∈ L) →
        IsSimpleGroup ↥L ∧ Subgroup.centralizer (L : Set G) = ⊥) := by
  obtain ⟨L, hL, hLn, hzL, hnc⟩ := S.exists_normal_component hK hz
  refine ⟨L, hL, hLn, hzL,
    fun J hJ t ht htL => S.commutes_of_not_mem hK hJ hz ht hL hzL hnc htL, ?_⟩
  rintro (htrans | hall)
  · refine S.simple_of_forall_mem hL fun J hJ t ht => ?_
    obtain ⟨g, rfl⟩ := htrans J hJ
    have h2 : t = g * z * g⁻¹ := ht.eq (hz.conj g)
    rw [h2]
    have := conj_mem_conjSub (n := g) hzL
    rwa [conjSub_eq_of_normal L g] at this
  · exact S.simple_of_forall_mem hL hall

end Hyp173
end AscThmA
end Asc77
end
namespace Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

theorem e17_3_simple {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} (hΩ : HM Ω)
    (hsolv : ∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    (hgen : (⨆ J ∈ Ω, J) = ⊤) {K : Subgroup G} (hK : K ∈ Ω)
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) :
    ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
      Subgroup.centralizer (F : Set G) = ⊥ := by
  have h613 : AscThmA.Comm613On Ω := by
    intro R hR X hX hRX
    exact (l6_13_on hΩ (l6_7On_of_l6_7 l6_7_proved hΩ) R hR ⊤ X le_top le_top
      (fun y _ => AscThmA.conjSub_eq_of_normal X y) hRX).2
  have S : AscThmA.Hyp173 Ω :=
    ⟨hΩ, h613, fun J hJ L hL k hk => AscThmA.thmA_on hΩ h613 hJ hL hk, hsolv, hgen⟩
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
  obtain ⟨L, hL, hLn, -, -, h3⟩ := S.l17_3 hK hz
  obtain ⟨hs, hC⟩ := h3 (Or.inl htrans)
  refine ⟨L, hLn, hs, ?_, hC⟩
  by_contra hab
  push Not at hab
  have hQ : CFSG.IsQuasisimple ↥L := hL.1
  have hnt : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have hle : ⁅L, L⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_def, hab x hx y hy, mul_inv_cancel_right,
      mul_inv_cancel]
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hQ.1
  exact (Subgroup.nontrivial_iff_ne_bot L).mp hnt (le_bot_iff.mp (hperf ▸ hle))

end Asc77

end CFSG.ClassicalInvolution.Hat2A7E
