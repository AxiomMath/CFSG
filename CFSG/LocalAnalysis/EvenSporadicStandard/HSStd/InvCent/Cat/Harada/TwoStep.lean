module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.TwoCfg
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.AutBasic
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.Perfect
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Perm5
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Defs

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed
open CFSG.ComponentClassification.SolMax.FiveCat

section Main

variable {G : Type*} [Group G]

namespace TwoCfg

variable {t v : G} {J : Subgroup G} (h : TwoCfg t v J)

include h

theorem mul_self_of_mem_fourGroup {x : G} (hx : x ∈ fourGroup t v) : x * x = 1 := by
  rw [h.mem_fourGroup] at hx
  have htv := h.tv_comm
  rcases hx with rfl | rfl | rfl | rfl
  · simp
  · exact h.t_sq
  · exact h.hv
  · calc t * v * (t * v) = t * (v * t) * v := by group
      _ = t * (t * v) * v := by rw [← htv]
      _ = (t * t) * (v * v) := by group
      _ = 1 := by rw [h.t_sq, h.hv, one_mul]

theorem le_fourGroup_of_commute (htop : centralizer ({t} : Set G) ≠ ⊤) {c : G}
    (hc : c ∈ centralizer ({t} : Set G))
    (hcp : ∀ p ∈ centralizerDerived t, c * p = p * c) : c ∈ fourGroup t v := by
  obtain ⟨e⟩ := h.hJ
  have hc' := hc
  rw [h.hC] at hc'
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute h.hcomm).1 hc'
  have hPJ : ∀ b₀ : Equiv.Perm (Fin 5), b₀ ∈ alternatingGroup (Fin 5) →
      embJ J e b₀ ∈ centralizerDerived t := by
    intro b₀ hb₀
    rw [h.centralizerDerived_eq htop, commutator_eq_map_alt J e]
    exact ⟨b₀, hb₀, rfl⟩
  obtain ⟨b₀, rfl⟩ : ∃ b₀, embJ J e b₀ = b := (embJ_range J e).ge hb
  have hb1 : b₀ = 1 := by
    apply rhyp_perm5.eq_one_of_commute
    intro q hq
    have hp := hcp _ (hPJ q hq)
    have hqa : embJ J e q * a = a * embJ J e q := (h.hcomm a ha _ (embJ_mem J e q)).symm
    have h1 : a * (embJ J e b₀ * embJ J e q) = a * (embJ J e q * embJ J e b₀) := by
      calc a * (embJ J e b₀ * embJ J e q) = a * embJ J e b₀ * embJ J e q := by rw [mul_assoc]
        _ = embJ J e q * (a * embJ J e b₀) := hp
        _ = (embJ J e q * a) * embJ J e b₀ := by rw [mul_assoc]
        _ = (a * embJ J e q) * embJ J e b₀ := by rw [hqa]
        _ = a * (embJ J e q * embJ J e b₀) := by rw [mul_assoc]
    exact embJ_injective J e (by rw [map_mul, map_mul]; exact mul_left_cancel h1)
  rw [hb1, map_one, mul_one]
  exact ha

theorem centralizer_eq_of_mem_fourGroup {w : G} (hw : w ∈ fourGroup t v) (hw1 : w ≠ 1) :
    centralizer ({w} : Set G) = centralizer ({t} : Set G) := by
  rw [h.mem_fourGroup] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact absurd rfl hw1
  · rfl
  · exact h.hCv
  · exact h.hCtv

theorem fourGroup_le_of_two {S : Subgroup G} {d d' : G} (hd : d ∈ fourGroup t v)
    (hd' : d' ∈ fourGroup t v) (hd1 : d ≠ 1) (hd'1 : d' ≠ 1) (hdd' : d ≠ d') (hdS : d ∈ S)
    (hd'S : d' ∈ S) : fourGroup t v ≤ S := by
  intro x hx
  have key : t ∈ S ∧ v ∈ S := by
    rw [h.mem_fourGroup] at hd hd'
    rcases hd with rfl | rfl | rfl | rfl <;> rcases hd' with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hd1
      | exact absurd rfl hd'1
      | exact absurd rfl hdd'
      | exact ⟨hdS, hd'S⟩
      | exact ⟨hd'S, hdS⟩
      | exact ⟨hdS, by simpa using S.mul_mem (S.inv_mem hdS) hd'S⟩
      | exact ⟨hd'S, by simpa using S.mul_mem (S.inv_mem hd'S) hdS⟩
      | exact ⟨by simpa using S.mul_mem hdS (S.inv_mem hd'S), hd'S⟩
      | exact ⟨by simpa using S.mul_mem hd'S (S.inv_mem hdS), hdS⟩
  rw [h.mem_fourGroup] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact S.one_mem
  · exact key.1
  · exact key.2
  · exact S.mul_mem key.1 key.2

end TwoCfg


theorem derived_le_of_two {G : Type} [Group G] [Finite G] (h4 : CatCentFour)
    {S : Subgroup G} (hSn : S.Normal) (hS : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hcat : Blueprint.Catalog ↥S)
    (hcent : centralizer (S : Set G) = ⊥) {t v : G} {J : Subgroup G} (h : TwoCfg t v J) :
    centralizerDerived t ≤ S := by
  classical
  haveI := hSn
  have htop : centralizer ({t} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hcent h.t_ne_one
  by_contra hnot
  obtain ⟨e⟩ := h.hJ
  have hPeq : centralizerDerived t = (alternatingGroup (Fin 5)).map (embJ J e) := by
    rw [h.centralizerDerived_eq htop, commutator_eq_map_alt J e]
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := rhyp_perm5.simple
  haveI hPsimple : IsSimpleGroup ↥(centralizerDerived t) := by
    rw [hPeq]
    exact (Subgroup.equivMapOfInjective _ _ (embJ_injective J e)).symm.isSimpleGroup
  have hPS : ∀ x ∈ centralizerDerived t, x ∈ S → x = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.subgroupOf (centralizerDerived t))
      with hb | htp
    · intro x hx hxS
      have hmem : (⟨x, hx⟩ : ↥(centralizerDerived t)) ∈ S.subgroupOf (centralizerDerived t) :=
        hxS
      rw [hb, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exfalso
      apply hnot
      intro x hx
      have hmem : (⟨x, hx⟩ : ↥(centralizerDerived t)) ∈ S.subgroupOf (centralizerDerived t) := by
        rw [htp]
        exact Subgroup.mem_top _
      exact hmem
  have hD : ∀ d ∈ S, d * t = t * d → d ∈ fourGroup t v := by
    intro d hdS hdt
    have hdC : d ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hdt
    refine h.le_fourGroup_of_commute htop hdC (fun p hp => ?_)
    have hk1 : p * d * p⁻¹ * d⁻¹ ∈ S :=
      S.mul_mem (hSn.conj_mem d hdS p) (S.inv_mem hdS)
    have hk2 : p * d * p⁻¹ * d⁻¹ ∈ centralizerDerived t := by
      have := (centralizerDerived t).mul_mem hp
        (conj_mem_centralizerDerived hdC ((centralizerDerived t).inv_mem hp))
      simpa [mul_assoc] using this
    have hk : p * d * p⁻¹ * d⁻¹ = 1 := hPS _ hk2 hk1
    have hpd : p * d = d * p := by
      calc p * d = (p * d * p⁻¹ * d⁻¹) * d * p := by group
        _ = d * p := by rw [hk, one_mul]
    exact hpd.symm
  obtain ⟨d, hdS, hdt, hd1⟩ : ∃ d ∈ S, d * t = t * d ∧ d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, hab⟩ := hnab
    have hcomm := fixedPointFree_commute_of_mul_self_eq_one (W := S) h.t_sq
      (fun w hw => hSn.conj_mem w hw t) (fun w hw hwt => hcon w hw hwt.symm) a a.2 b b.2
    exact hab (Subtype.ext hcomm)
  have hdV : d ∈ fourGroup t v := hD d hdS hdt
  have hd2 : d * d = 1 := h.mul_self_of_mem_fourGroup hdV
  have hperf : Group.IsPerfect ↥S := isPerfect_of_simple_of_nonab hS (by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨a, a.2, b, b.2, fun h' => hab (Subtype.ext h')⟩)
  obtain ⟨d', hd'S, hd'V, hd'1, hdd'⟩ :
      ∃ d' ∈ S, d' ∈ fourGroup t v ∧ d' ≠ 1 ∧ d ≠ d' := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hxS, hxd, hxn⟩ := exists_commute_not_mem_zpowers hperf hdS hd2 hd1
    apply hxn
    have hxC : x ∈ centralizer ({t} : Set G) := by
      have hx' : x ∈ centralizer ({d} : Set G) := mem_centralizer_singleton_iff.2 hxd
      rwa [h.centralizer_eq_of_mem_fourGroup hdV hd1] at hx'
    have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 hxC
    have hxV := hD x hxS hxt
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    · rw [← hcon x hxS hxV hx1]
      exact mem_zpowers d
  have hVS : fourGroup t v ≤ S := h.fourGroup_le_of_two hdV hd'V hd1 hd'1 hdd' hdS hd'S
  have hcard : Nat.card ↥((fourGroup t v).subgroupOf S) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv]
    exact h.card_fourGroup htop
  have hcentV : ∀ w ∈ (fourGroup t v).subgroupOf S, w ≠ 1 →
      centralizer ({w} : Set ↥S) = (fourGroup t v).subgroupOf S := by
    intro w hw hw1
    have hwV : (w : G) ∈ fourGroup t v := hw
    have hw1' : (w : G) ≠ 1 := fun h' => hw1 (Subtype.ext h')
    have hCw := h.centralizer_eq_of_mem_fourGroup hwV hw1'
    ext x
    constructor
    · intro hx
      have hx' : (x : G) * (w : G) = (w : G) * (x : G) :=
        congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx)
      have hxC : (x : G) ∈ centralizer ({t} : Set G) := by
        rw [← hCw]
        exact mem_centralizer_singleton_iff.2 hx'
      exact hD x x.2 (mem_centralizer_singleton_iff.1 hxC)
    · intro hx
      have hxV : (x : G) ∈ fourGroup t v := hx
      have hxC : (x : G) ∈ centralizer ({(w : G)} : Set G) := by
        rw [hCw]
        exact h.fourGroup_le_centralizer hxV
      exact mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 hxC))
  obtain ⟨e5⟩ := h4 ↥S hS hnab hcat ((fourGroup t v).subgroupOf S) hcard hcentV
  have hSA : Nat.card (MulAut ↥S) = 120 := by
    rw [Nat.card_congr (MulAut.congr e5).toEquiv]
    exact card_mulAut_alternatingGroup_five
  have h1 := card_le_card_mulAut hcent
  have h2 : Nat.card (centralizer ({t} : Set G)) ≤ Nat.card G :=
    Nat.card_le_card_of_injective _ (Subgroup.subtype_injective _)
  have h3 := h.card_centralizer htop
  omega

theorem fivePumpOutcome_two {G : Type} [Group G] [Finite G] (hleaf : FivePumpLeaf)
    (h4 : CatCentFour) {S : Subgroup G} (hSn : S.Normal) (hS : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hcat : Blueprint.Catalog ↥S)
    (hcent : centralizer (S : Set G) = ⊥) {t v : G} {J : Subgroup G} (h : TwoCfg t v J) :
    FivePumpOutcome ↥S := by
  haveI := hSn
  refine fivePumpOutcome_of_derived hleaf hS hnab hcat hcent h.ht
    (derived_le_of_two h4 hSn hS hnab hcat hcent h) ?_
  obtain ⟨e⟩ := h.hJ
  have htop : centralizer ({t} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hcent h.t_ne_one
  rw [h.centralizerDerived_eq htop, commutator_eq_map_alt J e]
  exact ⟨(Subgroup.equivMapOfInjective _ _ (embJ_injective J e)).symm⟩

end Main

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
