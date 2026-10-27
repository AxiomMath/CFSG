module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModel
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Layer
import CFSG.LocalAnalysis.OddStandard.AltStdSecHerCop

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84v_adjust {G : Type} [Group G] {L : Subgroup G} {γ l c : G} (hγ2 : γ * γ = 1)
    (hγN : γ ∈ normalizer (L : Set G)) (hl : l ∈ L) (hc : c ∈ centralizer (L : Set G))
    (hcomm : γ * (l * c) = (l * c) * γ)
    (hZ : ∀ y ∈ L, y ∈ centralizer (L : Set G) → Odd (orderOf y)) :
    ∃ w ∈ L, w ∈ centralizer (L : Set G) ∧ l * w ∈ centralizer ({γ} : Set G) := by
  have hγinv : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right hγ2
  have hγ2' : γ⁻¹ * γ⁻¹ = 1 := by rw [hγinv]; exact hγ2
  have hN : ∀ y ∈ L, γ * y * γ⁻¹ ∈ L := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hγN y).mp hy
  have hNC : ∀ y ∈ centralizer (L : Set G), γ * y * γ⁻¹ ∈ centralizer (L : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : γ⁻¹ * x * γ ∈ L := by
      have := hN x hx
      rwa [hγinv] at this ⊢
    have h1 : (γ⁻¹ * x * γ) * y = y * (γ⁻¹ * x * γ) := Subgroup.mem_centralizer_iff.mp hy _ hx'
    calc x * (γ * y * γ⁻¹) = γ * ((γ⁻¹ * x * γ) * y) * γ⁻¹ := by group
      _ = γ * (y * (γ⁻¹ * x * γ)) * γ⁻¹ := by rw [h1]
      _ = (γ * y * γ⁻¹) * x := by group
  set a : G := l⁻¹ * (γ * l * γ⁻¹) with ha
  have haL : a ∈ L := Subgroup.mul_mem _ (Subgroup.inv_mem _ hl) (hN l hl)
  have hcomm' : l⁻¹ * γ * l = c * γ * c⁻¹ := by
    have : γ * (l * c) = (l * c) * γ := hcomm
    calc l⁻¹ * γ * l = l⁻¹ * (γ * (l * c)) * c⁻¹ := by group
      _ = l⁻¹ * ((l * c) * γ) * c⁻¹ := by rw [this]
      _ = c * γ * c⁻¹ := by group
  have haC : a ∈ centralizer (L : Set G) := by
    have : a = c * (γ * c⁻¹ * γ⁻¹) := by
      calc a = (l⁻¹ * γ * l) * γ⁻¹ := by rw [ha]; group
        _ = (c * γ * c⁻¹) * γ⁻¹ := by rw [hcomm']
        _ = c * (γ * c⁻¹ * γ⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hc (hNC _ (Subgroup.inv_mem _ hc))
  have haodd : Odd (orderOf a) := hZ a haL haC
  have haγ : γ * a * γ⁻¹ = a⁻¹ := by
    calc γ * a * γ⁻¹ = (γ * l⁻¹ * γ⁻¹) * ((γ * γ) * l * (γ⁻¹ * γ⁻¹)) := by rw [ha]; group
      _ = (γ * l⁻¹ * γ⁻¹) * (1 * l * 1) := by rw [hγ2, hγ2']
      _ = a⁻¹ := by rw [ha]; group
  obtain ⟨w, hw, hww, hwγ⟩ := CFSG.OddStandard.AltStdSec.exists_sq_root_inverted haodd haγ
  have hwL : w ∈ L := (Subgroup.zpowers_le.mpr haL) hw
  have hwC : w ∈ centralizer (L : Set G) := (Subgroup.zpowers_le.mpr haC) hw
  refine ⟨w, hwL, hwC, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hl' : γ * l * γ⁻¹ = l * (w * w) := by rw [hww, ha]; group
  have : γ * (l * w) * γ⁻¹ = l * w := by
    calc γ * (l * w) * γ⁻¹ = (γ * l * γ⁻¹) * (γ * w * γ⁻¹) := by group
      _ = l * (w * w) * w⁻¹ := by rw [hl', hwγ]
      _ = l * w := by group
  calc l * w * γ = (γ * (l * w) * γ⁻¹) * γ := by rw [this]
    _ = γ * (l * w) := by group

private theorem sec8t84v_odd_card_oddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem sec8t84v_odd_orderOf_of_mem_centralizer {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hL : IsOm6M L) {x : G} (hxL : x ∈ L) (hxc : x ∈ centralizer (L : Set G)) :
    Odd (orderOf x) := by
  have hx' : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (hxc a a.2)
  have hxO : (⟨x, hxL⟩ : ↥L) ∈ oddCore ↥L := by
    rw [← ff_center_eq_oddCore_six_minus hL]
    exact hx'
  have hdvd : orderOf (⟨x, hxL⟩ : ↥L) ∣ Nat.card (oddCore ↥L) :=
    (oddCore ↥L).orderOf_dvd_natCard hxO
  have hodd : Odd (orderOf (⟨x, hxL⟩ : ↥L)) :=
    (sec8t84v_odd_card_oddCore ↥L).of_dvd_nat hdvd
  rwa [Subgroup.orderOf_mk x hxL] at hodd

private theorem sec8t84v_oddCoreIn_le {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsOm6M L) : oddCoreIn L ≤ centralizer (L : Set G) := by
  intro o ho
  unfold oddCoreIn CFSG.inSubgroup at ho
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ho
  rw [← ff_center_eq_oddCore_six_minus hL] at ha
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha ⟨h, hh⟩)

private theorem sec8t84v_zpowers_facts {G : Type} [Group G] {γ b : G} (hγ2 : γ * γ = 1)
    (hb : b ∈ zpowers γ) : b * b = 1 ∧ ∀ y : G, y * γ = γ * y → b * y = y * b := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hγinv : γ⁻¹ = γ := inv_eq_of_mul_eq_one_right hγ2
  refine ⟨?_, fun y hy => ?_⟩
  · have hbinv : (γ ^ m)⁻¹ = γ ^ m := by rw [← inv_zpow, hγinv]
    calc γ ^ m * γ ^ m = (γ ^ m)⁻¹ * γ ^ m := by rw [hbinv]
      _ = 1 := inv_mul_cancel _
  · have hy' : Commute y γ := hy
    exact (Commute.zpow_right hy' m).eq.symm

theorem sec8t84v_inner_of_sq (hGi : Sec8T84FactGamInner) {G : Type} [Group G] [Finite G]
    {t γ : G} {L : Subgroup G} (hL : IsOm6M L) (hγ2 : γ * γ = 1)
    (hout : InducesOutsideGStar L 6 (-1) γ) (hγN : γ ∈ normalizer (L : Set G))
    (hdec : ∀ x ∈ centralizer ({t} : Set G), ∃ b ∈ zpowers γ, ∃ l ∈ L,
      ∃ c ∈ centralizer (L : Set G), x = b * l * c) :
    ∀ x ∈ centralizer ({γ} : Set G) ⊓ centralizer ({t} : Set G), x * x = 1 →
      InnerOn (layerCent L γ) x := by
  intro x hx hx2
  have hK0 : layerCent L γ ≤ L ⊓ centralizer ({γ} : Set G) := inSubgroup_le _ _
  have hK0L : layerCent L γ ≤ L := hK0.trans inf_le_left
  have hK0γ : layerCent L γ ≤ centralizer ({γ} : Set G) := hK0.trans inf_le_right
  obtain ⟨b, hb, l, hl, c, hc, hxe⟩ := hdec x hx.2
  obtain ⟨hbb, hbcomm⟩ := sec8t84v_zpowers_facts hγ2 hb
  have hbγ : b * γ = γ * b := hbcomm γ rfl
  have hxe' : x = b * (l * c) := by rw [hxe, mul_assoc]
  have hxγ : x * γ = γ * x := Subgroup.mem_centralizer_singleton_iff.mp hx.1
  have hyγ : l * c * γ = γ * (l * c) := by
    have h1 : b * (l * c * γ) = b * (γ * (l * c)) := by
      calc b * (l * c * γ) = (b * (l * c)) * γ := by group
        _ = γ * (b * (l * c)) := by rw [← hxe']; exact hxγ
        _ = (γ * b) * (l * c) := by group
        _ = (b * γ) * (l * c) := by rw [hbγ]
        _ = b * (γ * (l * c)) := by group
    exact mul_left_cancel h1
  have hby : b * (l * c) = (l * c) * b := hbcomm (l * c) hyγ
  have hyy : l * c * (l * c) = 1 := by
    calc l * c * (l * c) = (b * b) * (l * c * (l * c)) := by rw [hbb, one_mul]
      _ = b * (b * (l * c)) * (l * c) := by group
      _ = b * ((l * c) * b) * (l * c) := by rw [hby]
      _ = (b * (l * c)) * (b * (l * c)) := by group
      _ = 1 := by rw [← hxe']; exact hx2
  have hZ : ∀ y ∈ L, y ∈ centralizer (L : Set G) → Odd (orderOf y) :=
    fun y hy hyc => sec8t84v_odd_orderOf_of_mem_centralizer hL hy hyc
  obtain ⟨w, hwL, hwC, hlw⟩ := sec8t84v_adjust hγ2 hγN hl hc hyγ.symm hZ
  have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc l hl
  have hwl : l * w = w * l := Subgroup.mem_centralizer_iff.mp hwC l hl
  have hll : l * l = (c * c)⁻¹ := by
    have h1 : l * l * (c * c) = 1 := by
      calc l * l * (c * c) = l * (l * c) * c := by group
        _ = l * (c * l) * c := by rw [hcl]
        _ = l * c * (l * c) := by group
        _ = 1 := hyy
    exact eq_inv_of_mul_eq_one_left h1
  have hsq : l * w * (l * w) ∈ centralizer (L : Set G) := by
    have : l * w * (l * w) = (c * c)⁻¹ * (w * w) := by
      calc l * w * (l * w) = l * (w * l) * w := by group
        _ = l * (l * w) * w := by rw [hwl]
        _ = l * l * (w * w) := by group
        _ = (c * c)⁻¹ * (w * w) := by rw [hll]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hc hc))
      (Subgroup.mul_mem _ hwC hwC)
  have hcomm2 : ∀ y ∈ layerCent L γ, l * w * (l * w) * y = y * (l * w * (l * w)) := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hsq y (hK0L hy)).symm
  have hl'K : l * w ∈ layerCent L γ ⊔ oddCoreIn L :=
    hGi G L hL γ hγ2 hout (l * w) ⟨Subgroup.mul_mem _ hl hwL, hlw⟩ hcomm2
  have hK0le : (layerCent L γ : Set G) ⊆ L := fun y hy => hK0L hy
  have hcentle : centralizer (L : Set G) ≤ centralizer (layerCent L γ : Set G) :=
    Subgroup.centralizer_le hK0le
  have hb' : b ∈ centralizer (layerCent L γ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hbcomm z (Subgroup.mem_centralizer_singleton_iff.mp (hK0γ hz))).symm
  have hc' : w⁻¹ * c ∈ centralizer (layerCent L γ : Set G) :=
    hcentle (Subgroup.mul_mem _ (Subgroup.inv_mem _ hwC) hc)
  have hl'' : l * w ∈ layerCent L γ ⊔ centralizer (layerCent L γ : Set G) :=
    sup_le_sup_left ((sec8t84v_oddCoreIn_le hL).trans hcentle) _ hl'K
  have hxfin : x = b * ((l * w) * (w⁻¹ * c)) := by rw [hxe']; group
  unfold InnerOn
  rw [hxfin]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hb')
    (Subgroup.mul_mem _ hl'' (Subgroup.mem_sup_right hc'))

end CFSG.OddStandard.SmallF3.Omega
