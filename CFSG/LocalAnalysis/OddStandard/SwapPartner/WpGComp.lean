module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WPrimeShapeComponent
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGTypes
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLQuot

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm

namespace WreathCase

private theorem wp_isSubnormal_map_subgroupOf_centralizer
    {C : Type*} [Group C] (Z : Subgroup C) [Z.Normal] (hZc : Z ≤ Subgroup.center C) (u : C)
    {D' : Subgroup C} (hD' : D' ≤ centralizer ({u} : Set C))
    (hN : ∀ p ∈ centralizer ({u} : Set C), ∀ d ∈ D', p * d * p⁻¹ ∈ D') :
    ((D'.map (QuotientGroup.mk' Z)).subgroupOf
      (centralizer ({(QuotientGroup.mk u : C ⧸ Z)} : Set (C ⧸ Z)))).IsSubnormal := by
  let F : Subgroup (C ⧸ Z) := centralizer ({(QuotientGroup.mk u : C ⧸ Z)} : Set (C ⧸ Z))
  let M : Subgroup (C ⧸ Z) := (centralizer ({u} : Set C)).map (QuotientGroup.mk' Z)
  have hNM : (D'.map (QuotientGroup.mk' Z)) ≤ M := Subgroup.map_mono hD'
  have hMF : M ≤ F := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    show QuotientGroup.mk' Z p * QuotientGroup.mk' Z u
      = QuotientGroup.mk' Z u * QuotientGroup.mk' Z p
    rw [← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hp]
    rfl
  have hNc : ∀ m ∈ M, ∀ n ∈ D'.map (QuotientGroup.mk' Z),
      m * n * m⁻¹ ∈ D'.map (QuotientGroup.mk' Z) := by
    intro m hm n hn
    rw [Subgroup.mem_map] at hm hn ⊢
    obtain ⟨p, hp, rfl⟩ := hm
    obtain ⟨d, hd, rfl⟩ := hn
    exact ⟨p * d * p⁻¹, hN p hp d hd, by simp [map_mul]⟩
  have hMc : ∀ f ∈ F, ∀ m ∈ M, f * m * f⁻¹ ∈ M := by
    intro f hf m hm
    rw [Subgroup.mem_map] at hm ⊢
    obtain ⟨p, hp, rfl⟩ := hm
    obtain ⟨f', rfl⟩ := QuotientGroup.mk'_surjective Z f
    have hfcomm : QuotientGroup.mk' Z f' * QuotientGroup.mk' Z u
        = QuotientGroup.mk' Z u * QuotientGroup.mk' Z f' := by
      simpa only [QuotientGroup.mk'_apply] using Subgroup.mem_centralizer_singleton_iff.mp hf
    set s : C := f' * u * f'⁻¹ * u⁻¹ with hsdef
    have hsZ : s ∈ Z := by
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' Z s = 1
      rw [hsdef]
      simp only [map_mul, map_inv]
      rw [hfcomm]
      simp
    have hscenter : ∀ z : C, z * s = s * z := Subgroup.mem_center_iff.mp (hZc hsZ)
    have hscenter' : ∀ z : C, z * s⁻¹ = s⁻¹ * z := fun z =>
      Subgroup.mem_center_iff.mp
        ((Subgroup.center C).inv_mem (Subgroup.mem_center_iff.mpr hscenter)) z
    have hconj : f' * u * f'⁻¹ = s * u := by
      rw [hsdef]; group
    have hconj' : f'⁻¹ * u * f' = s⁻¹ * u := by
      have h1 : u = s * (f'⁻¹ * u * f') := by
        calc u = f'⁻¹ * (f' * u * f'⁻¹) * f' := by group
          _ = f'⁻¹ * (s * u) * f' := by rw [hconj]
          _ = f'⁻¹ * s * u * f' := by group
          _ = s * (f'⁻¹ * u * f') := by rw [hscenter (f'⁻¹)]; group
      have h2 : s⁻¹ * u = f'⁻¹ * u * f' := by
        have := congrArg (fun z => s⁻¹ * z) h1
        simpa using this
      exact h2.symm
    have hp' : p * u = u * p := Subgroup.mem_centralizer_singleton_iff.mp hp
    have hpu : (f' * p * f'⁻¹) * u * (f' * p * f'⁻¹)⁻¹ = u := by
      calc (f' * p * f'⁻¹) * u * (f' * p * f'⁻¹)⁻¹
          = f' * p * (f'⁻¹ * u * f') * p⁻¹ * f'⁻¹ := by group
        _ = f' * p * (s⁻¹ * u) * p⁻¹ * f'⁻¹ := by rw [hconj']
        _ = s⁻¹ * (f' * p * u * p⁻¹ * f'⁻¹) := by
              rw [show f' * p * (s⁻¹ * u) * p⁻¹ * f'⁻¹
                    = (f' * p) * s⁻¹ * (u * p⁻¹ * f'⁻¹) by group,
                  hscenter' (f' * p)]
              group
        _ = s⁻¹ * (f' * (p * u * p⁻¹) * f'⁻¹) := by group
        _ = s⁻¹ * (f' * u * f'⁻¹) := by
              rw [show p * u * p⁻¹ = u by rw [hp']; group]
        _ = s⁻¹ * (s * u) := by rw [hconj]
        _ = u := by group
    have hq : (f' * p * f'⁻¹) * u = u * (f' * p * f'⁻¹) :=
      mul_inv_eq_iff_eq_mul.mp hpu
    exact ⟨f' * p * f'⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr hq,
      by simp only [map_mul, map_inv]⟩
  exact isSubnormal_subgroupOf_of_chain hNM hMF hNc hMc

theorem card_le_altCentCard8_of_simpleNormalIn {G : Type} [Group G] [Finite G] {x : G}
    (hx : x * x = 1) {t : TwoSec x} {Sg V K : Subgroup (TwoSec x)}
    (hO : CFSG.pPrimeCore 2 (TwoSec x) = ⊥) (H : WreathCase t Sg V K)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) {c : G} (hc : c ∈ centralizer ({x} : Set G))
    (hc2 : c * c = 1)
    (hcN : (QuotientGroup.mk ⟨c, hc⟩ : TwoSec x) ∈ normalizer (K : Set (TwoSec x)))
    {D : Subgroup G} (hD : SimpleNormalIn c x D) :
    Nat.card D ≤ altCentCard8 (theta H e ⟨QuotientGroup.mk ⟨c, hc⟩, hcN⟩).1 ∨
      Nat.card D ≤ altCentCard8 (theta H e ⟨QuotientGroup.mk ⟨c, hc⟩, hcN⟩).2 := by
  let C0 : Subgroup G := centralizer ({x} : Set G)
  let Z : Subgroup C0 := zpowers (selfC x)
  let q : C0 →* TwoSec x := QuotientGroup.mk' Z
  let u : C0 := ⟨c, hc⟩
  let D' : Subgroup C0 := D.subgroupOf C0
  have hDleC : D ≤ C0 := fun d hd => (Subgroup.mem_inf.mp (hD.le hd)).2
  have hD'le : D' ≤ centralizer ({u} : Set C0) := by
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hdc : (d : G) ∈ centralizer ({c} : Set G) :=
      (Subgroup.mem_inf.mp (hD.le (Subgroup.mem_subgroupOf.mp hd))).1
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hdc
    simpa using hcomm
  have hN : ∀ p ∈ centralizer ({u} : Set C0), ∀ d ∈ D', p * d * p⁻¹ ∈ D' := by
    intro p hp d hd
    rw [Subgroup.mem_subgroupOf]
    have hpC : (p : G) ∈ centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := Subgroup.mem_centralizer_singleton_iff.mp hp
      simpa using congrArg Subtype.val h
    have hpX : (p : G) ∈ centralizer ({x} : Set G) := p.2
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
    have hmem := hD.normal (p : G) ⟨hpC, hpX⟩ (d : G) hdD
    simpa using hmem
  have hZc : Z ≤ Subgroup.center C0 := zpowers_le.mpr (selfC_mem_center x)
  have hsub : ((D'.map q).subgroupOf
      (centralizer ({(q u : TwoSec x)} : Set (TwoSec x)))).IsSubnormal :=
    wp_isSubnormal_map_subgroupOf_centralizer Z hZc u hD'le hN
  haveI : IsSimpleGroup D := hD.simple
  have hDnab : ∃ a b : D, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hD.nonab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (by simpa using congrArg Subtype.val h)⟩
  have hcenterD : Subgroup.center D = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hDnab).2
  have hinj : ∀ d1 d2 : D', q d1 = q d2 → d1 = d2 := by
    intro d1 d2 h
    let w : D' := d1 * d2⁻¹
    have h1 : q w = 1 := by
      show q (d1 * d2⁻¹) = 1
      rw [map_mul, Subgroup.coe_inv, map_inv, h, mul_inv_cancel]
    have hmem : (w : C0) ∈ Z := by
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' Z (w : C0) = 1
      exact h1
    have hcases := (mem_zpowers_selfC_iff hx).mp hmem
    have hgoal : w = 1 → d1 = d2 := by
      intro hw1
      calc d1 = w * d2 := by rw [show w = d1 * d2⁻¹ from rfl]; group
        _ = d2 := by rw [hw1]; simp
    rcases hcases with hone | hxeq
    · apply hgoal
      apply Subtype.ext
      exact Subtype.ext hone
    · apply hgoal
      let δ : D := ⟨((w : C0) : G), w.2⟩
      have hδval : (δ : G) = x := hxeq
      have hδcenter : δ ∈ Subgroup.center D := by
        rw [Subgroup.mem_center_iff]
        intro e
        apply Subtype.ext
        change (e : G) * (δ : G) = (δ : G) * (e : G)
        rw [hδval]
        have he : (e : G) ∈ centralizer ({x} : Set G) :=
          (Subgroup.mem_inf.mp (hD.le e.2)).2
        exact Subgroup.mem_centralizer_singleton_iff.mp he
      have hδ1 : δ = 1 := by
        have hmem' : δ ∈ (⊥ : Subgroup D) := hcenterD ▸ hδcenter
        simpa using hmem'
      apply Subtype.ext
      apply Subtype.ext
      show ((w : C0) : G) = 1
      have hδ1val : (δ : G) = 1 := congrArg (fun z : D => (z : G)) hδ1
      simpa [δ] using hδ1val
  have e1 : D' ≃* D := Subgroup.subgroupOfEquivOfLe hDleC
  have hcard1 : Nat.card D' = Nat.card D := Nat.card_congr e1.toEquiv
  let φ : D' →* D'.map q :=
    { toFun := fun d => ⟨q (d : C0), Subgroup.mem_map_of_mem q d.2⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun d1 d2 => Subtype.ext (map_mul q (d1 : C0) (d2 : C0)) }
  have hφ : Function.Bijective φ := by
    constructor
    · intro d1 d2 h
      exact hinj d1 d2 (Subtype.ext_iff.mp h)
    · intro y
      obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨d, hd⟩, Subtype.ext hdy⟩
  let e2 : D' ≃* D'.map q := MulEquiv.ofBijective φ hφ
  have hcard2 : Nat.card D' = Nat.card (D'.map q) := Nat.card_congr e2.toEquiv
  have eDDbar : D ≃* D'.map q := e1.symm.trans e2
  have hDquasi : CFSG.IsQuasisimple D :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hDnab).1
  have hDbarQuasi : CFSG.IsQuasisimple (D'.map q) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eDDbar hDquasi
  have hDbarSimple : IsSimpleGroup (D'.map q) := eDDbar.symm.isSimpleGroup
  have hDx : D'.map q ≤ centralizer ({(q u : TwoSec x)} : Set (TwoSec x)) := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc q d * q u = q (d * u) := (map_mul q d u).symm
      _ = q (u * d) := by rw [Subgroup.mem_centralizer_singleton_iff.mp (hD'le hd)]
      _ = q u * q d := map_mul q u d
  have hcomp : CFSG.IsComponent ((D'.map q).subgroupOf
      (centralizer ({(q u : TwoSec x)} : Set (TwoSec x)))) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hDx).symm hDbarQuasi, hsub⟩
  have hu2 : u * u = 1 := Subtype.ext hc2
  have hxbar2 : (q u : TwoSec x) * (q u : TwoSec x) = 1 := by
    rw [← map_mul, hu2, map_one]
  have hxbarN : (q u : TwoSec x) ∈ normalizer (K : Set (TwoSec x)) := by
    show (QuotientGroup.mk ⟨c, hc⟩ : TwoSec x) ∈ normalizer (K : Set (TwoSec x))
    exact hcN
  have hX := card_le_altCentCard8_of_isComponent_centralizer (X := TwoSec x)
    (t := t) (Sg := Sg) (V := V) (K := K) hO H e (x := (q u : TwoSec x))
    hxbar2 hxbarN hDx hcomp hDbarSimple
  have hcard : Nat.card (D'.map q) = Nat.card D := hcard2.symm.trans hcard1
  have htheta : (⟨(q u : TwoSec x), hxbarN⟩ : normalizer (K : Set (TwoSec x)))
      = ⟨QuotientGroup.mk ⟨c, hc⟩, hcN⟩ := Subtype.ext rfl
  rw [hcard, htheta] at hX
  exact hX

end WreathCase

end CFSG.OddStandard.AltStdSec.SwapPartner
