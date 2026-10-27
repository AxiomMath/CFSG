module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card

import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

theorem eq_one_of_commute_image_of_perfect {H : Type*} [Group H] (N D₀ : Subgroup H) [N.Normal]
    [D₀.Normal] (hN : ⁅N, N⁆ = N) (hD : ∀ h : H, h ∈ D₀ ↔ ∀ n ∈ N, h * n = n * h)
    (y : H ⧸ D₀) (hy : ∀ s ∈ N.map (QuotientGroup.mk' D₀), y * s = s * y) : y = 1 := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective D₀ y
  change (QuotientGroup.mk h = 1)
  rw [QuotientGroup.eq_one_iff]
  refine (hD h).mpr fun n hn => ?_
  let q : H →* H ⧸ D₀ := QuotientGroup.mk' D₀
  have hcD : ∀ x ∈ N, h * x * h⁻¹ * x⁻¹ ∈ D₀ := by
    intro x hx
    have hy' := hy (q x) (Subgroup.mem_map_of_mem q hx)
    have hq : q (h * x) = q (x * h) := by
      simpa only [map_mul] using hy'
    have h1 : q (h * x * h⁻¹ * x⁻¹) = 1 := by
      rw [show h * x * h⁻¹ * x⁻¹ = (h * x) * (x * h)⁻¹ by group]
      simp only [map_mul, map_inv, hq, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hcN : ∀ x ∈ N, h * x * h⁻¹ * x⁻¹ ∈ N :=
    fun x hx => N.mul_mem ((inferInstance : N.Normal).conj_mem x hx h) (N.inv_mem hx)
  have hcomm : ∀ a ∈ N, ∀ b ∈ N, h * ⁅a, b⁆ = ⁅a, b⁆ * h := by
    intro a ha b hb
    have hcaD := hcD a ha
    have hcbD := hcD b hb
    have hcaN := hcN a ha
    have hcbN := hcN b hb
    have hca : ∀ m ∈ N, (h * a * h⁻¹ * a⁻¹) * m = m * (h * a * h⁻¹ * a⁻¹) :=
      fun m hm => (hD _).mp hcaD m hm
    have hcb : ∀ m ∈ N, (h * b * h⁻¹ * b⁻¹) * m = m * (h * b * h⁻¹ * b⁻¹) :=
      fun m hm => (hD _).mp hcbD m hm
    have ha' : h * a * h⁻¹ = (h * a * h⁻¹ * a⁻¹) * a := by group
    have hb' : h * b * h⁻¹ = (h * b * h⁻¹ * b⁻¹) * b := by group
    have h1 : ⁅h * a * h⁻¹ * a⁻¹, b * (h * b * h⁻¹ * b⁻¹)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (hca (b * (h * b * h⁻¹ * b⁻¹)) (N.mul_mem hb hcbN))
    have h2 : ⁅a, h * b * h⁻¹ * b⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hcb a ha).symm
    have key : h * ⁅a, b⁆ * h⁻¹ = ⁅a, b⁆ := by
      rw [conjugate_commutatorElement a b h, ha', hb']
      calc ⁅(h * a * h⁻¹ * a⁻¹) * a, (h * b * h⁻¹ * b⁻¹) * b⁆
          = ⁅a * (h * a * h⁻¹ * a⁻¹), b * (h * b * h⁻¹ * b⁻¹)⁆ := by
              rw [hca a ha, hcb b hb]
        _ = a * ⁅h * a * h⁻¹ * a⁻¹, b * (h * b * h⁻¹ * b⁻¹)⁆ * a⁻¹ *
              ⁅a, b * (h * b * h⁻¹ * b⁻¹)⁆ :=
              commutatorElement_mul_left_eq_conj_mul a _ _
        _ = ⁅a, b * (h * b * h⁻¹ * b⁻¹)⁆ := by rw [h1]; group
        _ = ⁅a, b⁆ * b * ⁅a, h * b * h⁻¹ * b⁻¹⁆ * b⁻¹ :=
              commutatorElement_mul_right_eq_mul_conj a b _
        _ = ⁅a, b⁆ := by rw [h2]; group
    exact (mul_inv_eq_iff_eq_mul).mp key
  have hNle : N ≤ Subgroup.centralizer ({h} : Set H) := by
    rw [← hN]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    exact (Subgroup.mem_centralizer_singleton_iff (g := h) (k := ⁅a, b⁆)).mpr
      (hcomm a ha b hb).symm
  exact ((Subgroup.mem_centralizer_singleton_iff (g := h) (k := n)).mp (hNle hn)).symm

theorem nonempty_mulEquiv_map_quotient_center {H : Type*} [Group H] (N D₀ : Subgroup H)
    [D₀.Normal] (hD : ∀ h : H, h ∈ D₀ ↔ ∀ n ∈ N, h * n = n * h) :
    Nonempty (↥(N.map (QuotientGroup.mk' D₀)) ≃* (↥N ⧸ Subgroup.center ↥N)) := by
  let f : ↥N →* H ⧸ D₀ := (QuotientGroup.mk' D₀).comp N.subtype
  have hker : f.ker = Subgroup.center ↥N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hx y
      have hx' : ((x : H) : H ⧸ D₀) = 1 := hx
      have hxD : (x : H) ∈ D₀ := (QuotientGroup.eq_one_iff (x : H)).mp hx'
      exact (Subtype.ext ((hD (x : H)).mp hxD (y : H) y.2)).symm
    · intro hx
      have hxD : (x : H) ∈ D₀ := (hD (x : H)).mpr fun n hn => by
        have hval := congrArg Subtype.val (hx ⟨n, hn⟩)
        simpa using hval.symm
      show ((x : H) : H ⧸ D₀) = 1
      exact (QuotientGroup.eq_one_iff (x : H)).mpr hxD
  have hrange : f.range = N.map (QuotientGroup.mk' D₀) := by
    dsimp only [f]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans
      (MulEquiv.subgroupCongr hrange))).symm⟩

theorem dvd_card_of_dvd_centralizer_of_not_dvd_quotient {H : Type*} [Group H] [Finite H]
    (D : Subgroup H) [D.Normal] (d : H) {p : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.card (Subgroup.centralizer ({d} : Set H)))
    (hq : ¬ p ∣ Nat.card (Subgroup.centralizer ({(d : H ⧸ D)} : Set (H ⧸ D)))) :
    p ∣ Nat.card D := by
  let C : Subgroup H := Subgroup.centralizer ({d} : Set H)
  change p ∣ Nat.card ↥C at h
  let g : ↥C →* H ⧸ D := (QuotientGroup.mk' D).comp C.subtype
  have hrange_le : g.range ≤ Subgroup.centralizer ({(d : H ⧸ D)} : Set (H ⧸ D)) := by
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : (c : H) * d = d * (c : H) :=
      Subgroup.mem_centralizer_singleton_iff.mp c.2
    show (QuotientGroup.mk' D) (c : H) * (d : H ⧸ D) =
      (d : H ⧸ D) * (QuotientGroup.mk' D) (c : H)
    change (QuotientGroup.mk' D) (c : H) * (QuotientGroup.mk' D) d =
      (QuotientGroup.mk' D) d * (QuotientGroup.mk' D) (c : H)
    rw [← map_mul, ← map_mul, hc]
  have hnot : ¬ p ∣ Nat.card ↥g.range := fun hdiv =>
    hq (hdiv.trans (Subgroup.card_dvd_of_le hrange_le))
  have hcard : Nat.card ↥C = Nat.card ↥g.range * Nat.card ↥g.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
  have hpker : p ∣ Nat.card ↥g.ker := by
    have h' : p ∣ Nat.card ↥g.range * Nat.card ↥g.ker := by
      rw [← hcard]
      exact h
    exact (hp.dvd_mul.mp h').resolve_left hnot
  let φ : ↥g.ker →* ↥D :=
    { toFun := fun c => ⟨((c : ↥C) : H), by
        have hc := MonoidHom.mem_ker.mp c.2
        exact (QuotientGroup.eq_one_iff ((c : ↥C) : H)).mp hc⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥D => (z : H)) hab
  exact hpker.trans (Subgroup.card_dvd_of_injective φ hφinj)

end CFSG.OddStandard.AltStdSec.SwapPartner
