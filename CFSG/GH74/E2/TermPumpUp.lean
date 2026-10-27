module

public import CFSG.GH74.E2.TermBasic
public import CFSG.GH74.E2.ComponentsBridge
public import CFSG.GH74.E2.OddRankG

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.GH74.GLS

structure PumpUpData : Prop where
  card_quasisimple_fixed : ∀ (K : Type) [Group K] [Finite K], K0Shape K → ∀ α : MulAut K,
    α ^ 2 = 1 → α ≠ 1 → ∀ L : Subgroup K, (∀ x ∈ L, α x = x) → IsQuasisimple ↥L →
      Nat.card ↥L = 60 ∨ Nat.card ↥L = 120

theorem isCompCen_le_layer {G : Type} [Group G] [Finite G] (hH : Hyp G) {u y : G}
    (hu : orderOf u = 2) (hy : orderOf y = 2) (huy : u * y = y * u) {K : Subgroup G}
    (hK : IsCompCen u K) (hKy : K ≤ Cen y) :
    K.subgroupOf (Cen y) ≤ CFSG.layer ↥(Cen y) := by
  have hcore : CFSG.pPrimeCore 2 ↥(Cen y) = ⊥ := hH.pPrimeCore_cen_bot hy
  have huC : u ∈ Cen y := mem_Cen.2 huy.symm
  have hu2 : u * u = 1 := by rw [← sq]; exact sq_eq_one_of_orderOf hu
  have hKle : K ≤ Cen u ⊓ Cen y := le_inf hK.1 hKy
  have hcomp : IsCompIn (Cen u ⊓ Cen y) K := isCompIn_mono hK hKle inf_le_left
  refine component_le_layer_of_balance hcore (x := (⟨u, huC⟩ : ↥(Cen y)))
    (M := (Cen u ⊓ Cen y).subgroupOf (Cen y)) ?_ ?_ ?_ ?_
  · exact Subtype.ext hu2
  · intro m
    constructor
    · intro hm
      have h1 : u * (m : G) = (m : G) * u :=
        mem_Cen.1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hm)).1
      exact Subtype.ext h1.symm
    · intro hm
      have h1 : (m : G) * u = u * (m : G) := congrArg (fun x : ↥(Cen y) => (x : G)) hm
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨mem_Cen.2 h1.symm, m.2⟩)
  · exact Subgroup.subgroupOf_mono (Cen y) hKle
  · exact (isComponent_subgroupOf_iff inf_le_right).2 hcomp.2

theorem isCompCen_of_commute (hComp : ComponentList) (hP : PumpUpData) {G : Type} [Group G]
    [Finite G] (hH : Hyp G) {u y : G} (hu : orderOf u = 2) (hy : orderOf y = 2)
    (huy : u * y = y * u) {K : Subgroup G} (hK : IsCompCen u K) (hKy : K ≤ Cen y)
    (h60 : Nat.card ↥K ≠ 60) (h120 : Nat.card ↥K ≠ 120) : IsCompCen y K := by
  have hKq : IsQuasisimple ↥K := isCompCen_quasisimple hK
  have hu2 : u * u = 1 := by rw [← sq]; exact sq_eq_one_of_orderOf hu
  have hbal := isCompCen_le_layer hH hu hy huy hK hKy
  have hlay : CFSG.layer ↥(Cen y) ≠ ⊥ := by
    intro hbot
    have hle := hbal.trans hbot.le
    have hnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
    obtain ⟨k, hk⟩ := exists_ne (1 : ↥K)
    have hkm : (⟨(k : G), hKy k.2⟩ : ↥(Cen y)) ∈ K.subgroupOf (Cen y) := k.2
    have h2 := hle hkm
    rw [Subgroup.mem_bot] at h2
    apply hk
    apply Subtype.ext
    have h3 : ((⟨(k : G), hKy k.2⟩ : ↥(Cen y)) : G) = ((1 : ↥(Cen y)) : G) :=
      congrArg (fun x : ↥(Cen y) => (x : G)) h2
    exact h3
  obtain ⟨Ky, hKy'⟩ := exists_isCompCen_of_layer_ne_bot hlay
  obtain ⟨hshape, huniq⟩ := hComp G hH y hy Ky hKy'
  have hKKy : K ≤ Ky := by
    intro k hk
    have h1 : (⟨k, hKy hk⟩ : ↥(Cen y)) ∈ K.subgroupOf (Cen y) := hk
    exact layer_le_of_unique huniq (hbal h1)
  have huC : u ∈ Cen y := mem_Cen.2 huy.symm
  have hconj : conjugate Ky u = Ky := conjugate_eq_of_unique hKy' huniq huC
  have hnorm : ∀ x : G, x ∈ Ky ↔ u * x * u⁻¹ ∈ Ky := by
    intro x
    have h := AS16.mem_conjugate_iff' Ky u x
    rw [hconj] at h
    exact h
  have hKyq : IsQuasisimple ↥Ky := isCompCen_quasisimple hKy'
  by_cases hcen : ∀ x ∈ Ky, u * x = x * u
  ·
    have hKyu : Ky ≤ Cen u := fun x hx => mem_Cen.2 (hcen x hx)
    have huniqK := (hComp G hH u hu K hK).2
    have hnormK : ∀ x ∈ Ky, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
      intro x hx k hk
      have hconjK := conjugate_eq_of_unique hK huniqK (hKyu hx)
      have h := AS16.mem_conjugate_iff' K x k
      rw [hconjK] at h
      exact h.1 hk
    have hN : (K.subgroupOf Ky).Normal := ⟨fun n hn g => hnormK g g.2 n hn⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKyq hN with htop | hcentre
    · have hKyK : Ky ≤ K := fun x hx => by
        have : (⟨x, hx⟩ : ↥Ky) ∈ K.subgroupOf Ky := by rw [htop]; trivial
        exact this
      rw [le_antisymm hKKy hKyK]
      exact hKy'
    · exfalso
      have hcomm : ∀ a b : ↥K, a * b = b * a := by
        intro a b
        have ha : (⟨(a : G), hKKy a.2⟩ : ↥Ky) ∈ K.subgroupOf Ky := a.2
        have h1 := Subgroup.mem_center_iff.1 (hcentre ha) ⟨(b : G), hKKy b.2⟩
        apply Subtype.ext
        exact (congrArg (fun x : ↥Ky => (x : G)) h1).symm
      obtain ⟨-, -, a, b, hab⟩ := hKq
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm a' b']
  ·
    push Not at hcen
    obtain ⟨x0, hx0, hx0'⟩ := hcen
    have hunorm : u ∈ normalizer (Ky : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      exact hnorm
    obtain ⟨α, hαdef⟩ : ∃ α : MulAut ↥Ky, α = Ky.normalizerMonoidHom ⟨u, hunorm⟩ := ⟨_, rfl⟩
    have hα : ∀ x : ↥Ky, ((α x : ↥Ky) : G) = u * x * u⁻¹ := fun x => by rw [hαdef]; rfl
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    have hα2 : α ^ 2 = 1 := by
      refine MulEquiv.ext fun x => ?_
      rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
      apply Subtype.ext
      rw [hα, hα, hu']
      calc u * (u * (x : G) * u) * u = (u * u) * x * (u * u) := by simp only [mul_assoc]
        _ = x := by rw [hu2, one_mul, mul_one]
    have hα1 : α ≠ 1 := by
      intro h
      apply hx0'
      have h1 := congrArg (fun f : MulAut ↥Ky => ((f ⟨x0, hx0⟩ : ↥Ky) : G)) h
      have h2 : u * x0 * u⁻¹ = x0 := (hα ⟨x0, hx0⟩).symm.trans h1
      calc u * x0 = (u * x0 * u⁻¹) * u := by rw [inv_mul_cancel_right]
        _ = x0 * u := by rw [h2]
    have hLq : IsQuasisimple ↥(K.subgroupOf Ky) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKKy).symm hKq
    have hLfix : ∀ x ∈ K.subgroupOf Ky, α x = x := by
      intro x hx
      apply Subtype.ext
      rw [hα]
      have hxK : (x : G) ∈ K := hx
      have hcu : u * (x : G) = (x : G) * u := mem_Cen.1 (hK.1 hxK)
      calc u * (x : G) * u⁻¹ = (x : G) * u * u⁻¹ := by rw [hcu]
        _ = (x : G) := by rw [mul_inv_cancel_right]
    have hcardL : Nat.card ↥(K.subgroupOf Ky) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKKy).toEquiv
    rcases hP.card_quasisimple_fixed ↥Ky hshape α hα2 hα1 _ hLfix hLq with h | h
    · exact absurd (hcardL ▸ h) h60
    · exact absurd (hcardL ▸ h) h120

end CFSG.GH74.E2
