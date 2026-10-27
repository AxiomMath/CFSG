module

public import CFSG.GH74.AS16.E2.Leaves
public import CFSG.GH74.E2.Terminal

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS
open CFSG.GH74.E2 hiding Hyp

structure PumpUpData2 : Prop where
  shape_of_fixed : ∀ (K : Type) [Group K] [Finite K], K0Shape K → ∀ α : MulAut K, α ^ 2 = 1 →
    α ≠ 1 → ∀ L : Subgroup K, (∀ x ∈ L, α x = x) → IsQuasisimple ↥L → Shape2M12 K

@[expose] def NoComponent2M12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.GH74.E2.Hyp G → ∀ w : G, orderOf w = 2 →
    ∀ K : Subgroup G, IsCompCen w K → ¬ Shape2M12 ↥K

theorem isCompCen_or_m12_of_commute (hComp : ComponentList) (hP : PumpUpData2) {G : Type}
    [Group G] [Finite G] (hH : CFSG.GH74.E2.Hyp G) {u y : G} (hu : orderOf u = 2)
    (hy : orderOf y = 2) (huy : u * y = y * u) {K : Subgroup G} (hK : IsCompCen u K)
    (hKy : K ≤ Cen y) :
    IsCompCen y K ∨
      ∃ (w : G) (Kw : Subgroup G), orderOf w = 2 ∧ IsCompCen w Kw ∧ Shape2M12 ↥Kw := by
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
      left
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
    exact Or.inr ⟨y, Ky, hy, hKy', hP.shape_of_fixed ↥Ky hshape α hα2 hα1 _ hLfix hLq⟩


theorem exists_m12_of_nonTerminal (hComp : ComponentList) (hP : PumpUpData2) {G : Type}
    [Group G] [Finite G] (hH : CFSG.GH74.E2.Hyp G) {z : G} (hz : orderOf z = 2) {L : Subgroup G}
    (hL : IsCompCen z L) (hnt : ¬ Terminal L) :
    ∃ (w : G) (Kw : Subgroup G), orderOf w = 2 ∧ IsCompCen w Kw ∧ Shape2M12 ↥Kw := by
  unfold Terminal at hnt
  push Not at hnt
  obtain ⟨y, hy, hyL, hyn⟩ := hnt
  have hz2 : z * z = 1 := by rw [← sq]; exact sq_eq_one_of_orderOf hz
  have hy2 : y * y = 1 := by rw [← sq]; exact sq_eq_one_of_orderOf hy
  have hLy : L ≤ Cen y := fun k hk => mem_Cen.2 (Subgroup.mem_centralizer_iff.1 hyL k hk).symm
  by_cases hcomm : z * y = y * z
  · rcases isCompCen_or_m12_of_commute hComp hP hH hz hy hcomm hL hLy with h | h
    · exact absurd h hyn
    · exact h
  · have hty : z * y ∈ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
      have h1 : z * k = k * z := mem_Cen.1 (hL.1 hk)
      have h2 : k * y = y * k := Subgroup.mem_centralizer_iff.1 hyL k hk
      calc k * (z * y) = (k * z) * y := by rw [mul_assoc]
        _ = (z * k) * y := by rw [h1]
        _ = z * (k * y) := by rw [mul_assoc]
        _ = z * (y * k) := by rw [h2]
        _ = (z * y) * k := by rw [mul_assoc]
    have hcK : ∀ g ∈ Subgroup.zpowers (z * y), g ∈ Subgroup.centralizer (L : Set G) :=
      fun g hg => Subgroup.zpowers_le.2 hty hg
    rcases dihedral_cases hz2 hy2 with ⟨g, hg, hgty⟩ | ⟨w, hw, hw2, hw1, hwz, hwy⟩
    · exfalso
      have hconjK := conjugate_eq_of_mem_centralizer (hcK g hg)
      have h := AS16.isCompIn_conj hL g
      rw [conjugate_Cen_eq hgty, hconjK] at h
      exact hyn h
    · have hw' : w ^ 2 = 1 := by rw [pow_two]; exact hw2
      have hwo : orderOf w = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime hw' hw1
      have hLw : L ≤ Cen w := fun k hk =>
        mem_Cen.2 (Subgroup.mem_centralizer_iff.1 (hcK w hw) k hk).symm
      rcases isCompCen_or_m12_of_commute hComp hP hH hz hwo hwz.symm hL hLw with h | h
      · rcases isCompCen_or_m12_of_commute hComp hP hH hwo hy hwy h hLy with h' | h'
        · exact absurd h' hyn
        · exact h'
      · exact h

theorem noPairA5NT_of (hCL : ComponentList) (hP : PumpUpData2) (hN : NoComponent2M12) :
    NoPairA5NT := by
  intro G _ _ T z L hcfg _ hnt
  obtain ⟨w, Kw, hw, hKw, hsh⟩ :=
    exists_m12_of_nonTerminal hCL hP hcfg.hyp hcfg.pair.orderOf_eq hcfg.pair.isComp hnt
  exact hN G hcfg.hyp w hw Kw hKw hsh

theorem noPair2M12_of (hN : NoComponent2M12) : NoPairOf Shape2M12 := by
  intro G _ _ T z L hcfg _ hsh
  exact hN G hcfg.hyp z hcfg.pair.orderOf_eq L hcfg.pair.isComp hsh

end CFSG.GH74.AS16.E2
