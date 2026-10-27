module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PrA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888F2A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B513Norm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma s888_odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem s888_oddCore_sl23 : CFSG.oddCore SL23 = ⊥ := by
  rcases sl23_normal_dichotomy (CFSG.oddCore_normal (G := SL23)) with htop | hq8
  · exfalso
    have hodd := s888_odd_card_oddCore SL23
    have hcard : Nat.card SL23 = 24 := by rw [Nat.card_eq_fintype_card]; decide
    rw [htop, Subgroup.card_top, hcard] at hodd
    exact (by decide : ¬ Odd 24) hodd
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx4 : x ^ 4 = 1 := hq8 x hx
    have hoddx : Odd (orderOf x) :=
      Odd.of_dvd_nat (s888_odd_card_oddCore SL23) (Subgroup.orderOf_dvd_natCard _ hx)
    have hdvd4 : orderOf x ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hx4
    have hcop : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.mpr hoddx
    have h1 : orderOf x ∣ 1 := by
      have h4 : orderOf x ∣ 2 * 2 := by simpa using hdvd4
      have h2 : orderOf x ∣ 2 := (hcop.dvd_mul_right (m := 2) (n := 2)).mp h4
      exact (hcop.dvd_mul_right (m := 1) (n := 2)).mp (by simpa using h2)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

private theorem s888_isSL23Mod_sl23 : IsSL23Mod SL23 :=
  ⟨(QuotientGroup.quotientMulEquivOfEq s888_oddCore_sl23).trans QuotientGroup.quotientBot⟩

private lemma s888_twoRes_le (H : Subgroup G) : twoRes H ≤ H :=
  (Subgroup.closure_le (K := H)).2 fun _ hx => hx.1

private theorem s888_isSubnormal_subgroupOf_of_two_step {A : Type*} [Group A] {H L C : Subgroup A}
    (hHL : H ≤ L) (hH : ∀ h ∈ H, ∀ l ∈ L, l * h * l⁻¹ ∈ H)
    (hL : ∀ l ∈ L, ∀ c ∈ C, c * l * c⁻¹ ∈ L) : (H.subgroupOf C).IsSubnormal := by
  have hLn : (L.subgroupOf C).Normal := by
    constructor
    intro l hl c
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact hL _ hl _ c.2
  refine Subgroup.IsSubnormal.step _ (L.subgroupOf C) ?_ hLn.isSubnormal ?_
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hHL hx
  · constructor
    intro h hh g
    have hh' : ((h : ↥C) : A) ∈ H := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hh)
    have hg : ((g : ↥C) : A) ∈ L := Subgroup.mem_subgroupOf.mp g.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hH _ hh' _ hg

private theorem s888_sl23PocketIn_of {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z)
    {X : Subgroup G} (hM : K₁ ⊔ K₂ = twoRes (X ⊓ centralizer ({z} : Set G))) :
    Sl23PocketIn X z K₁ := by
  obtain ⟨e₁⟩ := h.iso₁
  have hMY : K₁ ⊔ K₂ ≤ X ⊓ centralizer ({z} : Set G) := by
    rw [hM]; exact s888_twoRes_le _
  refine ⟨h.z_mem₁, le_sup_left.trans hMY, ?_, ?_⟩
  · refine s888_isSubnormal_subgroupOf_of_two_step (L := K₁ ⊔ K₂)
      (C := X ⊓ centralizer ({z} : Set G)) le_sup_left ?_ ?_
    · intro a ha l hl
      obtain ⟨p, hp, q, hq, rfl⟩ := sec5b_mem_sup_of_comm h.comm hl
      have hqp : q * a * q⁻¹ = a := by
        rw [← h.comm a ha q hq, mul_assoc, mul_inv_cancel, mul_one]
      have hcalc : p * q * a * (p * q)⁻¹ = p * a * p⁻¹ := by
        rw [show p * q * a * (p * q)⁻¹ = p * (q * a * q⁻¹) * p⁻¹ by group, hqp]
      rw [hcalc]
      exact K₁.mul_mem (K₁.mul_mem hp ha) (K₁.inv_mem hp)
    · intro l hl c hc
      have hnorm : c ∈ normalizer ((twoRes (X ⊓ centralizer ({z} : Set G))) : Set G) :=
        sec5b513_mem_normalizer_twoRes (Subgroup.le_normalizer hc)
      have hl' : l ∈ twoRes (X ⊓ centralizer ({z} : Set G)) := by rw [← hM]; exact hl
      have hcl := (Subgroup.mem_normalizer_iff.mp hnorm l).mp hl'
      rwa [hM]
  · exact isSL23Mod_of_mulEquiv e₁.symm s888_isSL23Mod_sl23

theorem Sec5Pair.le_twoRes {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z) {Y : Subgroup G}
    (hY : K₁ ⊔ K₂ ≤ Y) : K₁ ⊔ K₂ ≤ twoRes Y := by
  obtain ⟨e₁⟩ := h.iso₁
  obtain ⟨e₂⟩ := h.iso₂
  refine sup_le ?_ ?_
  · exact sec5_le_of_odd e₁ fun x hx hodd =>
      Subgroup.subset_closure ⟨hY (Subgroup.mem_sup_left hx), hodd⟩
  · exact sec5_le_of_odd e₂ fun x hx hodd =>
      Subgroup.subset_closure ⟨hY (Subgroup.mem_sup_right hx), hodd⟩

theorem Sec5Pair.eq_twoRes [Finite G] {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z)
    {Y : Subgroup G} (hY : K₁ ⊔ K₂ ≤ Y) (hcard : Nat.card ↥(twoRes Y) = 288) :
    K₁ ⊔ K₂ = twoRes Y :=
  Subgroup.eq_of_le_of_card_ge (h.le_twoRes hY) (by rw [hcard, h.card_sup])

theorem Sec5Pair.pocket [Finite G] {K₁ K₂ : Subgroup G} {z : G} (h : Sec5Pair K₁ K₂ z)
    {X : Subgroup G} (hM : K₁ ⊔ K₂ = twoRes (X ⊓ centralizer ({z} : Set G))) :
    Sl23PocketIn X z K₁ ∧ Sl23PocketIn X z K₂ := by
  refine ⟨s888_sl23PocketIn_of h hM, ?_⟩
  refine s888_sl23PocketIn_of (K₁ := K₂) (K₂ := K₁) ?_ ?_
  · exact ⟨fun a ha b hb => (h.comm b hb a ha).symm, h.iso₂, h.iso₁, h.z_mem₂, h.z_mem₁,
      h.z_sq, h.z_ne⟩
  · exact (sup_comm K₂ K₁).trans hM

end CFSG.OddStandard.SmallF3.Omega
