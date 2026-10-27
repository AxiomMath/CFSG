module

public import CFSG.GH74.Uniqueness.Bender.Core
public import CFSG.GroupTheory.SolvableHallNodes

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup
open scoped Pointwise

theorem exists_conj_mem_of_odd_card {G : Type*} [Group G] [Finite G] {N D D₃ A : Subgroup G}
    [N.Normal] (hNp : IsPGroup 2 N) (hND : N ⊓ D = ⊥) (hsup : N ⊔ D = ⊤) (hD₃D : D₃ ≤ D)
    (hD₃ : ∀ d ∈ D, Odd (orderOf d) → d ∈ D₃) (hA : Odd (Nat.card A)) :
    ∃ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ D₃ := by
  classical
  obtain ⟨k, hk⟩ := hNp.exists_card_eq
  have hNA : N ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨j, hj⟩ := hNp ⟨x, hx.1⟩
    have h1 : orderOf x ∣ 2 ^ j :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hj)
    have h2 : orderOf x ∣ Nat.card A := by
      have := orderOf_dvd_natCard (⟨x, hx.2⟩ : A)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ j) (Nat.card A) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hA)
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rw [orderOf_eq_one_iff] at this
    simpa using this
  set B : Subgroup G := N ⊔ A with hB
  have hNB : N ≤ B := le_sup_left
  have hAB : A ≤ B := le_sup_right
  have hBcard : Nat.card B = Nat.card N * Nat.card A :=
    card_sup_eq_mul_of_le_normalizer
      (by rw [Subgroup.normalizer_eq_top]; exact le_top) hNA
  let N' : Subgroup B := N.subgroupOf B
  let A' : Subgroup B := A.subgroupOf B
  let H' : Subgroup B := D₃.subgroupOf B
  have : N'.Normal := Subgroup.Normal.subgroupOf inferInstance B
  have hN'card : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv
  have hindex : N'.index = Nat.card A := by
    have h1 := Subgroup.card_mul_index N'
    rw [hN'card, hBcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hN'p : IsPGroup 2 N' :=
    hNp.of_injective (Subgroup.subgroupOfEquivOfLe hNB).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hNB).injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent N' := hN'p.isNilpotent
  have hsolv : Group.IsSolvable N' := inferInstance
  have hcop : Nat.Coprime (Nat.card N') N'.index := by
    rw [hN'card, hk, hindex]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hA)
  have hNA' : N' ⊓ A' = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨x, hxB⟩ ⟨hx1, hx2⟩
    have hx : x ∈ N ⊓ A := ⟨hx1, hx2⟩
    rw [hNA, Subgroup.mem_bot] at hx
    exact Subgroup.mem_bot.mpr (Subtype.ext hx)
  have hNH' : N' ⊓ H' = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨x, hxB⟩ ⟨hx1, hx2⟩
    have hx : x ∈ N ⊓ D := ⟨hx1, hD₃D hx2⟩
    rw [hND, Subgroup.mem_bot] at hx
    exact Subgroup.mem_bot.mpr (Subtype.ext hx)
  have hNA'u : (N' : Set B) * (A' : Set B) = Set.univ := by
    ext ⟨b, hb⟩
    simp only [Set.mem_univ, iff_true]
    have hb' : b ∈ ((N ⊔ A : Subgroup G) : Set G) := hb
    rw [Subgroup.normal_mul] at hb'
    obtain ⟨n, hn, a, ha, rfl⟩ := Set.mem_mul.mp hb'
    exact Set.mem_mul.mpr ⟨⟨n, hNB hn⟩, hn, ⟨a, hAB ha⟩, ha, rfl⟩
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp D.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    have : (x : G) ∈ N ⊓ D := ⟨hxN, x.2⟩
    rw [hND, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hNH'u : (N' : Set B) * (H' : Set B) = Set.univ := by
    ext ⟨b, hb⟩
    simp only [Set.mem_univ, iff_true]
    have hb' : b ∈ ((N ⊔ A : Subgroup G) : Set G) := hb
    rw [Subgroup.normal_mul] at hb'
    obtain ⟨n, hn, a, ha, rfl⟩ := Set.mem_mul.mp hb'
    have ha' : a ∈ ((N ⊔ D : Subgroup G) : Set G) := by rw [hsup]; trivial
    rw [Subgroup.normal_mul] at ha'
    obtain ⟨n', hn', d, hd, rfl⟩ := Set.mem_mul.mp ha'
    have hdord : Odd (orderOf d) := by
      have hn1 : (QuotientGroup.mk' N) n' = 1 := (QuotientGroup.eq_one_iff n').mpr hn'
      have h1 : (QuotientGroup.mk' N) d = (QuotientGroup.mk' N) (n' * d) := by
        rw [map_mul, hn1, one_mul]
      have h2 := orderOf_injective _ hinj ⟨d, hd⟩
      have h3 : orderOf ((QuotientGroup.mk' N).comp D.subtype ⟨d, hd⟩) = orderOf d := by
        rw [h2, Subgroup.orderOf_mk]
      have h4 : orderOf ((QuotientGroup.mk' N) d) ∣ orderOf (n' * d) := by
        rw [h1]
        exact orderOf_map_dvd _ _
      have h5 : orderOf (n' * d) ∣ Nat.card A := by
        have := orderOf_dvd_natCard (⟨n' * d, ha⟩ : A)
        rwa [Subgroup.orderOf_mk] at this
      refine Odd.of_dvd_nat hA ?_
      rw [← h3]
      exact h4.trans h5
    have hdD₃ : d ∈ D₃ := hD₃ d hd hdord
    have hdB : d ∈ B := by
      have : d = n'⁻¹ * (n' * d) := by group
      rw [this]
      exact B.mul_mem (B.inv_mem (hNB hn')) (hAB ha)
    refine Set.mem_mul.mpr ⟨⟨n * n', B.mul_mem (hNB hn) (hNB hn')⟩, N.mul_mem hn hn',
      ⟨d, hdB⟩, hdD₃, ?_⟩
    apply Subtype.ext
    simp [mul_assoc]
  obtain ⟨n', hn', hconj⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy N' hsolv
    hcop hNH'u hNA'u hNH' hNA'
  refine ⟨(n' : G), hn', fun a ha => ?_⟩
  have hmem : (⟨a, hAB ha⟩ : B) ∈ A' := ha
  rw [hconj] at hmem
  obtain ⟨h, hh, hha⟩ := hmem
  have h1 : (n' : G)⁻¹ * (h : G) * (n' : G) = a := by
    have := congrArg Subtype.val hha
    simpa [MulAut.conj_apply] using this
  have h2 : (n' : G) * a * (n' : G)⁻¹ = (h : G) := by
    rw [← h1]; group
  rw [h2]
  exact hh

end CFSG.GH74.Uniqueness.Bender
