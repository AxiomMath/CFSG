module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29I1
public import CFSG.GH74.Generic.BProg.B3.S3Sec29C1

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools Subgroup

namespace S3T3

variable {G : Type} [Group G] [Finite G]

theorem exists_invol {Λ : Subgroup G} (hperf : ⁅Λ, Λ⁆ = Λ) (hne : Λ ≠ ⊥) :
    ∃ l ∈ Λ, l * l = 1 ∧ l ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥Λ := (Subgroup.nontrivial_iff_ne_bot Λ).mpr hne
  have heven : 2 ∣ Nat.card ↥Λ :=
    S3Sec29I.even_card_of_perfect (Subgroup.isPerfect_iff.mpr hperf)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥Λ) 2 heven
  refine ⟨g, g.2, ?_, ?_⟩
  · have h := pow_orderOf_eq_one g
    rw [hg, pow_two] at h
    exact congrArg Subtype.val h
  · intro h
    have h1 : g = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hg
    omega

theorem exists_invol_comm {J Λ : Subgroup G} (hJ : IsA7Bar J) (hΛJ : Λ ≤ J)
    (hperf : ⁅Λ, Λ⁆ = Λ) (hne : Λ ≠ ⊥) {l : G} (hl : l ∈ Λ) (hl2 : l * l = 1) (hl1 : l ≠ 1) :
    ∃ w ∈ Λ, w * w = 1 ∧ w ≠ 1 ∧ w ≠ l ∧ w * l = l * w := by
  have hlo : orderOf l = 2 := orderOf_eq_prime (by rw [pow_two]; exact hl2) hl1
  have hlP : IsPGroup 2 ↥(zpowers l) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hlo, pow_one])
  obtain ⟨T, hT, hlT⟩ := S3Theta52.exists_isSylowOf_ge (zpowers_le.2 hl) hlP
  have hlT' : l ∈ T := hlT (mem_zpowers l)
  obtain ⟨s, hsT, t, htT, hs1, ht1, hst, hs2, ht2⟩ :=
    S3Sec29I1.two_invol_of_A7 hJ hΛJ hperf hne hT
  have hTne : T ≠ ⊥ := fun h => hl1 (by rw [h] at hlT'; exact (Subgroup.mem_bot.1 hlT'))
  obtain ⟨z, hzT, hzo, hzc⟩ := S3Sec29C.exists_involution_central hT.isPGroup le_rfl hTne
    (fun p hp f hf => T.mul_mem (T.mul_mem hp hf) (T.inv_mem hp))
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hzo, pow_two] at h
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hzo
    omega
  by_cases hzl : z = l
  · subst hzl
    by_cases hsz : s = z
    · exact ⟨t, hT.le htT, ht2, ht1, fun h => hst (hsz.trans h.symm), (hzc t htT)⟩
    · exact ⟨s, hT.le hsT, hs2, hs1, hsz, (hzc s hsT)⟩
  · exact ⟨z, hT.le hzT, hz2, hz1, hzl, (hzc l hlT').symm⟩

theorem exists_invol_centralizer {Λ : Subgroup G} (heven : 2 ∣ Nat.card ↥Λ) {x : G}
    (hxN : x ∈ normalizer (Λ : Set G)) (hx2 : x * x = 1) :
    ∃ w ∈ Λ, w * w = 1 ∧ w ≠ 1 ∧ w * x = x * w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype ↥Λ := Fintype.ofFinite _
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  let f : Function.End ↥Λ := fun l => ⟨x * l * x⁻¹, (mem_normalizer_iff.mp hxN l).mp l.2⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    funext l
    apply Subtype.ext
    show x * (x * (l : G) * x⁻¹) * x⁻¹ = l
    rw [hxi]
    calc x * (x * (l : G) * x) * x = (x * x) * l * (x * x) := by group
      _ = l := by rw [hx2]; group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  set C := Λ ⊓ centralizer ({x} : Set G) with hC
  have hfix : ∀ l : ↥Λ, f l = l ↔ (l : G) * x = x * l := by
    intro l
    constructor
    · intro h
      have h1 : x * (l : G) * x⁻¹ = l := congrArg Subtype.val h
      calc (l : G) * x = x * l * x⁻¹ * x := by rw [h1]
        _ = x * l := by group
    · intro h
      apply Subtype.ext
      show x * (l : G) * x⁻¹ = l
      rw [← h]
      group
  have hcard : Fintype.card (Function.fixedPoints f) = Nat.card ↥C := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun l => ⟨l.1.1, Subgroup.mem_inf.2 ⟨l.1.2,
          Subgroup.mem_centralizer_singleton_iff.2 ((hfix l.1).1 l.2)⟩⟩
        invFun := fun c => ⟨⟨c.1, (Subgroup.mem_inf.1 c.2).1⟩, (hfix _).2
          (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).2)⟩
        left_inv := fun l => rfl
        right_inv := fun c => rfl }
  rw [hcard, ← Nat.card_eq_fintype_card] at hmod
  have hCeven : 2 ∣ Nat.card ↥C := by
    have h1 : Nat.card ↥Λ % 2 = 0 := Nat.mod_eq_zero_of_dvd heven
    unfold Nat.ModEq at hmod
    exact Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 2 hCeven
  have hgC := g.2
  obtain ⟨hgΛ, hgx⟩ := Subgroup.mem_inf.1 hgC
  refine ⟨g, hgΛ, ?_, ?_, Subgroup.mem_centralizer_singleton_iff.1 hgx⟩
  · have h := pow_orderOf_eq_one g
    rw [hg, pow_two] at h
    exact congrArg Subtype.val h
  · intro h
    have h1 : g = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hg
    omega

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {v g : G} (hv : v * v = 1) (hg : g ∈ zpowers v) :
    g = 1 ∨ g = v := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have hv2 : v ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hv
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' i
  · left
    rw [hj, zpow_mul, hv2, one_zpow]
  · right
    rw [hj, zpow_add, zpow_mul, hv2, one_zpow, one_mul, zpow_one]

end S3T3

end CFSG.GH74.Generic.BProg.B3
