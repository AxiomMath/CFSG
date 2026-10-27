module

public import Mathlib.GroupTheory.Sylow

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.GroupTheory

theorem exists_conj_of_order_three_of_mem_same_coset
    {M : Type*} [Group M] [Finite M] {J : Subgroup M} [J.Normal]
    (hJ2 : IsPGroup 2 J) {x y : M} (hx : orderOf x = 3) (hy : orderOf y = 3)
    (hcos : x⁻¹ * y ∈ J) : ∃ j ∈ J, j * y * j⁻¹ = x := by
  let X : Subgroup M := Subgroup.zpowers x
  let Y : Subgroup M := Subgroup.zpowers y
  let K : Subgroup M := X ⊔ J
  have hX3 : IsPGroup 3 X := by
    refine IsPGroup.of_card (n := 1) ?_
    dsimp only [X]
    rw [Nat.card_zpowers, hx]
    norm_num
  have hY3 : IsPGroup 3 Y := by
    refine IsPGroup.of_card (n := 1) ?_
    dsimp only [Y]
    rw [Nat.card_zpowers, hy]
    norm_num
  have hcardX : Nat.card X = 3 := by
    dsimp only [X]
    rw [Nat.card_zpowers, hx]
  have hcardY : Nat.card Y = 3 := by
    dsimp only [Y]
    rw [Nat.card_zpowers, hy]
  have hdisj : Disjoint X J :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) X J hX3 hJ2
  have hinf : X ⊓ J = ⊥ := hdisj.eq_bot
  have hcardK : Nat.card K = 3 * Nat.card J := by
    let f : X × J → K := fun p =>
      ⟨(p.1 : M) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
    have hfinj : Function.Injective f := by
      rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
      simp only [f, Subtype.mk.injEq] at h
      have hcomm : a⁻¹ * a' = b * b'⁻¹ := by
        calc
          a⁻¹ * a' = a⁻¹ * (a' * b') * b'⁻¹ := by group
          _ = a⁻¹ * (a * b) * b'⁻¹ := by rw [h]
          _ = b * b'⁻¹ := by group
      have hmem : a⁻¹ * a' ∈ X ⊓ J := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact X.mul_mem (X.inv_mem ha) ha'
        · rw [hcomm]
          exact J.mul_mem hb (J.inv_mem hb')
      rw [hinf] at hmem
      have haa' : a⁻¹ * a' = 1 := by simpa using hmem
      have hbb' : b * b'⁻¹ = 1 := by rw [← hcomm]; exact haa'
      exact Prod.ext (Subtype.ext (inv_mul_eq_one.mp haa'))
        (Subtype.ext (mul_inv_eq_one.mp hbb'))
    have hfsurj : Function.Surjective f := by
      rintro ⟨k, hk⟩
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp (show k ∈ X ⊔ J from hk)
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
    have hbij : X × J ≃ K := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
    calc
      Nat.card K = Nat.card (X × J) := (Nat.card_congr hbij).symm
      _ = Nat.card X * Nat.card J := Nat.card_prod X J
      _ = 3 * Nat.card J := by rw [hcardX]
  have hnot3J : ¬ 3 ∣ Nat.card J := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hJ2
    rw [hn]
    intro h
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h32
  have hXleK : X ≤ K := le_sup_left
  have hcardXK : Nat.card (X.subgroupOf K) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXleK).toEquiv, hcardX]
  have hidxX : (X.subgroupOf K).index = Nat.card J := by
    have h := Subgroup.card_mul_index (X.subgroupOf K)
    rw [hcardXK, hcardK] at h
    exact Nat.mul_left_cancel (by norm_num) h
  let hXsyl : Sylow 3 K :=
    (hX3.of_equiv (Subgroup.subgroupOfEquivOfLe hXleK).symm).toSylow (by
      rw [hidxX]
      exact hnot3J)
  have hyK : y ∈ K := by
    have hy_eq : y = x * (x⁻¹ * y) := by group
    rw [hy_eq]
    exact Subgroup.mul_mem_sup (show x ∈ X from Subgroup.mem_zpowers x) hcos
  have hYleK : Y ≤ K := Subgroup.zpowers_le.mpr hyK
  have hcardYK : Nat.card (Y.subgroupOf K) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYleK).toEquiv, hcardY]
  have hidxY : (Y.subgroupOf K).index = Nat.card J := by
    have h := Subgroup.card_mul_index (Y.subgroupOf K)
    rw [hcardYK, hcardK] at h
    exact Nat.mul_left_cancel (by norm_num) h
  let hYsyl : Sylow 3 K :=
    (hY3.of_equiv (Subgroup.subgroupOfEquivOfLe hYleK).symm).toSylow (by
      rw [hidxY]
      exact hnot3J)
  have hfinSylow : Finite (Sylow 3 K) :=
    Finite.of_injective (fun P : Sylow 3 K => (P : Set K)) fun P Q h => by
      exact Sylow.ext (SetLike.coe_injective h)
  haveI := hfinSylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K hYsyl hXsyl
  have hyPY : (⟨y, hyK⟩ : K) ∈ (hYsyl : Subgroup K) := by
    change (⟨y, hyK⟩ : K) ∈ Y.subgroupOf K
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y)
  have hkconjX : (k : M) * y * (k : M)⁻¹ ∈ X := by
    have hk' : MulAut.conj (k : K) • (hYsyl : Subgroup K) = (hXsyl : Subgroup K) := by
      simpa [Sylow.coe_subgroup_smul] using
        congrArg (fun P : Sylow 3 K => (P : Subgroup K)) hk
    have hmem : MulAut.conj (k : K) • (⟨y, hyK⟩ : K) ∈ (hXsyl : Subgroup K) := by
      rw [← hk']
      exact Subgroup.smul_mem_pointwise_smul (⟨y, hyK⟩ : K) (MulAut.conj (k : K))
        (hYsyl : Subgroup K) hyPY
    have hmemX : ((MulAut.conj (k : K) • (⟨y, hyK⟩ : K) : K) : M) ∈ X :=
      Subgroup.mem_subgroupOf.mp
        (show MulAut.conj (k : K) • (⟨y, hyK⟩ : K) ∈ X.subgroupOf K from hmem)
    simpa [MulAut.smul_def, MulAut.conj_apply] using hmemX
  obtain ⟨p, hpX, j, hjJ, hpj⟩ :=
    Subgroup.mem_sup_of_normal_right.mp (show (k : M) ∈ X ⊔ J from k.2)
  have hzjX : j * y * j⁻¹ ∈ X := by
    have h := X.mul_mem (X.mul_mem (X.inv_mem hpX) hkconjX) hpX
    convert h using 1
    rw [← hpj]
    group
  have hzord : orderOf (j * y * j⁻¹) = 3 := by
    rw [← SemiconjBy.orderOf_eq j (show SemiconjBy j y (j * y * j⁻¹) by unfold SemiconjBy; group), hy]
  have hzclass : j * y * j⁻¹ = x ∨ j * y * j⁻¹ = x ^ 2 := by
    obtain ⟨m, hm⟩ :=
      Subgroup.mem_zpowers_iff.mp (show j * y * j⁻¹ ∈ Subgroup.zpowers x from hzjX)
    have hmod : x ^ (m % 3) = j * y * j⁻¹ := by
      calc
        x ^ (m % 3) = x ^ (m % (orderOf x : ℤ)) := by rw [hx]; norm_num
        _ = x ^ m := zpow_mod_orderOf x m
        _ = j * y * j⁻¹ := hm
    have h0 : 0 ≤ m % 3 := Int.emod_nonneg m (by norm_num)
    have hlt : m % 3 < 3 := Int.emod_lt_of_pos m (by norm_num)
    have hcases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hcases with h | h | h
    · exfalso
      have hz1 : j * y * j⁻¹ = 1 := by
        rw [← hmod, h]
        norm_num
      rw [hz1, orderOf_one] at hzord
      norm_num at hzord
    · left
      calc
        j * y * j⁻¹ = x ^ (m % 3) := hmod.symm
        _ = x ^ (1 : ℤ) := by rw [h]
        _ = x := by norm_num
    · right
      calc
        j * y * j⁻¹ = x ^ (m % 3) := hmod.symm
        _ = x ^ (2 : ℤ) := by rw [h]
        _ = x ^ (2 : ℕ) := by norm_num
  rcases hzclass with hzx | hzx
  · exact ⟨j, hjJ, hzx⟩
  · exfalso
    have hzyJ : (j * y * j⁻¹) * y⁻¹ ∈ J := by
      have hconj : y * j⁻¹ * y⁻¹ ∈ J :=
        (inferInstance : J.Normal).conj_mem (j⁻¹) (J.inv_mem hjJ) y
      have h := J.mul_mem hjJ hconj
      convert h using 1
      group
    have hyxJ : y * x⁻¹ ∈ J := by
      have h := (inferInstance : J.Normal).conj_mem (x⁻¹ * y) hcos x
      convert h using 1
      group
    have hzxJ : (j * y * j⁻¹) * x⁻¹ ∈ J := by
      have h := J.mul_mem hzyJ hyxJ
      convert h using 1
      group
    have hxJ : x ∈ J := by
      have h : x ^ 2 * x⁻¹ ∈ J := by simpa [hzx] using hzxJ
      convert h using 1
      group
    obtain ⟨n, hn⟩ := hJ2.exists_orderOf_dvd_pow (⟨x, hxJ⟩ : J)
    rw [Subgroup.orderOf_mk, hx] at hn
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hn
    norm_num at h32

theorem exists_conj_of_order_three_of_mul_inv_mem
    {M : Type*} [Group M] [Finite M] {J : Subgroup M} [J.Normal]
    (hJ2 : IsPGroup 2 J) {x y : M} (hx : orderOf x = 3) (hy : orderOf y = 3)
    (hcos : x * y⁻¹ ∈ J) : ∃ j ∈ J, j * y * j⁻¹ = x := by
  refine exists_conj_of_order_three_of_mem_same_coset hJ2 hx hy ?_
  have h : y * x⁻¹ ∈ J := by simpa using J.inv_mem hcos
  have hc := (inferInstance : J.Normal).conj_mem (y * x⁻¹) h x⁻¹
  convert hc using 1
  group

end CFSG.GroupTheory
