module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.GroupTheory.WielandtProductBasic
import CFSG.Timmesfeld.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem involution_mul_conj_mem_of_mem_sup_zpowers {K : Subgroup G} {t : G}
    (ht : t * t = 1) (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    {g : G} (hg : g ∈ K ⊔ Subgroup.zpowers t) :
    t * (g⁻¹ * t * g) ∈ K := by
  have htN : t ∈ Subgroup.normalizer (K : Set G) :=
    CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem htK
  have hzN : Subgroup.zpowers t ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr htN
  have hM : ((K ⊔ Subgroup.zpowers t : Subgroup G) : Set G) =
      (K : Set G) * (Subgroup.zpowers t : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K (Subgroup.zpowers t) hzN
  have hg' : g ∈ (K : Set G) * (Subgroup.zpowers t : Set G) := by
    rw [← hM]
    exact hg
  rw [Set.mem_mul] at hg'
  obtain ⟨k, hk, z, hz, rfl⟩ := hg'
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hzcases : z = 1 ∨ z = t := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
    rcases Int.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · left
      rw [← two_mul, zpow_mul, h2, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
  rcases hzcases with hz1 | hzt
  · rw [hz1, mul_one]
    have h1 : t * k⁻¹ * t⁻¹ ∈ K := htK k⁻¹ (K.inv_mem hk)
    have e : t * (k⁻¹ * t * k) = (t * k⁻¹ * t⁻¹) * k := by
      rw [hti]
      group
    rw [e]
    exact K.mul_mem h1 hk
  · rw [hzt]
    have h1 : t * k * t⁻¹ ∈ K := htK k hk
    have h1' : t * k * t ∈ K := by simpa [hti] using h1
    have h2 : k⁻¹ * (t * k * t) ∈ K := K.mul_mem (K.inv_mem hk) h1'
    have e : t * ((k * t)⁻¹ * t * (k * t)) = (t * t) * (k⁻¹ * (t * k * t)) := by
      rw [mul_inv_rev, hti]
      group
    rw [e, ht, one_mul]
    exact h2

theorem isPGroup_closure_pair_of_forall_conj_eq_inv_imp_eq_one {K : Subgroup G} {t : G}
    (ht : t * t = 1) (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hinv : ∀ y ∈ K, Odd (orderOf y) → t * y * t⁻¹ = y⁻¹ → y = 1)
    {g : G} (hg : g ∈ K ⊔ Subgroup.zpowers t) :
    IsPGroup 2 (Subgroup.closure ({t, g⁻¹ * t * g} : Set G)) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hgK : t * (g⁻¹ * t * g) ∈ K :=
    involution_mul_conj_mem_of_mem_sup_zpowers ht htK hg
  set s := g⁻¹ * t * g with hs
  have hs2 : s * s = 1 := by
    rw [hs]
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht]; group
  set u := t * s with hu
  have huK : u ∈ K := by rw [hu]; exact hgK
  have htu : t * u * t⁻¹ = u⁻¹ := by
    rw [hu, show (t * s)⁻¹ = s * t by
      rw [mul_inv_rev, hti, inv_eq_of_mul_eq_one_right hs2]]
    calc t * (t * s) * t⁻¹ = (t * t) * s * t⁻¹ := by group
      _ = s * t⁻¹ := by rw [ht, one_mul]
      _ = s * t := by rw [hti]
  by_contra hnot
  have hn0 : orderOf u ≠ 0 := (orderOf_pos u).ne'
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hm1 : m ≠ 1 := by
    intro hm1
    apply hnot
    have ham' : orderOf u = 2 ^ a := by rw [ham, hm1, mul_one]
    refine CFSG.Timmesfeld.isPGroup_two_closure_pair (k := a) ht hs2 ?_
    rw [← hu, ← ham', pow_orderOf_eq_one]
  set y := u ^ 2 ^ a with hy
  have h2a0 : 2 ^ a ≠ 0 := by positivity
  have hdvd : 2 ^ a ∣ orderOf u := by
    rw [ham]
    exact dvd_mul_right _ _
  have hyord : orderOf y = m := by
    rw [hy, orderOf_pow_of_dvd h2a0 hdvd, ham, Nat.mul_div_cancel_left m (by positivity)]
  have hyodd : Odd (orderOf y) := hyord ▸ hm
  have hyne : y ≠ 1 := by
    intro h1
    apply hm1
    rw [← hyord, orderOf_eq_one_iff.mpr h1]
  have hyK : y ∈ K := by
    rw [hy]
    exact K.pow_mem huK _
  have hty : t * y * t⁻¹ = y⁻¹ := by
    rw [hy]
    have h1 : t * u ^ 2 ^ a * t⁻¹ = (t * u * t⁻¹) ^ 2 ^ a := (conj_pow).symm
    rw [htu, inv_pow] at h1
    exact h1
  exact hyne (hinv y hyK hyodd hty)

theorem mem_pCore_sup_zpowers_of_forall_conj_eq_inv_imp_eq_one {K : Subgroup G} {t : G}
    (ht : t * t = 1) (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hinv : ∀ y ∈ K, Odd (orderOf y) → t * y * t⁻¹ = y⁻¹ → y = 1) :
    (⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩ :
        (K ⊔ Subgroup.zpowers t : Subgroup G)) ∈
      CFSG.pCore 2 (K ⊔ Subgroup.zpowers t : Subgroup G) := by
  let M : Subgroup G := K ⊔ Subgroup.zpowers t
  let t' : M := ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩
  have hstep : ∀ g ∈ M, IsPGroup 2 (Subgroup.closure ({t, g⁻¹ * t * g} : Set G)) :=
    fun g hg => isPGroup_closure_pair_of_forall_conj_eq_inv_imp_eq_one ht htK hinv hg
  have hclosM : ∀ g : M, IsPGroup 2
      (Subgroup.closure ({t', g⁻¹ * t' * g} : Set M)) := by
    intro g
    have hG : IsPGroup 2
        (Subgroup.closure ({t, ((g : M) : G)⁻¹ * t * ((g : M) : G)} : Set G)) :=
      hstep (g : G) g.2
    have e : (Subgroup.closure ({t', g⁻¹ * t' * g} : Set M)).map M.subtype =
        Subgroup.closure ({t, ((g : M) : G)⁻¹ * t * ((g : M) : G)} : Set G) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [← e] at hG
    exact hG.of_equiv
      ((Subgroup.closure _).equivMapOfInjective M.subtype M.subtype_injective).symm
  refine (CFSG.BaerSuzuki.baer_suzuki_iff (p := 2) t').2 fun g => ?_
  have h := hclosM g⁻¹
  rw [show (g⁻¹)⁻¹ = g from inv_inv g] at h
  exact h

theorem commute_of_forall_conj_eq_inv_imp_eq_one {K : Subgroup G}
    (hK : ∀ P : Subgroup G, P ≤ K → IsPGroup 2 P → K ≤ Subgroup.normalizer (P : Set G) → P = ⊥)
    {t : G} (ht : t * t = 1) (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hinv : ∀ y ∈ K, Odd (orderOf y) → t * y * t⁻¹ = y⁻¹ → y = 1) :
    ∀ k ∈ K, t * k = k * t := by
  let M : Subgroup G := K ⊔ Subgroup.zpowers t
  let t' : M := ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩
  have hP : t' ∈ CFSG.pCore 2 M :=
    mem_pCore_sup_zpowers_of_forall_conj_eq_inv_imp_eq_one ht htK hinv
  let N : Subgroup G := (CFSG.pCore 2 M).map M.subtype ⊓ K
  have hN2 : IsPGroup 2 N :=
    (CFSG.pCore_isPGroup (p := 2) (G := M) |>.map M.subtype).to_le inf_le_left
  have hNK : N ≤ K := inf_le_right
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨m, hmP, rfl⟩ := hn.1
    have hmK : (m : G) ∈ K := hn.2
    let k' : M := ⟨k, Subgroup.mem_sup_left hk⟩
    have hconjP : k' * m * k'⁻¹ ∈ CFSG.pCore 2 M :=
      CFSG.pCore_normal.conj_mem m hmP k'
    have hconjK : k * (m : G) * k⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem hk hmK) (K.inv_mem hk)
    exact ⟨⟨k' * m * k'⁻¹, hconjP, rfl⟩, hconjK⟩
  have hNbot : N = ⊥ := hK N hNK hN2 hKN
  intro k hk
  let k' : M := ⟨k, Subgroup.mem_sup_left hk⟩
  have hm0P : t' * k' * t'⁻¹ * k'⁻¹ ∈ CFSG.pCore 2 M := by
    have h1 : k' * t'⁻¹ * k'⁻¹ ∈ CFSG.pCore 2 M :=
      CFSG.pCore_normal.conj_mem t'⁻¹ (Subgroup.inv_mem _ hP) k'
    have e : t' * k' * t'⁻¹ * k'⁻¹ = t' * (k' * t'⁻¹ * k'⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hP h1
  have hm0K : t * k * t⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem (htK k hk) (K.inv_mem hk)
  have hc : t * k * t⁻¹ * k⁻¹ ∈ N :=
    ⟨⟨t' * k' * t'⁻¹ * k'⁻¹, hm0P, rfl⟩, hm0K⟩
  rw [hNbot, Subgroup.mem_bot] at hc
  have hkt : k * t = t * k := by
    calc k * t = (t * k * t⁻¹ * k⁻¹)⁻¹ * (t * k) := by group
      _ = t * k := by rw [hc, inv_one, one_mul]
  exact hkt.symm

end CFSG.GroupTheory
