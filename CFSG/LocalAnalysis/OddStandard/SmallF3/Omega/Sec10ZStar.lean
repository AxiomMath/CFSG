module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.ZStar
public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem relIndex_mul_card' {G : Type} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    H.relIndex K * Nat.card H = Nat.card K := by
  have h1 := Subgroup.card_mul_index (H.subgroupOf K)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h1
  rw [mul_comm]
  exact h1

private theorem eq_of_mem_zpowers_of_orderOf_eq_two {G : Type} [Group G] {t x : G}
    (ht : orderOf t = 2) (hx : x ∈ zpowers t) (hx2 : orderOf x = 2) : x = t := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' i
  · exfalso
    rw [hk, zpow_mul, zpow_two, ht2, one_zpow] at hi
    rw [← hi] at hx2
    simp at hx2
  · rw [hk, zpow_add, zpow_mul, zpow_two, ht2, one_zpow, one_mul, zpow_one] at hi
    exact hi.symm

private theorem exists_mul_zpow_of_mem_sup_oddCore {G : Type} [Group G] {H : Subgroup G} {t : G}
    (htH : t ∈ H) {a : G} (ha : a ∈ oddCoreIn H ⊔ zpowers t) :
    ∃ o ∈ oddCoreIn H, ∃ i : ℤ, a = o * t ^ i := by
  let O : Subgroup G := oddCoreIn H
  let X : Subgroup G := O ⊔ zpowers t
  have hOH : O ≤ H := CFSG.ClassicalInvolution.Balance.oddCoreIn_le H
  have hOX : O ≤ X := le_sup_left
  have hZX : zpowers t ≤ X := le_sup_right
  have hXH : X ≤ H := sup_le hOH (Subgroup.zpowers_le.mpr htH)
  have hXnorm : X ≤ Subgroup.normalizer (O : Set G) :=
    hXH.trans (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn H)
  haveI : (O.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXnorm
  have hsup : (O.subgroupOf X) ⊔ ((zpowers t).subgroupOf X) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hOX hZX]
    exact Subgroup.subgroupOf_self X
  have haX : a ∈ X := ha
  have hmem : (⟨a, haX⟩ : ↥X) ∈ (O.subgroupOf X) ⊔ ((zpowers t).subgroupOf X) := by
    rw [hsup]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hz)
  refine ⟨(y : G), hy, i, ?_⟩
  have h1 : (y : G) * (z : G) = a := by
    have := congrArg (Subtype.val) hyz
    simpa using this
  rw [← h1, ← hi]

theorem sec10_zStar [Finite G] {H : Subgroup G} {t : G} (htH : t ∈ H) (ht1 : t ≠ 1)
    (ht2 : t * t = 1)
    (hiso : ∀ h ∈ H, (h * t * h⁻¹) * t = t * (h * t * h⁻¹) → h * t * h⁻¹ = t) :
    ∀ h ∈ H, h * t * h⁻¹ * t⁻¹ ∈ oddCoreIn H := by
  haveI : Fintype ↥H := Fintype.ofFinite ↥H
  have ht1' : (⟨t, htH⟩ : ↥H) ≠ 1 := by
    intro h1
    exact ht1 (by simpa using congrArg Subtype.val h1)
  have ht2' : (⟨t, htH⟩ : ↥H) * ⟨t, htH⟩ = 1 := by
    apply Subtype.ext
    simpa using ht2
  have hiso' : ∀ g : ↥H,
      (g * ⟨t, htH⟩ * g⁻¹) * ⟨t, htH⟩ = ⟨t, htH⟩ * (g * ⟨t, htH⟩ * g⁻¹) →
      g * ⟨t, htH⟩ * g⁻¹ = ⟨t, htH⟩ := by
    intro g hg
    apply Subtype.ext
    have hg' : ((g : G) * t * (g : G)⁻¹) * t = t * ((g : G) * t * (g : G)⁻¹) := by
      have := congrArg (Subtype.val) hg
      simpa using this
    have hres := hiso (g : G) g.2 hg'
    simpa using hres
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar ↥H ⟨t, htH⟩ ht1' ht2' hiso'
  have hNle' : N ≤ CFSG.oddCore ↥H :=
    le_sSup (s := {N : Subgroup ↥H | N.Normal ∧ Odd (Nat.card N)}) ⟨hNn, hNodd⟩
  have hNle : N.map H.subtype ≤ oddCoreIn H := by
    unfold oddCoreIn CFSG.inSubgroup
    exact Subgroup.map_mono hNle'
  intro h hh
  have hmem : (⟨h, hh⟩ : ↥H) * ⟨t, htH⟩ * (⟨h, hh⟩ : ↥H)⁻¹ * (⟨t, htH⟩ : ↥H)⁻¹ ∈ N :=
    hN ⟨h, hh⟩
  have hmap : (((⟨h, hh⟩ : ↥H) * ⟨t, htH⟩ * (⟨h, hh⟩ : ↥H)⁻¹ *
      (⟨t, htH⟩ : ↥H)⁻¹ : ↥H) : G) ∈ N.map H.subtype := ⟨_, hmem, rfl⟩
  simpa using hNle hmap

theorem sec10_zStar_decomp [Finite G] {H : Subgroup G} {t : G} (htH : t ∈ H) (ht2 : t * t = 1)
    (hZ : ∀ h ∈ H, h * t * h⁻¹ * t⁻¹ ∈ oddCoreIn H) :
    ∀ h ∈ H, ∃ o ∈ oddCoreIn H, ∃ c ∈ H ⊓ centralizer ({t} : Set G), h = o * c := by
  intro h hh
  by_cases ht1 : t = 1
  · refine ⟨1, (oddCoreIn H).one_mem, h, ⟨hh, ?_⟩, by simp⟩
    simp [ht1, Subgroup.mem_centralizer_singleton_iff]
  · let O : Subgroup G := oddCoreIn H
    let X : Subgroup G := O ⊔ zpowers t
    have hOH : O ≤ H := CFSG.ClassicalInvolution.Balance.oddCoreIn_le H
    have hOodd : Odd (Nat.card O) := CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn H
    have htord : orderOf t = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
    let u : G := h * t * h⁻¹
    let v : G := u * t⁻¹
    have hvO : v ∈ O := by
      have := hZ h hh
      simpa [v, u, O] using this
    have hu_eq : u = v * t := by
      unfold v
      group
    have huord : orderOf u = 2 := by
      have h' := (MulAut.conj h).orderOf_eq t
      rw [MulAut.conj_apply] at h'
      rw [htord] at h'
      simpa [u] using h'
    have hOinf : O ⊓ zpowers t = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxO, hxz⟩ := hx
      have hdvd2 : orderOf x ∣ 2 := by
        have := orderOf_dvd_of_mem_zpowers hxz
        rwa [htord] at this
      have hdvdO : orderOf x ∣ Nat.card O := O.orderOf_dvd_natCard hxO
      have hodd : Odd (orderOf x) := hOodd.of_dvd_nat hdvdO
      have hx1 : orderOf x = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
        · exact h1
        · rw [h2] at hodd
          exact absurd hodd (by norm_num)
      simpa using (orderOf_eq_one_iff.mp hx1)
    have hcardX : Nat.card X = Nat.card O * 2 := by
      have h := CFSG.ClassicalInvolution.natCard_eq_mul_of_inf_eq_bot
        (M := X) (A := O) (B := zpowers t) le_sup_left le_sup_right hOinf
        (fun m hm => by
          obtain ⟨o, ho, i, rfl⟩ := exists_mul_zpow_of_mem_sup_oddCore htH hm
          exact ⟨o, ho, t ^ i, Subgroup.zpow_mem_zpowers t i, rfl⟩)
      rwa [Nat.card_zpowers, htord] at h
    have hzt2 : IsPGroup 2 (zpowers t) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, htord]
      norm_num
    have isSylow_t : IsSylow2Of (zpowers t) X := by
      have hrel : (zpowers t).relIndex X = Nat.card O := by
        have h := relIndex_mul_card' (show zpowers t ≤ X from le_sup_right)
        rw [Nat.card_zpowers, htord, hcardX] at h
        exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) h
      exact ⟨le_sup_right, hzt2, by rw [hrel]; exact hOodd.not_two_dvd_nat⟩
    have huX : u ∈ X := by
      rw [hu_eq]
      exact X.mul_mem (Subgroup.mem_sup_left hvO) (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    have hzu2 : IsPGroup 2 (zpowers u) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, huord]
      norm_num
    have isSylow_u : IsSylow2Of (zpowers u) X := by
      have hrel : (zpowers u).relIndex X = Nat.card O := by
        have h := relIndex_mul_card' (Subgroup.zpowers_le.mpr huX)
        rw [Nat.card_zpowers, huord, hcardX] at h
        exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) h
      exact ⟨Subgroup.zpowers_le.mpr huX, hzu2, by rw [hrel]; exact hOodd.not_two_dvd_nat⟩
    obtain ⟨a, haX, hconj⟩ := IsSylow2Of.exists_conj_mem isSylow_t isSylow_u
    have hua_mem : a⁻¹ * u * a ∈ zpowers t := (hconj u).mp (Subgroup.mem_zpowers u)
    have hua_ord : orderOf (a⁻¹ * u * a) = 2 := by
      have h' := (MulAut.conj a⁻¹).orderOf_eq u
      rw [MulAut.conj_apply] at h'
      rw [huord] at h'
      simpa using h'
    have huat : a⁻¹ * u * a = t :=
      eq_of_mem_zpowers_of_orderOf_eq_two htord hua_mem hua_ord
    have hua : u = a * t * a⁻¹ := by
      rw [← huat]
      group
    obtain ⟨o, hoO, i, hai⟩ := exists_mul_zpow_of_mem_sup_oddCore htH haX
    have ha_conj : a * t * a⁻¹ = o * t * o⁻¹ := by
      rw [hai]
      have hcomm : t ^ i * t = t * t ^ i := (Commute.zpow_self t i).eq
      calc (o * t ^ i) * t * (o * t ^ i)⁻¹
          = o * (t ^ i * t) * (t ^ i)⁻¹ * o⁻¹ := by group
        _ = o * (t * t ^ i) * (t ^ i)⁻¹ * o⁻¹ := by rw [hcomm]
        _ = o * t * o⁻¹ := by group
    have h1 : o * t * o⁻¹ = h * t * h⁻¹ := by
      rw [← ha_conj, ← hua]
    have hc_comm : (o⁻¹ * h) * t = t * (o⁻¹ * h) := by
      calc (o⁻¹ * h) * t = o⁻¹ * (h * t * h⁻¹) * h := by group
        _ = o⁻¹ * (o * t * o⁻¹) * h := by rw [h1]
        _ = t * (o⁻¹ * h) := by group
    refine ⟨o, hoO, o⁻¹ * h, ⟨H.mul_mem (H.inv_mem (hOH hoO)) hh, ?_⟩, by group⟩
    change o⁻¹ * h ∈ centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc_comm

end CFSG.OddStandard.SmallF3.Omega
