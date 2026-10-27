module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open Equiv

theorem orderOf_finRotate_seven : orderOf (finRotate 7) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · decide
  · decide

theorem isCycle_of_orderOf_seven (τ : Perm (Fin 7)) (hτ : orderOf τ = 7) : τ.IsCycle := by
  apply Equiv.Perm.isCycle_of_prime_order
  · rw [hτ]; norm_num
  · rw [hτ]
    have := Finset.card_le_univ τ.support
    simp only [Fintype.card_fin] at this
    omega

theorem isConj_finRotate_seven {τ : Perm (Fin 7)} (hτ : orderOf τ = 7) :
    IsConj τ (finRotate 7) := by
  have hc : (finRotate 7).IsCycle := isCycle_of_orderOf_seven _ orderOf_finRotate_seven
  have ht : τ.IsCycle := isCycle_of_orderOf_seven τ hτ
  have hsupp : τ.support.card = (finRotate 7).support.card := by
    rw [← ht.orderOf, ← hc.orderOf, hτ, orderOf_finRotate_seven]
  exact ht.isConj hc hsupp

set_option maxRecDepth 100000 in
theorem centralizer_finRotate_seven_no_five :
    ∀ y : Perm (Fin 7), y * finRotate 7 = finRotate 7 * y → y ^ 5 = 1 → y = 1 := by
  decide +kernel

theorem comm_of_normalizes_of_pow_five {G : Type*} [Group G] (c y : G) (m : ℤ)
    (hc : orderOf c = 7) (hy : y ^ 5 = 1) (h : y * c * y⁻¹ = c ^ m) : y * c = c * y := by
  have hk : ∀ k : ℕ, y ^ k * c * (y ^ k)⁻¹ = c ^ (m ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : y ^ (k + 1) * c * (y ^ (k + 1))⁻¹ = y * (y ^ k * c * (y ^ k)⁻¹) * y⁻¹ := by
        group
      rw [e, ih, ← conj_zpow, h, ← zpow_mul]
      congr 1
      ring
  have h5 : c = c ^ (m ^ 5) := by
    simpa [hy] using hk 5
  have hdvd : (orderOf c : ℤ) ∣ m ^ 5 - 1 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, zpow_one, ← h5, mul_inv_cancel]
  rw [hc] at hdvd
  have hz : ((m ^ 5 - 1 : ℤ) : ZMod 7) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hdvd
  push_cast at hz
  have hm : (m : ZMod 7) = 1 := by
    have key : ∀ x : ZMod 7, x ^ 5 - 1 = 0 → x = 1 := by decide
    exact key _ hz
  have hm1 : (7 : ℤ) ∣ m - 1 := by
    have : ((m - 1 : ℤ) : ZMod 7) = 0 := by
      push_cast
      rw [hm, sub_self]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    exact_mod_cast this
  have hcm : c ^ m = c := by
    have h7 : (orderOf c : ℤ) ∣ m - 1 := by
      rw [hc]
      exact hm1
    have h1 : c ^ (m - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp h7
    have e : c ^ m = c ^ (m - 1) * c := by
      rw [← zpow_add_one]
      congr 1
      ring
    rw [e, h1, one_mul]
  rw [hcm, mul_inv_eq_iff_eq_mul] at h
  exact h

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem alternating_seven_no_subgroup_card_280 (H : Subgroup (alternatingGroup (Fin 7))) :
    Nat.card H ≠ 280 := by
  intro hH
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let ψ : H →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp H.subtype
  have hψ : Function.Injective ψ := fun a b h => Subtype.ext (Subtype.ext h)
  have hcard7 : 7 ∣ Nat.card H := by rw [hH]; norm_num
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' 7 hcard7
  have hfac : (Nat.card H).factorization 7 = 1 := by
    rw [hH, show (280 : ℕ) = 7 * 40 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let P : Sylow 7 H := Sylow.ofCard (Subgroup.zpowers τ)
    (by rw [Nat.card_zpowers, hτ, hfac, pow_one])
  have hmod : (Subgroup.normalizer (P : Set H)).index ≡ 1 [MOD 7] := by
    rw [← P.card_eq_index_normalizer]
    exact card_sylow_modEq_one 7 H
  have hidx : (Subgroup.normalizer (P : Set H)).index ∣ 280 := by
    rw [← hH]
    exact Subgroup.index_dvd_card _
  have hi : (Subgroup.normalizer (P : Set H)).index = 1 ∨ (Subgroup.normalizer (P : Set H)).index = 8 := by
    have small : ∀ i < 281, i ∣ 280 → i % 7 = 1 → i = 1 ∨ i = 8 := by decide +kernel
    have hle := Nat.le_of_dvd (by norm_num) hidx
    exact small _ (by omega) hidx hmod
  have h5 : 5 ∣ Nat.card (Subgroup.normalizer (P : Set H)) := by
    have hN := (Subgroup.normalizer (P : Set H)).card_mul_index
    rw [hH] at hN
    rcases hi with h1 | h1 <;> rw [h1] at hN <;> omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hx5 : orderOf (x : H) = 5 := (Subgroup.orderOf_coe x).trans hx
  have hxN : (x : H) ∈ Subgroup.normalizer (P : Set H) := x.2
  have hPsub : (P : Subgroup H) = Subgroup.zpowers τ := Sylow.coe_ofCard _ _
  have hPset : (P : Set H) = ((Subgroup.zpowers τ : Subgroup H) : Set H) :=
    congrArg SetLike.coe hPsub
  have hτP : τ ∈ (P : Set H) := by
    rw [hPset]
    exact Subgroup.mem_zpowers τ
  have hconj : (x : H) * τ * (x : H)⁻¹ ∈ Subgroup.zpowers τ := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hxN τ).mp hτP
    show _ ∈ ((Subgroup.zpowers τ : Subgroup H) : Set H)
    rw [← hPset]
    exact h1
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hconj
  have ht : orderOf (ψ τ) = 7 := by rw [orderOf_injective ψ hψ τ, hτ]
  have ha : orderOf (ψ (x : H)) = 5 := by rw [orderOf_injective ψ hψ (x : H), hx5]
  have ha5 : ψ (x : H) ^ 5 = 1 := by
    have := pow_orderOf_eq_one (ψ (x : H))
    rwa [ha] at this
  have ha1 : ψ (x : H) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ha
    norm_num at ha
  have hcon : ψ (x : H) * ψ τ * (ψ (x : H))⁻¹ = (ψ τ) ^ m := by
    have := congrArg ψ hm
    simp only [map_mul, map_inv, map_zpow] at this
    exact this.symm
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_finRotate_seven ht)
  have hy5 : (g * ψ (x : H) * g⁻¹) ^ 5 = 1 := by
    rw [conj_pow, ha5, mul_one, mul_inv_cancel]
  have hyc : (g * ψ (x : H) * g⁻¹) * finRotate 7 * (g * ψ (x : H) * g⁻¹)⁻¹
      = (finRotate 7) ^ m := by
    rw [← hg, conj_zpow, ← hcon]
    group
  have hcomm := comm_of_normalizes_of_pow_five (finRotate 7) (g * ψ (x : H) * g⁻¹) m
    orderOf_finRotate_seven hy5 hyc
  have hy1 := centralizer_finRotate_seven_no_five _ hcomm hy5
  apply ha1
  calc ψ (x : H) = g⁻¹ * (g * ψ (x : H) * g⁻¹) * g := by group
    _ = 1 := by rw [hy1]; group

theorem a7_three_dvd_card_of_index_le_fifteen (H : Subgroup (alternatingGroup (Fin 7)))
    (h15 : H.index ≤ 15) : 3 ∣ Nat.card H := by
  have hmul : Nat.card H * H.index = 2520 := by
    rw [H.card_mul_index, card_alternatingGroup_seven]
  by_contra h3
  have hcop : Nat.Coprime 9 (Nat.card H) := by
    have h3' : Nat.Coprime 3 (Nat.card H) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    simpa using h3'.pow_left 2
  have h9 : 9 ∣ H.index := by
    have h9m : 9 ∣ Nat.card H * H.index := ⟨280, by rw [hmul]⟩
    exact hcop.dvd_of_dvd_mul_left h9m
  have hidx : H.index = 9 ∨ H.index = 0 := by omega
  rcases hidx with h | h
  · have hcard : Nat.card H = 280 := by
      rw [h] at hmul
      omega
    exact alternating_seven_no_subgroup_card_280 H hcard
  · rw [h, mul_zero] at hmul
    omega

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
