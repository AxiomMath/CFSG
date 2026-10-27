module

public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.Foundations.Basic

public section

namespace CFSG.OddStandard.SmallF3

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem oddCore_eq_pPrimeCore_two_local (H : Type*) [Group H] :
    CFSG.oddCore H = CFSG.pPrimeCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.oddCore_eq_piCore H).trans (CFSG.pPrimeCore_eq_piCore H 2).symm

private theorem oddCore_eq_bot_of_normal_local {H : Type*} [Group H] [Finite H]
    (hO : CFSG.oddCore H = ⊥) (K : Subgroup H) [K.Normal] : CFSG.oddCore K = ⊥ := by
  rw [oddCore_eq_pPrimeCore_two_local] at hO ⊢
  have hN : ((CFSG.pPrimeCore 2 K).map K.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hle : (CFSG.pPrimeCore 2 K).map K.subtype ≤ CFSG.pPrimeCore 2 H := by
    refine le_sSup ⟨hN, ?_⟩
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  rwa [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at hle

private theorem oddCore_eq_bot_of_mulEquiv_local {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : CFSG.oddCore A = ⊥) : CFSG.oddCore B = ⊥ := by
  rw [eq_bot_iff]
  refine sSup_le fun N hN' => ?_
  obtain ⟨hN, hodd⟩ := hN'
  have h1 : N.map e.symm.toMonoidHom ≤ CFSG.oddCore A :=
    le_sSup ⟨hN.map _ e.symm.surjective,
      by rwa [Subgroup.card_map_of_injective e.symm.injective]⟩
  rw [h] at h1
  intro x hx
  have hx1 : e.symm x ∈ (⊥ : Subgroup A) := h1 ⟨x, hx, rfl⟩
  rw [mem_bot, MulEquiv.symm_apply_eq, map_one] at hx1
  rw [mem_bot]
  exact hx1

theorem oddCore_eq_bot_of_balanced (hS : StandardSetting G L)
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) :
    CFSG.oddCore ↥L = ⊥ := by
  have ht2dvd : 2 ∣ Nat.card (centralizer (L : Set G)) :=
    even_iff_two_dvd.mp hS.standard.2.1
  obtain ⟨u, hu2⟩ :=
    exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) 2 ht2dvd
  let t : G := u
  have ht : t ∈ Subgroup.centralizer (L : Set G) := u.2
  have ht2 : orderOf t = 2 := by
    show orderOf (u : G) = 2
    rw [Subgroup.orderOf_coe]
    exact hu2
  obtain ⟨-, hLT, hLn, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      hS.standard ht ht2
  haveI : (L.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal := hLn
  have hOK : CFSG.oddCore ↥(L.subgroupOf (Subgroup.centralizer ({t} : Set G))) = ⊥ :=
    oddCore_eq_bot_of_normal_local (hbal t ht2)
      (L.subgroupOf (Subgroup.centralizer ({t} : Set G)))
  exact oddCore_eq_bot_of_mulEquiv_local (Subgroup.subgroupOfEquivOfLe hLT) hOK

theorem isPGroup_two_center_of_balanced (hS : StandardSetting G L)
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) :
    IsPGroup 2 (center L) := by
  have hbot : CFSG.oddCore ↥L = ⊥ := oddCore_eq_bot_of_balanced hS hbal
  have huniq : ∀ {d : ℕ}, Nat.Prime d → d ∣ Nat.card (center L) → d = 2 := by
    intro d hd hdvd
    by_contra hd2
    haveI : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := center L) d hdvd
    have hodd : Odd (Nat.card (Subgroup.zpowers (x : ↥L))) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
      exact hd.odd_of_ne_two hd2
    have hle : Subgroup.zpowers (x : ↥L) ≤ CFSG.oddCore ↥L :=
      le_sSup ⟨Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr x.2), hodd⟩
    have hx1 : (x : ↥L) = 1 := by
      have := hle (Subgroup.mem_zpowers (x : ↥L))
      rwa [hbot, Subgroup.mem_bot] at this
    have hx1' : x = 1 := Subtype.ext hx1
    have hd1 : d = 1 := by rw [← hx, hx1', orderOf_one]
    exact hd.ne_one hd1
  haveI : Nonempty ↥(center L) := ⟨1⟩
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' huniq)

theorem center_eq_bot_or_even_card (hS : StandardSetting G L)
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) :
    center L = ⊥ ∨ Even (Nat.card (center L)) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_two_center_of_balanced hS hbal)
  rcases n with _ | k
  · left
    exact Subgroup.eq_bot_of_card_eq (center L) (by simpa using hn)
  · right
    rw [hn]
    exact even_two.pow_of_ne_zero (Nat.succ_ne_zero k)

end CFSG.OddStandard.SmallF3
