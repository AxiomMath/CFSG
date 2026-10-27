module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Misc2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem odd_card_oddCore_l34g (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem l34g_card_le_two_of_central_two [Finite G] {I : Subgroup G} (hI : InFStar I)
    {N : Subgroup G} (hNI : N ≤ I) (hNc : ∀ n ∈ N, ∀ a ∈ I, a * n = n * a)
    (hN2 : IsPGroup 2 ↥N) : Nat.card ↥N ≤ 2 := by
  by_cases hbot : N = ⊥
  · rw [hbot, Subgroup.card_bot]
    norm_num
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnt : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hbot
    obtain ⟨k, hkpos, hkcard⟩ := hN2.nontrivial_iff_card.mp hnt
    have hdvd : 2 ∣ Nat.card ↥N := by
      rw [hkcard]
      exact (by norm_num : 2 ∣ 2 ^ (1 : ℕ)).trans (pow_dvd_pow 2 (Nat.succ_le_of_lt hkpos))
    obtain ⟨u₀, hu₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 hdvd
    let u : G := (u₀ : G)
    have hu : orderOf u = 2 := (Subgroup.orderOf_coe u₀).trans hu₀
    have huI : u ∈ I := hNI u₀.2
    have hcu : ∀ a ∈ I, a * u = u * a := fun a ha => hNc (u₀ : G) u₀.2 a ha
    have hT : IsTwoU43 (↥I ⧸ oddCore ↥I) := isTwoU43_of_mem_center hI hu huI hcu
    let ψ : ↥N →* (↥I ⧸ oddCore ↥I) :=
      (QuotientGroup.mk' (oddCore ↥I)).comp (Subgroup.inclusion hNI)
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro n hn
      have h1 : QuotientGroup.mk' (oddCore ↥I) (Subgroup.inclusion hNI n) = 1 :=
        MonoidHom.mem_ker.mp hn
      have hy : Subgroup.inclusion hNI n ∈ oddCore ↥I := by
        have h2 := MonoidHom.mem_ker.mpr h1
        rwa [QuotientGroup.ker_mk'] at h2
      have hodeq : orderOf (Subgroup.inclusion hNI n) = orderOf n :=
        orderOf_injective (Subgroup.inclusion hNI) (Subgroup.inclusion_injective hNI) n
      have hodd : Odd (orderOf n) := by
        have hdiv : orderOf n ∣ Nat.card (oddCore ↥I) :=
          hodeq ▸ Subgroup.orderOf_dvd_natCard (oddCore ↥I) hy
        exact (odd_card_oddCore_l34g ↥I).of_dvd_nat hdiv
      obtain ⟨m, hm⟩ := hN2 n
      have h2dvd : orderOf n ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
      obtain ⟨i, -, hix⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2dvd
      rcases i with _ | i
      · rw [pow_zero] at hix
        exact orderOf_eq_one_iff.mp hix
      · exfalso
        rw [hix] at hodd
        exact (Nat.not_even_iff_odd.mpr hodd)
          (even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.succ_ne_zero i)))
    have hmem : ∀ n : ↥N, ψ n ∈ Subgroup.center (↥I ⧸ oddCore ↥I) := by
      intro n
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (oddCore ↥I) q
      show QuotientGroup.mk' (oddCore ↥I) a *
          QuotientGroup.mk' (oddCore ↥I) (Subgroup.inclusion hNI n) =
        QuotientGroup.mk' (oddCore ↥I) (Subgroup.inclusion hNI n) *
          QuotientGroup.mk' (oddCore ↥I) a
      simp only [← map_mul]
      congr 1
      exact Subtype.ext (hNc (n : G) n.2 a a.2)
    let ψ' : ↥N →* ↥(Subgroup.center (↥I ⧸ oddCore ↥I)) :=
      ψ.codRestrict (Subgroup.center (↥I ⧸ oddCore ↥I)) hmem
    have hinj' : Function.Injective ψ' :=
      (MonoidHom.injective_codRestrict ψ (Subgroup.center (↥I ⧸ oddCore ↥I)) hmem).mpr hinj
    have hle : Nat.card ↥N ≤ Nat.card ↥(Subgroup.center (↥I ⧸ oddCore ↥I)) :=
      Nat.card_le_card_of_injective ψ' hinj'
    exact hle.trans_eq hT.1

end CFSG.OddStandard.SmallF3.Omega
