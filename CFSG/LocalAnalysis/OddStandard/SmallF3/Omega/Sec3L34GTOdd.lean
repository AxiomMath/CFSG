module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

private theorem l34g_odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem l34g_exists_odd_lift {A C : Type} [Group A] [Group C] [Finite A] (φ : A →* C)
    (hφ : Function.Surjective φ) {c : C} (hc : Odd (orderOf c)) :
    ∃ a : A, φ a = c ∧ Odd (orderOf a) := by
  classical
  obtain ⟨d, hd⟩ := hφ c
  have hd0 : orderOf d ≠ 0 := (orderOf_pos d).ne'
  obtain ⟨s, m, hm_odd, hs⟩ := Nat.exists_eq_two_pow_mul_odd hd0
  have hd'pow : (d ^ (2 ^ s)) ^ m = 1 := by
    rw [← pow_mul, ← hs, pow_orderOf_eq_one]
  have hd'odd : Odd (orderOf (d ^ (2 ^ s))) :=
    hm_odd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hd'pow)
  have hcop : Nat.Coprime (2 ^ s) (orderOf c) :=
    (Nat.coprime_two_left.mpr hc).pow_left s
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(d ^ (2 ^ s)) ^ k, ?_, ?_⟩
  · rw [map_pow, map_pow, hd, hk]
  · exact hd'odd.of_dvd_nat (orderOf_pow_dvd k)

theorem l34g_isSL23Mod_of_odd_ker {A C : Type} [Group A] [Group C] [Finite A] (ψ : A →* C)
    (hψ : Function.Surjective ψ) (hodd : Odd (Nat.card ψ.ker)) (h : IsSL23Mod C) :
    IsSL23Mod A := by
  classical
  haveI : Finite C := Finite.of_surjective ψ hψ
  let θ : A →* C ⧸ oddCore C := (QuotientGroup.mk' (oddCore C)).comp ψ
  have hθ : Function.Surjective θ := by
    intro y
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (oddCore C) y
    obtain ⟨a, ha⟩ := hψ c
    exact ⟨a, by
      show QuotientGroup.mk' (oddCore C) (ψ a) = y
      rw [ha, hc]⟩
  have hKodd : Odd (Nat.card ((oddCore C).comap ψ)) := by
    let f : ((oddCore C).comap ψ) →* oddCore C :=
      (ψ.comp ((oddCore C).comap ψ).subtype).codRestrict (oddCore C)
        (fun k => Subgroup.mem_comap.mp k.2)
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨a, ha⟩ := hψ (y : C)
      exact ⟨⟨a, Subgroup.mem_comap.mpr (by rw [ha]; exact y.2)⟩, Subtype.ext ha⟩
    have hfker : f.ker = ψ.ker.subgroupOf ((oddCore C).comap ψ) := by
      dsimp only [f]
      rw [MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker, Subgroup.comap_subtype]
    have hcard : Nat.card f.ker = Nat.card ψ.ker := by
      rw [hfker]
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (MonoidHom.ker_le_comap ψ (oddCore C))).toEquiv
    rw [← Subgroup.card_ker_mul_card_of_surjective hf]
    exact (hcard.symm ▸ hodd).mul (l34g_odd_card_oddCore C)
  have hθker : θ.ker = (oddCore C).comap ψ := by
    dsimp only [θ]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hKle : (oddCore C).comap ψ ≤ oddCore A := by
    change (oddCore C).comap ψ ≤ sSup {N : Subgroup A | N.Normal ∧ Odd (Nat.card N)}
    exact le_sSup ⟨(CFSG.oddCore_normal (G := C)).comap ψ, hKodd⟩
  have hCore_le : oddCore A ≤ (oddCore C).comap ψ := by
    change sSup {N : Subgroup A | N.Normal ∧ Odd (Nat.card N)} ≤ (oddCore C).comap ψ
    refine sSup_le ?_
    intro N hN
    have hmap : N.map ψ ≤ oddCore C := by
      change N.map ψ ≤ sSup {M : Subgroup C | M.Normal ∧ Odd (Nat.card M)}
      exact le_sSup ⟨hN.1.map ψ hψ, hN.2.of_dvd_nat (Subgroup.card_map_dvd N ψ)⟩
    exact Subgroup.map_le_iff_le_comap.mp hmap
  have hker : θ.ker = oddCore A := hθker.trans (le_antisymm hKle hCore_le)
  obtain ⟨e⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective θ hθ).trans e)⟩

end CFSG.OddStandard.SmallF3.Omega
