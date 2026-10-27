module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem odd_card_oddCore' (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem injective_mk_comp_of_odd {A : Type} [Group A] (N : Subgroup A) [N.Normal]
    (hN : Odd (Nat.card N)) {f : QuaternionGroup 2 →* A} (hf : Function.Injective f) :
    Function.Injective ((QuotientGroup.mk' N).comp f) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : f g ∈ N := (QuotientGroup.eq_one_iff (f g)).mp (by simpa using hg)
  have hcard : Nat.card (QuaternionGroup 2) = 8 := by
    haveI : NeZero 2 := ⟨by norm_num⟩
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h8 : orderOf g ∣ 8 := by
    rw [← hcard]
    exact orderOf_dvd_natCard g
  have hNcard : orderOf g ∣ Nat.card N := by
    rw [← orderOf_injective f hf g]
    exact N.orderOf_dvd_natCard hmem
  have hcop : Nat.Coprime 8 (Nat.card N) := by
    have h2 : Nat.Coprime 2 (Nat.card N) := Nat.coprime_two_left.mpr hN
    have hpow : Nat.Coprime (2 ^ 3) (Nat.card N) :=
      (Nat.coprime_pow_left_iff (n := 3) (by norm_num) 2 (Nat.card N)).mpr h2
    simpa using hpow
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h8 hNcard)

theorem exists_injective_quotient_oddCore [Finite G] {I : Subgroup G}
    {f : QuaternionGroup 2 →* G} (hf : Function.Injective f) (hI : f.range ≤ I) :
    ∃ f' : QuaternionGroup 2 →* ↥I ⧸ oddCore ↥I, Function.Injective f' ∧
      ∀ g, f' g = QuotientGroup.mk (⟨f g, hI ⟨g, rfl⟩⟩ : ↥I) := by
  let F : QuaternionGroup 2 →* ↥I := f.codRestrict I (fun g => hI ⟨g, rfl⟩)
  let f' : QuaternionGroup 2 →* ↥I ⧸ oddCore ↥I :=
    (QuotientGroup.mk' (oddCore ↥I)).comp F
  refine ⟨f', ?_, ?_⟩
  · have hF : Function.Injective F := by
      change Function.Injective (f.codRestrict I (fun g => hI ⟨g, rfl⟩))
      rw [MonoidHom.injective_codRestrict]
      exact hf
    exact injective_mk_comp_of_odd (oddCore ↥I) (odd_card_oddCore' ↥I) hF
  · intro g
    rfl

end CFSG.OddStandard.SmallF3.Omega

end
