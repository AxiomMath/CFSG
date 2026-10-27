
module

public import CFSG.LocalAnalysis.SectionRank.SylowWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J3LocalDet
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HSLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Ru
public import CFSG.LocalAnalysis.SectionRank.OddCover.CubicKernel

@[expose] public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

theorem not_sq_dvd_mul_of_coprime {r A m : ℕ} (hr : Nat.Coprime r A) (hm : ¬ r ^ 2 ∣ m) :
    ¬ r ^ 2 ∣ A * m := fun h =>
  hm ((Nat.Coprime.pow_left 2 hr).dvd_of_dvd_mul_left h)

theorem coprime_pow_of_ne {r p : ℕ} (hr : r.Prime) (hp : p.Prime) (hne : r ≠ p) (k : ℕ) :
    Nat.Coprime r (p ^ k) :=
  Nat.Coprime.pow_right _ ((Nat.coprime_primes hr hp).2 hne)

theorem not_sq_dvd_prod_primes {r : ℕ} (hr : r.Prime) :
    ∀ {l : List ℕ}, (∀ p ∈ l, p.Prime) → l.Nodup → ¬ r ^ 2 ∣ l.prod
  | [], _, _, h => by
    rw [List.prod_nil, Nat.dvd_one] at h
    have : 2 ≤ r := hr.two_le
    nlinarith
  | p :: l, hl, hnd, h => by
    rw [List.prod_cons] at h
    have hp : p.Prime := hl p List.mem_cons_self
    have hl' : ∀ q ∈ l, q.Prime := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hpl : p ∉ l := (List.nodup_cons.1 hnd).1
    by_cases hrp : r = p
    · subst hrp
      have h2 : r ∣ l.prod := by
        rw [sq] at h
        exact Nat.dvd_of_mul_dvd_mul_left hr.pos h
      obtain ⟨a, ha, hra⟩ := (Nat.prime_iff.1 hr).dvd_prod_iff.1 h2
      exact hpl ((Nat.prime_dvd_prime_iff_eq hr (hl' a ha)).1 hra ▸ ha)
    · exact not_sq_dvd_prod_primes hr hl' (List.nodup_cons.1 hnd).2
        ((Nat.Coprime.pow_left 2 ((Nat.coprime_primes hr hp).2 hrp)).dvd_of_dvd_mul_left h)

theorem not_sq_dvd_of_factorization {r A : ℕ} (hr : r.Prime) (hA : Nat.Coprime r A)
    (l : List ℕ) (hl : ∀ p ∈ l, p.Prime) (hnd : l.Nodup) : ¬ r ^ 2 ∣ A * l.prod :=
  not_sq_dvd_mul_of_coprime hA (not_sq_dvd_prod_primes hr hl hnd)

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

theorem J2_perfect_odd_cover_trivial
    (π : E →* NativeSporadic.J2) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have hcard := CFSG.Sporadic.J2.card_J2
  refine ker_eq_bot_of_sylow_kernel_eq_bot π hπ hC hodd fun r hr hr2 hsq _ Cp => ?_
  by_cases h3 : r = 3
  · subst h3
    obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := J2_sylow3_cubic_witness
    exact OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hx hy hz hzx hzy hQ
      (by rw [hcard]; decide) hhx hhy hhz (by decide +revert) Cp
  by_cases h5 : r = 5
  · subst h5
    obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := J2_sylow5_square_witness
    exact sylow_kernel_eq_bot_of_square_witness π hπ hC hx hy hxy hQ (by rw [hcard]; decide)
      hhx hhy (by decide +revert) Cp
  · exfalso
    rw [hcard, show 604800 = (2 ^ 7 * 3 ^ 3 * 5 ^ 2) * [7].prod by norm_num] at hsq
    exact not_sq_dvd_of_factorization hr (Nat.Coprime.mul_right (Nat.Coprime.mul_right
      (coprime_pow_of_ne hr Nat.prime_two hr2 _) (coprime_pow_of_ne hr Nat.prime_three h3 _))
      (coprime_pow_of_ne hr (by norm_num) h5 _)) _ (by norm_num) (by decide) hsq

theorem HS_perfect_odd_cover_trivial
    (π : E →* NativeSporadic.HS) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have hcard := CFSG.Sporadic.HS.card_HS
  refine ker_eq_bot_of_sylow_kernel_eq_bot π hπ hC hodd fun r hr hr2 hsq _ Cp => ?_
  by_cases h3 : r = 3
  · subst h3
    obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := HS_sylow3_square_witness
    exact sylow_kernel_eq_bot_of_square_witness π hπ hC hx hy hxy hQ (by rw [hcard]; decide)
      hhx hhy (by decide +revert) Cp
  by_cases h5 : r = 5
  · subst h5
    obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := HS_sylow5_cubic_witness
    exact OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hx hy hz hzx hzy hQ
      (by rw [hcard]; decide) hhx hhy hhz (by decide +revert) Cp
  · exfalso
    rw [hcard, show 44352000 = (2 ^ 9 * 3 ^ 2 * 5 ^ 3) * [7, 11].prod by norm_num] at hsq
    exact not_sq_dvd_of_factorization hr (Nat.Coprime.mul_right (Nat.Coprime.mul_right
      (coprime_pow_of_ne hr Nat.prime_two hr2 _) (coprime_pow_of_ne hr Nat.prime_three h3 _))
      (coprime_pow_of_ne hr (by norm_num) h5 _)) _ (by norm_num) (by decide) hsq

theorem He_perfect_odd_cover_trivial
    (π : E →* NativeSporadic.He) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have hcard := CFSG.Sporadic.He.card_He
  refine ker_eq_bot_of_sylow_kernel_eq_bot π hπ hC hodd fun r hr hr2 hsq _ Cp => ?_
  by_cases h3 : r = 3
  · subst h3
    obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := He_sylow3_cubic_witness
    exact OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hx hy hz hzx hzy hQ
      (by rw [hcard]; decide) hhx hhy hhz (by decide +revert) Cp
  by_cases h5 : r = 5
  · subst h5
    obtain ⟨x, y, h, hx, hy, hxy, hQ, hhx, hhy⟩ := He_sylow5_square_witness
    exact sylow_kernel_eq_bot_of_square_witness π hπ hC hx hy hxy hQ (by rw [hcard]; decide)
      hhx hhy (by decide +revert) Cp
  by_cases h7 : r = 7
  · subst h7
    obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := He_sylow7_cubic_witness
    exact OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hx hy hz hzx hzy hQ
      (by rw [hcard]; decide) hhx hhy hhz (by decide +revert) Cp
  · exfalso
    rw [hcard, show 4030387200 = (2 ^ 10 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3) * [17].prod by norm_num] at hsq
    exact not_sq_dvd_of_factorization hr (Nat.Coprime.mul_right (Nat.Coprime.mul_right
      (Nat.Coprime.mul_right (coprime_pow_of_ne hr Nat.prime_two hr2 _)
        (coprime_pow_of_ne hr Nat.prime_three h3 _)) (coprime_pow_of_ne hr (by norm_num) h5 _))
      (coprime_pow_of_ne hr (by norm_num) h7 _)) _ (by norm_num) (by decide) hsq

theorem Ru_perfect_odd_cover_trivial
    (π : E →* NativeSporadic.Ru) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have hcard := CFSG.Sporadic.Ru.card_Ru
  refine ker_eq_bot_of_sylow_kernel_eq_bot π hπ hC hodd fun r hr hr2 hsq _ Cp => ?_
  by_cases h3 : r = 3
  · subst h3
    obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := Ru_sylow3_cubic_witness
    exact OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hx hy hz hzx hzy hQ
      (by rw [hcard]; decide) hhx hhy hhz (by decide +revert) Cp
  by_cases h5 : r = 5
  · subst h5
    obtain ⟨x, y, h, hx, hy, hz, hzx, hzy, hQ, hhx, hhy, hhz⟩ := Ru_sylow5_cubic_witness
    exact OddCover.cubic_extraspecial_sylow_central_kernel π hπ hC hx hy hz hzx hzy hQ
      (by rw [hcard]; decide) hhx hhy hhz (by decide +revert) Cp
  · exfalso
    rw [hcard, show 145926144000 = (2 ^ 14 * 3 ^ 3 * 5 ^ 3) * [7, 13, 29].prod by norm_num] at hsq
    exact not_sq_dvd_of_factorization hr (Nat.Coprime.mul_right (Nat.Coprime.mul_right
      (coprime_pow_of_ne hr Nat.prime_two hr2 _) (coprime_pow_of_ne hr Nat.prime_three h3 _))
      (coprime_pow_of_ne hr (by norm_num) h5 _)) _ (by norm_num) (by decide) hsq

@[expose] def J4OrderHyp : Prop :=
  Nat.card NativeSporadic.J4 ∣ 86775571046077562880

theorem central_quotient_exclusion_of_three_rank_four {G T : Type} [Group G] [Finite G] [Group T]
    (hSQT : IsStronglyQuasithin G) (A : Subgroup G) [A.Normal] (hAZ : A ≤ Subgroup.center G)
    (hT : ∃ E : Subgroup T, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) : IsEmpty (G ⧸ A ≃* T) := by
  refine ⟨fun e => ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite T := Finite.of_equiv _ e.toEquiv
  obtain ⟨E, hE, hcard⟩ := hT
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup T) := le_pRank (by norm_num) le_top hE hcard
  rw [← pRank_top_eq_of_mulEquiv (by norm_num) e] at h4
  have h3 := pRank_quotient_le_three (by norm_num)
    (isStronglyQuasithin_iff.1 hSQT 3 Nat.prime_three (by norm_num)) A hAZ
  omega

theorem odd_central_quotient_exclusion_of_local_det {G T : Type} [Group G] [Finite G] [Group T]
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hSQT : IsStronglyQuasithin G) (A : Subgroup G)
    [A.Normal] (hAZ : A ≤ Subgroup.center G) (hA : Odd (Nat.card A))
    (hw : ∃ K : Subgroup T, ∃ (_ : Group.IsPerfect K), ∃ (Q : Sylow p K) (x y : K) (h cc : T)
      (a b c d : ℕ), IsElemAbelian p (Q : Subgroup K) ∧ Nat.card (Q : Subgroup K) = p ^ 2 ∧
      (∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ R : Sylow r K, IsCyclic (R : Subgroup K)) ∧
      h ∈ Subgroup.normalizer (K : Set T) ∧ Subgroup.closure ({x, y} : Set K) = Q ∧
      h * x * h⁻¹ = (x : T) ^ a * (y : T) ^ c ∧ h * y * h⁻¹ = (x : T) ^ b * (y : T) ^ d ∧
      ((a * d - b * c : ℤ) : ZMod p) ≠ 1 ∧ (∀ k ∈ K, Commute cc k) ∧ orderOf cc = p ∧
      Subgroup.zpowers cc ⊓ K = ⊥) :
    IsEmpty (G ⧸ A ≃* T) := by
  refine ⟨fun e => ?_⟩
  have : Finite T := Finite.of_equiv _ e.toEquiv
  set π : G →* T := e.toMonoidHom.comp (QuotientGroup.mk' A) with hπdef
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective A)
  have hker : π.ker = A := by
    ext g
    rw [hπdef, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨K, hKp, Q, x, y, h, cc, a, b, c, d, hQ, hQcard, hcyc, hhK, hgen, hx, hy, hdet, hcK,
    hcc, hcK1⟩ := hw
  obtain ⟨E3, hE3, hcard⟩ := perfect_local_det_cover_rank K Q hQ hQcard hcyc h hhK hgen hx hy
    hdet cc hcK hcc hcK1 π hπ (hker ▸ hAZ) (hker ▸ hA)
  have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := le_pRank hp.out.one_lt le_top hE3 hcard
  have := isStronglyQuasithin_iff.1 hSQT p hp.out hp2
  omega

theorem J3_odd_central_quotient_exclusion
    {G : Type} [Group G] [Finite G]
    (hSQT : IsStronglyQuasithin G) (A : Subgroup G) [A.Normal] (hAZ : A ≤ Subgroup.center G)
    (hA : Odd (Nat.card A)) : IsEmpty (G ⧸ A ≃* NativeSporadic.J3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hKp, Q, x, y, h, cc, a, b, c, d, -, hQ, hQcard, hcyc, hhK, hgen, hx, hy, hdet, hcK,
    hcc, hcK1⟩ := J3_perfect_local_det_witness
  exact odd_central_quotient_exclusion_of_local_det (T := NativeSporadic.J3) (p := 3)
    (by norm_num) hSQT A hAZ hA
    ⟨K, hKp, Q, x, y, h, cc, a, b, c, d, hQ, hQcard, hcyc, hhK, hgen, hx, hy, hdet, hcK, hcc,
      hcK1⟩

end CFSG.SectionRank
