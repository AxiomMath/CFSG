module

public import CFSG.CharacterTheory.Burnside
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Subgroup
open scoped Pointwise

theorem not_isSolvable_of_isPerfect {K : Type*} [Group K] [Nontrivial K] [Group.IsPerfect K] :
    ¬ Group.IsSolvable K :=
  Group.IsPerfect.not_isSolvable K

theorem exists_third_prime_dvd_card_of_not_isSolvable {K : Type*} [Group K] [Finite K]
    (hK : ¬ Group.IsSolvable K) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∃ r, r.Prime ∧ r ∣ Nat.card K ∧ r ≠ p ∧ r ≠ q := by
  by_contra hne
  push Not at hne
  have hn : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hsupp : ∀ r, r.Prime → r ∣ Nat.card K → r = p ∨ r = q := by
    intro r hr hdvd
    by_cases hrp : r = p
    · exact Or.inl hrp
    · exact Or.inr (hne r hr hdvd hrp)
  by_cases hpq : p = q
  · subst hpq
    apply hK
    have hcard : Nat.card K = p ^ (Nat.card K).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hn (fun {d} hd hdd => (hsupp d hd hdd).elim id id)
    have : Fact (Nat.Prime p) := ⟨hp⟩
    have := IsPGroup.isNilpotent (IsPGroup.of_card hcard)
    exact inferInstance
  · have hprod : (Nat.card K).factorization.prod (fun r k => r ^ k) = Nat.card K :=
      Nat.prod_factorization_pow_eq_self hn
    have hsub : (Nat.card K).factorization.support ⊆ {p, q} := by
      intro r hr
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hr
      rcases hsupp r hr.1 hr.2.1 with h | h <;> simp [h]
    have hcardEq : Nat.card K = p ^ (Nat.card K).factorization p * q ^ (Nat.card K).factorization q := by
      conv_lhs => rw [← hprod]
      rw [Finsupp.prod_of_support_subset _ hsub _ (fun i _ => pow_zero i), Finset.prod_pair hpq]
    let := Fintype.ofFinite K
    have hcardF : Fintype.card K = p ^ (Nat.card K).factorization p * q ^ (Nat.card K).factorization q := by
      rw [← Nat.card_eq_fintype_card]
      exact hcardEq
    exact hK (CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq hcardF)

theorem exists_conj_eq_of_card_eq_four {H : Type*} [Group H] [Finite H] (hH : ¬ 8 ∣ Nat.card H)
    {A B : Subgroup H} (hA : Nat.card A = 4) (hB : Nat.card B = 4) :
    ∃ h : H, A.map (MulAut.conj h).toMonoidHom = B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 4 ∣ Nat.card H := hA ▸ Subgroup.card_subgroup_dvd_card A
  have hnz : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card H).factorization 2 = 2 := by
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      have h8 : 2 ^ 3 ∣ Nat.card H := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hnz).mpr
        (by omega)
      exact hH (by norm_num at h8; exact h8)
    · have h4 : 2 ^ 2 ∣ Nat.card H := by norm_num; exact hdvd
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hnz).mp h4
  have hA' : Nat.card A = 2 ^ (Nat.card H).factorization 2 := by rw [hfac, hA]; norm_num
  have hB' : Nat.card B = 2 ^ (Nat.card H).factorization 2 := by rw [hfac, hB]; norm_num
  let P : Sylow 2 H := Sylow.ofCard A hA'
  let Q : Sylow 2 H := Sylow.ofCard B hB'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P Q
  refine ⟨g, ?_⟩
  apply SetLike.coe_injective
  have hsm : MulAut.conj g • ((A : Subgroup H) : Set H) = ((B : Subgroup H) : Set H) :=
    congrArg (fun S : Sylow 2 H => ((S : Subgroup H) : Set H)) hg
  rw [Subgroup.coe_map, ← hsm, ← Set.image_smul]
  rfl

theorem nonempty_mulEquiv_prod_of_le_center {C : Type*} [Group C] [Finite C] {A B : Subgroup C}
    (hA : A ≤ Subgroup.center C) (hAB : Disjoint A B)
    (hcard : Nat.card A * Nat.card B = Nat.card C) : Nonempty (C ≃* A × B) := by
  classical
  let f : A →* C := A.subtype
  let g : B →* C := B.subtype
  have comm : ∀ (a : A) (b : B), Commute (f a) (g b) := by
    intro a b
    have ha : (a : C) ∈ Subgroup.center C := hA a.2
    exact (Subgroup.mem_center_iff.mp ha (b : C)).symm
  let φ : A × B →* C := MonoidHom.noncommCoprod f g comm
  have hinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨Subgroup.subtype_injective A, Subgroup.subtype_injective B, ?_⟩
    simp only [f, g, Subgroup.range_subtype]
    exact hAB
  have hbij : Function.Bijective φ := by
    have := Fintype.ofFinite C
    have := Fintype.ofFinite (A × B)
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_prod, hcard]
  exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

theorem nonempty_mulEquiv_klein {E : Type*} [Group E] (h4 : Nat.card E = 4)
    (h2 : ∀ e : E, e ^ 2 = 1) :
    Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  have hexp : Monoid.exponent E = 2 := by
    have hdvd : Monoid.exponent E ∣ 2 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      have hone : ∀ x : E, x = 1 := fun x => by
        have hx := Monoid.pow_exponent_eq_one x
        rwa [h, pow_one] at hx
      have hsub : Subsingleton E := ⟨fun a b => by rw [hone a, hone b]⟩
      have := Nat.card_of_subsingleton (1 : E)
      omega
    · exact h
  have : IsKleinFour E := ⟨h4, hexp⟩
  obtain ⟨e⟩ : Nonempty (E ≃* Multiplicative (ZMod 2 × ZMod 2)) := IsKleinFour.nonempty_mulEquiv
  exact ⟨e.trans (MulEquiv.prodMultiplicative (ZMod 2) (ZMod 2))⟩

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
