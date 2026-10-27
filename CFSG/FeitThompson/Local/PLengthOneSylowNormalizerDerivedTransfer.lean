module

public import CFSG.FeitThompson.Local.PLengthOneNormalSeries
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.DerivedSubgroupCharacteristic
import CFSG.FeitThompson.Foundations.HallImageQuotient
import CFSG.FeitThompson.Local.PrimeChiefFactorsCoprimeQuotient
import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow

open Pointwise Subgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {P : Subgroup X}

theorem factorization_natCard_of_not_dvd_index {T : Subgroup X} (h : ¬ p ∣ T.index) :
    (Nat.card T).factorization p = (Nat.card X).factorization p := by
  have h1 : Nat.card T * T.index = Nat.card X := Subgroup.card_mul_index T
  rw [← h1, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd h, add_zero]

theorem factorization_natCard_quotient_pComplCore (hp : p.Prime) (X : Type*) [Group X]
    [Finite X] :
    (Nat.card (X ⧸ pComplCore p X)).factorization p = (Nat.card X).factorization p := by
  have hmul : Nat.card (pComplCore p X) * Nat.card (X ⧸ pComplCore p X) = Nat.card X := by
    rw [← Subgroup.index_eq_card]; exact Subgroup.card_mul_index _
  have h2 : (Nat.card X).factorization p
      = (Nat.card (pComplCore p X)).factorization p
        + (Nat.card (X ⧸ pComplCore p X)).factorization p := by
    rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply]
  rw [h2, Nat.factorization_eq_zero_of_not_dvd (not_dvd_natCard_pComplCore hp X), zero_add]

variable [Fact p.Prime]

theorem inf_pComplCore_eq_bot (hPp : IsPGroup p P) : pComplCore p X ⊓ P = ⊥ := by
  have hp : p.Prime := Fact.out
  rw [← Subgroup.card_eq_one]
  by_contra hne
  obtain ⟨q, hq⟩ := Nat.exists_prime_and_dvd hne
  have hq1 : q ∣ Nat.card (pComplCore p X) := hq.2.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hq2 : q ∣ Nat.card P := hq.2.trans (Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hPp
  rw [hn] at hq2
  have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq.1 hp).1 (hq.1.dvd_of_dvd_pow hq2)
  exact not_dvd_natCard_pComplCore hp X (hqp ▸ hq1)

theorem natCard_map_mk'_pComplCore (hP : Nat.card P = p ^ (Nat.card X).factorization p) :
    Nat.card (P.map (QuotientGroup.mk' (pComplCore p X)))
      = p ^ (Nat.card X).factorization p := by
  have h := natCard_map_mk'_mul_natCard_inf P (pComplCore p X)
  rw [inf_pComplCore_eq_bot (IsPGroup.of_card hP)] at h
  simpa [hP] using h

theorem natCard_pCore_quotient_pComplCore (hT : ¬ p ∣ (pComplPCore p X).index) :
    Nat.card (pCore p (X ⧸ pComplCore p X)) = p ^ (Nat.card X).factorization p := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_pCore hp (X ⧸ pComplCore p X))
  have hcard : Nat.card (pComplPCore p X)
      = Nat.card (pComplCore p X) * Nat.card (pCore p (X ⧸ pComplCore p X)) := by
    rw [pComplPCore_eq_comap]; exact natCard_comap_mk' _ _
  have hfac := factorization_natCard_of_not_dvd_index hT
  rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_natCard_pComplCore hp X), zero_add, hk,
    hp.factorization_pow, Finsupp.single_eq_same] at hfac
  rw [hk, hfac]

theorem pComplPCore_eq_pComplCore_sup (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hT : ¬ p ∣ (pComplPCore p X).index) :
    pComplPCore p X = pComplCore p X ⊔ P := by
  have hp : p.Prime := Fact.out
  set N := pComplCore p X with hN
  have hQcard : Nat.card (P.map (QuotientGroup.mk' N))
      = p ^ (Nat.card (X ⧸ N)).factorization p := by
    rw [factorization_natCard_quotient_pComplCore hp X]
    exact natCard_map_mk'_pComplCore hP
  set Q : Sylow p (X ⧸ N) := Sylow.ofCard _ hQcard with hQ
  have hQcoe : (Q : Subgroup (X ⧸ N)) = P.map (QuotientGroup.mk' N) := Sylow.coe_ofCard _ _
  have hle : pCore p (X ⧸ N) ≤ (Q : Subgroup (X ⧸ N)) :=
    IsPGroup.le_sylow_of_normal (isPGroup_pCore hp _) Q
  have heq : pCore p (X ⧸ N) = P.map (QuotientGroup.mk' N) := by
    refine Subgroup.eq_of_le_of_card_ge (hQcoe ▸ hle) ?_
    rw [natCard_pCore_quotient_pComplCore hT, natCard_map_mk'_pComplCore hP]
  rw [pComplPCore_eq_comap, heq, comap_map_mk', sup_comm]

theorem coe_pComplPCore_eq_mul (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hT : ¬ p ∣ (pComplPCore p X).index) :
    (pComplPCore p X : Set X) = (pComplCore p X : Set X) * (P : Set X) := by
  have : (pComplCore p X).Normal := Subgroup.normal_of_characteristic _
  rw [pComplPCore_eq_pComplCore_sup hP hT, Subgroup.normal_mul]

theorem pComplCore_sup_normalizer_eq_top (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hT : ¬ p ∣ (pComplPCore p X).index) :
    pComplCore p X ⊔ normalizer (P : Set X) = ⊤ := by
  have hTeq := pComplPCore_eq_pComplCore_sup hP hT
  have hPT : P ≤ pComplPCore p X := hTeq ▸ le_sup_right
  have hcard : Nat.card P = p ^ (Nat.card (pComplPCore p X)).factorization p := by
    rw [factorization_natCard_of_not_dvd_index hT, hP]
  have hfrat : pComplPCore p X ⊔ normalizer (P : Set X) = ⊤ :=
    sup_normalizer_eq_top_of_normal hPT hcard
  rwa [hTeq, sup_assoc, sup_eq_right.2 Subgroup.le_normalizer] at hfrat

theorem coe_pComplCore_mul_coe_normalizer_eq_univ
    (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hT : ¬ p ∣ (pComplPCore p X).index) :
    (pComplCore p X : Set X) * (normalizer (P : Set X) : Set X) = Set.univ := by
  have : (pComplCore p X).Normal := Subgroup.normal_of_characteristic _
  rw [← Subgroup.normal_mul, pComplCore_sup_normalizer_eq_top hP hT, Subgroup.coe_top]

theorem notMem_singleton_of_mem_primeFactors_natCard_pComplCore (hp : p.Prime) (X : Type*)
    [Group X] [Finite X] {q : ℕ} (hq : q ∈ (Nat.card (pComplCore p X)).primeFactors) :
    q ∉ ({p} : Set ℕ) := by
  rw [Set.mem_singleton_iff]
  rintro rfl
  exact not_dvd_natCard_pComplCore hp X (Nat.dvd_of_mem_primeFactors hq)

theorem inf_commutator_le_commutator_normalizer
    (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hT : ¬ p ∣ (pComplPCore p X).index) :
    P ⊓ _root_.commutator X ≤ ⁅normalizer (P : Set X), normalizer (P : Set X)⁆ :=
  IsPiSubgroup.inf_commutator_le_commutator (π := ({p} : Set ℕ))
    ((isPiSubgroup_singleton_iff Fact.out P).2 (IsPGroup.of_card hP))
    (Subgroup.normal_of_characteristic _)
    (fun _ hq => notMem_singleton_of_mem_primeFactors_natCard_pComplCore Fact.out X hq)
    (coe_pComplCore_mul_coe_normalizer_eq_univ hP hT) Subgroup.le_normalizer

theorem inf_closure_le_closure_normalizer
    (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hT : ¬ p ∣ (pComplPCore p X).index) :
    P ⊓ Subgroup.closure {g : X | ∃ x y : X, x⁻¹ * y⁻¹ * x * y = g} ≤
      Subgroup.closure
        {g : X | ∃ a ∈ normalizer (P : Set X), ∃ b ∈ normalizer (P : Set X),
          a⁻¹ * b⁻¹ * a * b = g} := by
  rw [closure_setOf_inv_mul_inv_mul_mul_eq_commutator, closure_setOf_inv_mul_inv_mul_mul]
  exact inf_commutator_le_commutator_normalizer hP hT

end

end CFSG.FeitThompson
