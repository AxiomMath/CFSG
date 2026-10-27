module

public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
public import CFSG.FeitThompson.Foundations.NilpotentNormalizerCondition

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {X : Type*} [Group X] {π π' : Set ℕ}

def sylowPiPart (π : Set ℕ) (X : Type*) [Group X] : Subgroup X :=
  ⨆ p ∈ {q : ℕ | q ∈ π ∧ q.Prime}, ⨆ P : Sylow p X, (P : Subgroup X)

theorem sylowPiPart_eq_iSup (π : Set ℕ) (X : Type*) [Group X] :
    sylowPiPart π X = ⨆ p ∈ {q : ℕ | q ∈ π ∧ q.Prime}, ⨆ P : Sylow p X, (P : Subgroup X) := (rfl)

theorem sylow_le_sylowPiPart {p : ℕ} (hp : p.Prime) (hπ : p ∈ π) (P : Sylow p X) :
    (P : Subgroup X) ≤ sylowPiPart π X := by
  rw [sylowPiPart_eq_iSup]
  refine le_trans ?_ (le_iSup₂ (f := fun (q : ℕ) (_ : q ∈ {q : ℕ | q ∈ π ∧ q.Prime}) =>
    ⨆ P : Sylow q X, (P : Subgroup X)) p ⟨hπ, hp⟩)
  exact le_iSup (fun Q : Sylow p X => (Q : Subgroup X)) P

theorem sylowPiPart_le {K : Subgroup X}
    (h : ∀ p : ℕ, p.Prime → p ∈ π → ∀ P : Sylow p X, (P : Subgroup X) ≤ K) :
    sylowPiPart π X ≤ K := by
  rw [sylowPiPart_eq_iSup]
  exact iSup₂_le fun p hp => iSup_le fun P => h p hp.2 hp.1 P

theorem sylowPiPart_mono (h : π ⊆ π') : sylowPiPart π X ≤ sylowPiPart π' X :=
  sylowPiPart_le fun _ hp hπ P => sylow_le_sylowPiPart hp (h hπ) P

theorem sylowPiPart_empty (X : Type*) [Group X] : sylowPiPart (∅ : Set ℕ) X = ⊥ :=
  le_bot_iff.1 (sylowPiPart_le fun _ _ hπ _ => absurd hπ (Set.notMem_empty _))

instance sylowPiPart_characteristic (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    (sylowPiPart π X).Characteristic := by
  refine Subgroup.characteristic_iff_map_le.2 fun ϕ => ?_
  rw [Subgroup.map_le_iff_le_comap]
  refine sylowPiPart_le fun p hp hπ P => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card ((P : Subgroup X).map ϕ.toMonoidHom)
      = p ^ (Nat.card X).factorization p := by
    rw [Subgroup.card_map_of_injective ϕ.injective, P.card_eq_multiplicity]
  have h := sylow_le_sylowPiPart (π := π) hp hπ (Sylow.ofCard _ hcard)
  rwa [Sylow.coe_ofCard] at h

instance sylowPiPart_normal (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    (sylowPiPart π X).Normal :=
  Subgroup.normal_of_characteristic _

theorem sylowPiPart_map_equiv (π : Set ℕ) (X : Type*) [Group X] [Finite X] (ϕ : X ≃* X) :
    (sylowPiPart π X).map ϕ.toMonoidHom = sylowPiPart π X :=
  Subgroup.characteristic_iff_map_eq.1 (sylowPiPart_characteristic π X) ϕ

theorem finite_setOf_mem_and_mem_primeFactors (π : Set ℕ) (X : Type*) [Group X] :
    {p : ℕ | p ∈ π ∧ p ∈ (Nat.card X).primeFactors}.Finite :=
  Set.Finite.subset (Nat.card X).primeFactors.finite_toSet fun _ hp => hp.2

noncomputable def piPrimeFactors (π : Set ℕ) (X : Type*) [Group X] : Finset ℕ :=
  (finite_setOf_mem_and_mem_primeFactors π X).toFinset

@[simp]
theorem mem_piPrimeFactors {p : ℕ} :
    p ∈ piPrimeFactors π X ↔ p ∈ π ∧ p ∈ (Nat.card X).primeFactors :=
  Set.Finite.mem_toFinset _

theorem prime_of_mem_piPrimeFactors {p : ℕ} (hp : p ∈ piPrimeFactors π X) : p.Prime :=
  Nat.prime_of_mem_primeFactors (mem_piPrimeFactors.1 hp).2

theorem sylowPiPart_eq_iSup_piPrimeFactors (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    sylowPiPart π X = ⨆ p ∈ piPrimeFactors π X, ⨆ P : Sylow p X, (P : Subgroup X) := by
  refine le_antisymm (sylowPiPart_le fun p hp hπ P => ?_) ?_
  · by_cases hd : p ∣ Nat.card X
    · refine le_trans ?_ (le_iSup₂ (f := fun (q : ℕ) (_ : q ∈ piPrimeFactors π X) =>
        ⨆ P : Sylow q X, (P : Subgroup X)) p
        (mem_piPrimeFactors.2 ⟨hπ, Nat.mem_primeFactors.2 ⟨hp, hd, Nat.card_pos.ne'⟩⟩))
      exact le_iSup (fun Q : Sylow p X => (Q : Subgroup X)) P
    · have h1 : (P : Subgroup X) = ⊥ := by
        refine Subgroup.card_eq_one.1 ?_
        have : Fact p.Prime := ⟨hp⟩
        rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hd, pow_zero]
      rw [h1]
      exact bot_le
  · exact iSup₂_le fun p hp => iSup_le fun P =>
      sylow_le_sylowPiPart (prime_of_mem_piPrimeFactors hp) (mem_piPrimeFactors.1 hp).1 P

theorem sylowPiPart_eq_bot (π : Set ℕ) (X : Type*) [Group X] [Finite X]
    (h : piPrimeFactors π X = ∅) : sylowPiPart π X = ⊥ := by
  rw [sylowPiPart_eq_iSup_piPrimeFactors, h]
  simp

variable [Finite X]

theorem pow_factorization_dvd_natCard_sylowPiPart {p : ℕ} (hp : p.Prime) (hπ : p ∈ π) :
    p ^ (Nat.card X).factorization p ∣ Nat.card (sylowPiPart π X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p X) := inferInstance
  have h := Subgroup.card_dvd_of_le (sylow_le_sylowPiPart hp hπ P)
  rwa [P.card_eq_multiplicity] at h

theorem factorization_natCard_sylowPiPart {p : ℕ} (hp : p.Prime) (hπ : p ∈ π) :
    (Nat.card (sylowPiPart π X)).factorization p = (Nat.card X).factorization p := by
  refine le_antisymm ?_ ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
    (pow_factorization_dvd_natCard_sylowPiPart hp hπ))
  exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
    (Subgroup.card_subgroup_dvd_card _) p

theorem not_dvd_index_sylowPiPart {p : ℕ} (hp : p.Prime) (hπ : p ∈ π) :
    ¬ p ∣ (sylowPiPart π X).index := by
  intro h
  have hdvd : p ^ ((Nat.card X).factorization p + 1) ∣
      Nat.card (sylowPiPart π X) * (sylowPiPart π X).index := by
    rw [pow_succ]
    exact mul_dvd_mul (pow_factorization_dvd_natCard_sylowPiPart hp hπ) h
  rw [Subgroup.card_mul_index] at hdvd
  have := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  omega

theorem isPiNumber_compl_index_sylowPiPart (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    IsPiNumber πᶜ (sylowPiPart π X).index :=
  isPiNumber_compl_iff.2 fun _ hq hq' =>
    not_dvd_index_sylowPiPart (Nat.prime_of_mem_primeFactors hq) hq'
      (Nat.dvd_of_mem_primeFactors hq)

theorem isPiSubgroup_sylowPiPart (π : Set ℕ) (X : Type*) [Group X] [Finite X]
    [Group.IsNilpotent X] : IsPiSubgroup π (sylowPiPart π X) := by
  refine (isPiSubgroup_piCore π X).of_le (sylowPiPart_le fun p hp hπ P => ?_)
  have : Fact p.Prime := ⟨hp⟩
  exact le_piCore (sylow_normal_of_isNilpotent P)
    (((isPiSubgroup_singleton_iff hp _).2 P.isPGroup').mono (Set.singleton_subset_iff.2 hπ))

theorem natCard_sylowPiPart (π : Set ℕ) (X : Type*) [Group X] [Finite X] [Group.IsNilpotent X] :
    Nat.card (sylowPiPart π X)
      = ∏ p ∈ piPrimeFactors π X, p ^ (Nat.card X).factorization p := by
  refine Nat.eq_of_factorization_eq Nat.card_pos.ne' (Finset.prod_ne_zero_iff.2 ?_) fun q => ?_
  · exact fun p hp => pow_ne_zero _ (prime_of_mem_piPrimeFactors hp).pos.ne'
  · rw [Nat.factorization_prod fun p hp => pow_ne_zero _ (prime_of_mem_piPrimeFactors hp).pos.ne']
    simp only [Finsupp.finsetSum_apply]
    have h1 : ∀ p ∈ piPrimeFactors π X,
        ((p ^ (Nat.card X).factorization p).factorization) q
          = if q = p then (Nat.card X).factorization p else 0 := by
      intro p hp
      rw [(prime_of_mem_piPrimeFactors hp).factorization_pow, Finsupp.single_apply]
      simp [eq_comm]
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq]
    by_cases hq : q ∈ piPrimeFactors π X
    · simp only [hq, if_true]
      exact factorization_natCard_sylowPiPart (prime_of_mem_piPrimeFactors hq)
        (mem_piPrimeFactors.1 hq).1
    · simp only [hq, if_false]
      rw [Nat.factorization_eq_zero_iff]
      by_cases hqp : q.Prime
      · refine Or.inr (Or.inl fun hd => hq ?_)
        have hmem : q ∈ (Nat.card (sylowPiPart π X)).primeFactors :=
          Nat.mem_primeFactors.2 ⟨hqp, hd, Nat.card_pos.ne'⟩
        exact mem_piPrimeFactors.2 ⟨isPiSubgroup_iff.1 (isPiSubgroup_sylowPiPart π X) q hmem,
          Nat.mem_primeFactors.2 ⟨hqp, hd.trans (Subgroup.card_subgroup_dvd_card _),
            Nat.card_pos.ne'⟩⟩
      · exact Or.inl hqp

theorem isHallSubgroup_sylowPiPart (π : Set ℕ) (X : Type*) [Group X] [Finite X]
    [Group.IsNilpotent X] : IsHallSubgroup π (sylowPiPart π X) where
  natCard := isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_sylowPiPart π X)
  index := isPiNumber_compl_index_sylowPiPart π X

theorem IsHallSubgroup.eq_sylowPiPart [Group.IsNilpotent X] {Y : Subgroup X}
    (hY : IsHallSubgroup π Y) : Y = sylowPiPart π X := by
  have hle : sylowPiPart π X ≤ Y := hY.le_of_isPiSubgroup (isPiSubgroup_sylowPiPart π X)
  refine (Subgroup.eq_of_le_of_card_ge hle (Nat.le_of_dvd Nat.card_pos ?_)).symm
  refine (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').1 fun p => ?_
  by_cases hp : p.Prime
  · by_cases hπ : p ∈ π
    · rw [factorization_natCard_sylowPiPart hp hπ]
      exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
        (Subgroup.card_subgroup_dvd_card _) p
    · have hnd : ¬ p ∣ Nat.card Y := fun hd =>
        hπ (isPiNumber_iff.1 hY.natCard p (Nat.mem_primeFactors.2 ⟨hp, hd, Nat.card_pos.ne'⟩))
      simp [Nat.factorization_eq_zero_of_not_dvd hnd]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem isHallSubgroup_iff_eq_sylowPiPart [Group.IsNilpotent X] {Y : Subgroup X} :
    IsHallSubgroup π Y ↔ Y = sylowPiPart π X :=
  ⟨IsHallSubgroup.eq_sylowPiPart, fun h => h ▸ isHallSubgroup_sylowPiPart π X⟩

theorem IsHallSubgroup.unique [Group.IsNilpotent X] {Y Z : Subgroup X}
    (hY : IsHallSubgroup π Y) (hZ : IsHallSubgroup π Z) : Y = Z :=
  hY.eq_sylowPiPart.trans hZ.eq_sylowPiPart.symm

theorem IsHallSubgroup.characteristic [Group.IsNilpotent X] {Y : Subgroup X}
    (hY : IsHallSubgroup π Y) : Y.Characteristic :=
  hY.eq_sylowPiPart ▸ sylowPiPart_characteristic π X

section Product

variable [Group.IsNilpotent X] (P : ∀ p : ↥(piPrimeFactors π X), Sylow (p : ℕ) X)

theorem subsingleton_sylow_of_isNilpotent (p : ℕ) (X : Type*) [Group X] [Finite X]
    [Group.IsNilpotent X] [Fact p.Prime] : Subsingleton (Sylow p X) :=
  have P : Sylow p X := Classical.arbitrary _
  have := Sylow.unique_of_normal P inferInstance
  Unique.instSubsingleton

theorem pairwise_commute_sylow_family :
    Pairwise fun i j : ↥(piPrimeFactors π X) =>
      ∀ x y : X, x ∈ (P i : Subgroup X) → y ∈ (P j : Subgroup X) → Commute x y := by
  intro i j hij
  have hi := prime_of_mem_piPrimeFactors i.2
  have hj := prime_of_mem_piPrimeFactors j.2
  have hfi : Fact (i : ℕ).Prime := ⟨hi⟩
  have hfj : Fact (j : ℕ).Prime := ⟨hj⟩
  exact Subgroup.commute_of_normal_of_disjoint _ _ (sylow_normal_of_isNilpotent (P i))
    (sylow_normal_of_isNilpotent (P j))
    ((P i).isPGroup'.disjoint_of_coprime (P j).isPGroup'
      ((Nat.coprime_primes hi hj).2 (Subtype.coe_ne_coe.2 hij)))

noncomputable def sylowPiHom : (∀ p : ↥(piPrimeFactors π X), (P p : Subgroup X)) →* X :=
  Subgroup.noncommPiCoprod (pairwise_commute_sylow_family P)

theorem range_sylowPiHom : (sylowPiHom P).range = ⨆ p, (P p : Subgroup X) :=
  Subgroup.noncommPiCoprod_range

theorem injective_sylowPiHom : Function.Injective (sylowPiHom P) := by
  have : ∀ p : ↥(piPrimeFactors π X), Fintype (P p : Subgroup X) := fun _ => Fintype.ofFinite _
  refine Subgroup.injective_noncommPiCoprod_of_iSupIndep
    (Subgroup.independent_of_coprime_order (pairwise_commute_sylow_family P) ?_)
  intro i j hij
  have hi := prime_of_mem_piPrimeFactors i.2
  have hj := prime_of_mem_piPrimeFactors j.2
  have hfi : Fact (i : ℕ).Prime := ⟨hi⟩
  have hfj : Fact (j : ℕ).Prime := ⟨hj⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    (P i).card_eq_multiplicity, (P j).card_eq_multiplicity]
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hi hj).2 (Subtype.coe_ne_coe.2 hij))

theorem iSup_sylow_eq_sylowPiPart :
    ⨆ p : ↥(piPrimeFactors π X), (P p : Subgroup X) = sylowPiPart π X := by
  refine le_antisymm (iSup_le fun i => sylow_le_sylowPiPart (prime_of_mem_piPrimeFactors i.2)
    (mem_piPrimeFactors.1 i.2).1 (P i)) (sylowPiPart_le fun p hp hπ Q => ?_)
  have : Fact p.Prime := ⟨hp⟩
  by_cases hd : p ∣ Nat.card X
  · have hmem : p ∈ piPrimeFactors π X :=
      mem_piPrimeFactors.2 ⟨hπ, Nat.mem_primeFactors.2 ⟨hp, hd, Nat.card_pos.ne'⟩⟩
    have := subsingleton_sylow_of_isNilpotent p X
    have heq : ((P ⟨p, hmem⟩ : Sylow p X) : Subgroup X) = (Q : Subgroup X) := by
      rw [Subsingleton.elim (P ⟨p, hmem⟩) Q]
    rw [← heq]
    exact le_iSup (fun i : ↥(piPrimeFactors π X) => (P i : Subgroup X)) ⟨p, hmem⟩
  · have h1 : (Q : Subgroup X) = ⊥ := by
      refine Subgroup.card_eq_one.1 ?_
      rw [Q.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hd, pow_zero]
    rw [h1]
    exact bot_le

noncomputable def sylowPiMulEquivSylowPiPart :
    (∀ p : ↥(piPrimeFactors π X), (P p : Subgroup X)) ≃* sylowPiPart π X :=
  (MonoidHom.ofInjective (injective_sylowPiHom P)).trans
    (MulEquiv.subgroupCongr ((range_sylowPiHom P).trans (iSup_sylow_eq_sylowPiPart P)))

end Product

theorem IsCentralSeries.isHallSubgroup_sylowPiPart {Z : ℕ → Subgroup X} {r : ℕ}
    (hZ : IsCentralSeries Z r) (π : Set ℕ) : IsHallSubgroup π (sylowPiPart π X) :=
  have : Group.IsNilpotent X := hZ.isNilpotent
  _root_.CFSG.FeitThompson.isHallSubgroup_sylowPiPart π X

theorem IsCentralSeries.eq_sylowPiPart {Z : ℕ → Subgroup X} {r : ℕ} (hZ : IsCentralSeries Z r)
    {Y : Subgroup X} (hY : IsHallSubgroup π Y) : Y = sylowPiPart π X :=
  have : Group.IsNilpotent X := hZ.isNilpotent
  hY.eq_sylowPiPart

end CFSG.FeitThompson

end
