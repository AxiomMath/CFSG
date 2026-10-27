module

public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import CFSG.FeitThompson.Local.NilpotentHallCharacteristic
import CFSG.FeitThompson.Foundations.SolvablePerfectTrivial
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Local.CyclicSylowDerivedNormal
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {X : Type*} [Group X] {q : ℕ}

theorem IsHallSubgroup.factorization_natCard_eq [Finite X] {π : Set ℕ} {H : Subgroup X}
    (hH : IsHallSubgroup π H) (hq : q ∈ π) :
    (Nat.card H).factorization q = (Nat.card X).factorization q := by
  by_cases hqp : q.Prime
  · have hnd : ¬ q ∣ H.index := fun hd =>
      isPiNumber_iff.1 hH.index q
        (Nat.mem_primeFactors.2 ⟨hqp, hd, Subgroup.index_ne_zero_of_finite⟩) hq
    have h := Subgroup.card_mul_index H
    rw [← h, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
    simp [Nat.factorization_eq_zero_of_not_dvd hnd]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hqp]

theorem isHallSubgroup_of_factorization_eq [Finite X] {π : Set ℕ} {H : Subgroup X}
    (hcard : IsPiNumber π (Nat.card H))
    (hfull : ∀ q ∈ π, q.Prime → (Nat.card H).factorization q = (Nat.card X).factorization q) :
    IsHallSubgroup π H where
  natCard := hcard
  index := isPiNumber_iff.2 fun q hq hq' => by
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hdvd : q ∣ H.index := Nat.dvd_of_mem_primeFactors hq
    have h := Subgroup.card_mul_index H
    have h0 := Nat.factorization_mul (a := Nat.card H) (b := H.index) Nat.card_pos.ne'
      Subgroup.index_ne_zero_of_finite
    rw [h] at h0
    have h1 : 1 ≤ H.index.factorization q :=
      hqp.factorization_pos_of_dvd Subgroup.index_ne_zero_of_finite hdvd
    have h2 := congrArg (fun f => f q) h0
    simp only [Finsupp.coe_add, Pi.add_apply] at h2
    rw [hfull q hq' hqp] at h2
    omega

theorem IsHallSubgroup.coprime_natCard [Finite X] {π ρ : Set ℕ} {H K : Subgroup X}
    (hH : IsHallSubgroup π H) (hK : IsHallSubgroup ρ K) (hd : ∀ q ∈ π, q ∉ ρ) :
    (Nat.card H).Coprime (Nat.card K) :=
  (Nat.disjoint_primeFactors Nat.card_pos.ne' Nat.card_pos.ne').1
    (Finset.disjoint_left.2 fun q hq hq' =>
      hd q (isPiNumber_iff.1 hH.natCard q hq) (isPiNumber_iff.1 hK.natCard q hq'))

theorem IsHallSubgroup.inf_eq_bot [Finite X] {π ρ : Set ℕ} {H K : Subgroup X}
    (hH : IsHallSubgroup π H) (hK : IsHallSubgroup ρ K) (hd : ∀ q ∈ π, q ∉ ρ) : H ⊓ K = ⊥ :=
  disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard (hH.coprime_natCard hK hd))

theorem IsHallSubgroup.natCard_mul_natCard [Finite X] {π ρ : Set ℕ} {H K : Subgroup X}
    (hH : IsHallSubgroup π H) (hK : IsHallSubgroup ρ K) (hd : ∀ q ∈ π, q ∉ ρ)
    (hcov : ∀ q ∈ (Nat.card X).primeFactors, q ∈ π ∨ q ∈ ρ) :
    Nat.card H * Nat.card K = Nat.card X := by
  refine Nat.eq_of_factorization_eq (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')
    Nat.card_pos.ne' fun q => ?_
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
  simp only [Finsupp.coe_add, Pi.add_apply]
  by_cases hqp : q.Prime
  · by_cases hqd : q ∣ Nat.card X
    · rcases hcov q (Nat.mem_primeFactors.2 ⟨hqp, hqd, Nat.card_pos.ne'⟩) with hq | hq
      · have h2 : ¬ q ∣ Nat.card K := fun hd' =>
          hd q hq (isPiNumber_iff.1 hK.natCard q
            (Nat.mem_primeFactors.2 ⟨hqp, hd', Nat.card_pos.ne'⟩))
        rw [hH.factorization_natCard_eq hq, Nat.factorization_eq_zero_of_not_dvd h2, add_zero]
      · have h2 : ¬ q ∣ Nat.card H := fun hd' =>
          hd q (isPiNumber_iff.1 hH.natCard q
            (Nat.mem_primeFactors.2 ⟨hqp, hd', Nat.card_pos.ne'⟩)) hq
        rw [hK.factorization_natCard_eq hq, Nat.factorization_eq_zero_of_not_dvd h2, zero_add]
    · have h1 : ¬ q ∣ Nat.card H := fun hd' => hqd (hd'.trans (Subgroup.card_subgroup_dvd_card _))
      have h2 : ¬ q ∣ Nat.card K := fun hd' => hqd (hd'.trans (Subgroup.card_subgroup_dvd_card _))
      simp [Nat.factorization_eq_zero_of_not_dvd h1, Nat.factorization_eq_zero_of_not_dvd h2,
        Nat.factorization_eq_zero_of_not_dvd hqd]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hqp]

theorem IsHallSubgroup.isComplement' [Finite X] {π ρ : Set ℕ} {H K : Subgroup X}
    (hH : IsHallSubgroup π H) (hK : IsHallSubgroup ρ K) (hd : ∀ q ∈ π, q ∉ ρ)
    (hcov : ∀ q ∈ (Nat.card X).primeFactors, q ∈ π ∨ q ∈ ρ) : H.IsComplement' K :=
  Subgroup.isComplement'_of_coprime (hH.natCard_mul_natCard hK hd hcov)
    (hH.coprime_natCard hK hd)

theorem IsHallSubgroup.map_subtype {π ρ : Set ℕ} {H : Subgroup X} {S : Subgroup H}
    (hH : IsHallSubgroup ρ H) (hS : IsHallSubgroup π S) (hπρ : π ⊆ ρ) :
    IsHallSubgroup π (S.map H.subtype) where
  natCard := by rw [Subgroup.card_subtype]; exact hS.natCard
  index := by
    rw [Subgroup.index_map_subtype]
    exact hS.index.mul (hH.index.mono fun q hq hq' => hq (hπρ hq'))

theorem IsHallSubgroup.sup [Finite X] {π ρ : Set ℕ} {H K : Subgroup X} [K.Normal]
    (hH : IsHallSubgroup π H) (hK : IsHallSubgroup ρ K) (hd : ∀ q ∈ π, q ∉ ρ) :
    IsHallSubgroup (π ∪ ρ) (H ⊔ K) := by
  have hcard : Nat.card (H ⊔ K : Subgroup X) = Nat.card H * Nat.card K := by
    have h := natCard_mul_mul_natCard_inf H K
    rw [← Subgroup.mul_normal H K, hH.inf_eq_bot hK hd] at h
    simpa using h
  refine isHallSubgroup_of_factorization_eq ?_ ?_
  · rw [hcard]
    exact (hH.natCard.mono Set.subset_union_left).mul (hK.natCard.mono Set.subset_union_right)
  · intro q hq hqp
    rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp only [Finsupp.coe_add, Pi.add_apply]
    rcases hq with hq | hq
    · have h2 : ¬ q ∣ Nat.card K := fun hd' =>
        hd q hq (isPiNumber_iff.1 hK.natCard q
          (Nat.mem_primeFactors.2 ⟨hqp, hd', Nat.card_pos.ne'⟩))
      rw [hH.factorization_natCard_eq hq, Nat.factorization_eq_zero_of_not_dvd h2, add_zero]
    · have h2 : ¬ q ∣ Nat.card H := fun hd' =>
        hd q (isPiNumber_iff.1 hH.natCard q
          (Nat.mem_primeFactors.2 ⟨hqp, hd', Nat.card_pos.ne'⟩)) hq
      rw [hK.factorization_natCard_eq hq, Nat.factorization_eq_zero_of_not_dvd h2, zero_add]

theorem eq_one_of_isPiNumber_of_isPiNumber {π ρ : Set ℕ} {n : ℕ} (hn : n ≠ 0)
    (h1 : IsPiNumber π n) (h2 : IsPiNumber ρ n) (hd : ∀ q ∈ π, q ∉ ρ) : n = 1 := by
  have hempty : n.primeFactors = ∅ := by
    ext q
    simp only [Finset.notMem_empty, iff_false]
    exact fun hq => hd q (isPiNumber_iff.1 h1 q hq) (isPiNumber_iff.1 h2 q hq)
  rcases Nat.primeFactors_eq_empty.1 hempty with h | h
  · exact absurd h hn
  · exact h

theorem isCyclic_of_mulEquiv {A B : Type*} [Group A] [Group B] [IsCyclic A] (e : A ≃* B) :
    IsCyclic B := isCyclic_of_surjective e e.surjective

theorem isNilpotent_of_isMulCommutative (A : Type*) [Group A] [IsMulCommutative A] :
    Group.IsNilpotent A :=
  ⟨1, by
    rw [Subgroup.upperCentralSeries_one]
    exact (Subgroup.eq_top_iff' _).2 fun x => Subgroup.mem_center_iff.2 fun y => mul_comm' y x⟩

theorem isZGroup_of_isHallSubgroup [Finite X] {π : Set ℕ} {H : Subgroup X}
    (hH : IsHallSubgroup π H)
    (hcyc : ∀ q ∈ π, ∀ Q : Sylow q X, IsCyclic (Q : Subgroup X)) : IsZGroup H := by
  rw [isZGroup_iff]
  intro q hq S
  have : Fact q.Prime := ⟨hq⟩
  by_cases hqπ : q ∈ π
  · have hcard : Nat.card ((S : Subgroup H).map H.subtype)
        = q ^ (Nat.card X).factorization q := by
      rw [Subgroup.card_subtype, S.card_eq_multiplicity, hH.factorization_natCard_eq hqπ]
    have hc := hcyc q hqπ (Sylow.ofCard _ hcard)
    rw [Sylow.coe_ofCard] at hc
    exact isCyclic_of_mulEquiv
      (((S : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).symm)
  · have hnd : ¬ q ∣ Nat.card H := fun hd =>
      hqπ (isPiNumber_iff.1 hH.natCard q (Nat.mem_primeFactors.2 ⟨hq, hd, Nat.card_pos.ne'⟩))
    have h1 : Nat.card (S : Subgroup H) = 1 := by
      rw [S.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero]
    have : Subsingleton (S : Subgroup H) := (Nat.card_eq_one_iff_unique.1 h1).1
    exact isCyclic_of_subsingleton

theorem natCard_commutator_dvd (H : Subgroup X) :
    Nat.card (commutator H) ∣ Nat.card (commutator X) := by
  rw [← Subgroup.card_subtype H (commutator H), Subgroup.map_subtype_commutator]
  exact Subgroup.card_dvd_of_le (Subgroup.commutator_mono le_top le_top)

theorem exists_mem_orderOf_eq_of_dvd [Finite X] {H : Subgroup X} (hq : q.Prime)
    (hd : q ∣ Nat.card H) : ∃ x ∈ H, orderOf x = q := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fintype H := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := H) q
    (by simpa [Nat.card_eq_fintype_card] using hd)
  exact ⟨x, x.2, by simpa [Subgroup.orderOf_coe] using hx⟩

theorem forall_isCyclic_sylow_iff_exists [Finite X] (hq : q.Prime) :
    (∀ Q : Sylow q X, IsCyclic (Q : Subgroup X)) ↔
      ∃ Q : Sylow q X, IsCyclic (Q : Subgroup X) := by
  have : Fact q.Prime := ⟨hq⟩
  refine ⟨fun h => ⟨Classical.arbitrary _, h _⟩, ?_⟩
  rintro ⟨P, hP⟩ Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
  have hcoe : (Q : Subgroup X) = (P : Subgroup X).map (MulAut.conj g) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    ext x
    simp [Subgroup.mem_smul_pointwise_iff_exists, MulAut.smul_def]
  rw [hcoe]
  exact isCyclic_of_surjective _
    (((P : Subgroup X).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).surjective)

def piTwoPrimes (X : Type*) [Group X] : Set ℕ :=
  {q | q ∈ (Nat.card X).primeFactors ∧ ∀ Q : Sylow q X, ¬ IsCyclic (Q : Subgroup X)}

def piOnePrimes (X : Type*) [Group X] : Set ℕ :=
  {q | q ∈ (Nat.card X).primeFactors ∧ (∀ Q : Sylow q X, IsCyclic (Q : Subgroup X)) ∧
    ¬ q ∣ Nat.card (commutator X)}

def piThreePrimes (X : Type*) [Group X] : Set ℕ :=
  {q | q ∈ (Nat.card X).primeFactors ∧ (∀ Q : Sylow q X, IsCyclic (Q : Subgroup X)) ∧
    q ∣ Nat.card (commutator X)}

theorem mem_piTwoPrimes_iff : q ∈ piTwoPrimes X ↔
    q ∈ (Nat.card X).primeFactors ∧ ∀ Q : Sylow q X, ¬ IsCyclic (Q : Subgroup X) := (Iff.rfl)

theorem mem_piOnePrimes_iff : q ∈ piOnePrimes X ↔ q ∈ (Nat.card X).primeFactors ∧
    (∀ Q : Sylow q X, IsCyclic (Q : Subgroup X)) ∧ ¬ q ∣ Nat.card (commutator X) := (Iff.rfl)

theorem mem_piThreePrimes_iff : q ∈ piThreePrimes X ↔ q ∈ (Nat.card X).primeFactors ∧
    (∀ Q : Sylow q X, IsCyclic (Q : Subgroup X)) ∧ q ∣ Nat.card (commutator X) := (Iff.rfl)

theorem mem_piTwoPrimes_iff_exists [Finite X] : q ∈ piTwoPrimes X ↔
    q ∈ (Nat.card X).primeFactors ∧ ∃ Q : Sylow q X, ¬ IsCyclic (Q : Subgroup X) := by
  refine and_congr_right fun hq => ?_
  rw [← not_iff_not, not_forall_not, not_exists_not]
  exact (forall_isCyclic_sylow_iff_exists (Nat.prime_of_mem_primeFactors hq)).symm

theorem prime_of_mem_piOnePrimes (hq : q ∈ piOnePrimes X) : q.Prime :=
  Nat.prime_of_mem_primeFactors hq.1

theorem prime_of_mem_piTwoPrimes (hq : q ∈ piTwoPrimes X) : q.Prime :=
  Nat.prime_of_mem_primeFactors hq.1

theorem prime_of_mem_piThreePrimes (hq : q ∈ piThreePrimes X) : q.Prime :=
  Nat.prime_of_mem_primeFactors hq.1

theorem piOnePrimes_disjoint_piTwoPrimes : ∀ p ∈ piOnePrimes X, p ∉ piTwoPrimes X :=
  fun _ h1 h2 => h2.2 (Classical.arbitrary _) (h1.2.1 _)

theorem piOnePrimes_disjoint_piThreePrimes : ∀ p ∈ piOnePrimes X, p ∉ piThreePrimes X :=
  fun _ h1 h3 => h1.2.2 h3.2.2

theorem piTwoPrimes_disjoint_piThreePrimes : ∀ p ∈ piTwoPrimes X, p ∉ piThreePrimes X :=
  fun _ h2 h3 => h2.2 (Classical.arbitrary _) (h3.2.1 _)

theorem mem_piOnePrimes_or_piTwoPrimes_or_piThreePrimes [Finite X]
    (hq : q ∈ (Nat.card X).primeFactors) :
    q ∈ piOnePrimes X ∨ q ∈ piTwoPrimes X ∨ q ∈ piThreePrimes X := by
  by_cases hc : ∀ Q : Sylow q X, IsCyclic (Q : Subgroup X)
  · by_cases hd : q ∣ Nat.card (commutator X)
    · exact Or.inr (Or.inr ⟨hq, hc, hd⟩)
    · exact Or.inl ⟨hq, hc, hd⟩
  · rw [not_forall] at hc
    obtain ⟨Q, hQ⟩ := hc
    exact Or.inr (Or.inl (mem_piTwoPrimes_iff_exists.2 ⟨hq, ⟨Q, hQ⟩⟩))

theorem isPiNumber_natCard_commutator [Finite X] :
    IsPiNumber (piTwoPrimes X ∪ piThreePrimes X) (Nat.card (commutator X)) :=
  isPiNumber_iff.2 fun q hq => by
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqd : q ∣ Nat.card (commutator X) := Nat.dvd_of_mem_primeFactors hq
    have hqX : q ∈ (Nat.card X).primeFactors :=
      Nat.mem_primeFactors.2 ⟨hqp, hqd.trans (Subgroup.card_subgroup_dvd_card _), Nat.card_pos.ne'⟩
    rcases mem_piOnePrimes_or_piTwoPrimes_or_piThreePrimes hqX with h | h | h
    · exact absurd hqd (mem_piOnePrimes_iff.1 h).2.2
    · exact Or.inl h
    · exact Or.inr h

theorem isPiNumber_natCard_commutator_of_isHallSubgroup [Finite X] {H : Subgroup X}
    (hH : IsHallSubgroup (piTwoPrimes X ∪ piOnePrimes X) H) :
    IsPiNumber (piTwoPrimes X) (Nat.card (commutator H)) := by
  refine isPiNumber_iff.2 fun q hq => ?_
  have hd : q ∣ Nat.card (commutator H) := Nat.dvd_of_mem_primeFactors hq
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have h1 : q ∈ piTwoPrimes X ∪ piOnePrimes X :=
    isPiNumber_iff.1 hH.natCard q (Nat.mem_primeFactors.2
      ⟨hqp, hd.trans (Subgroup.card_subgroup_dvd_card _), Nat.card_pos.ne'⟩)
  have h2 : q ∈ piTwoPrimes X ∪ piThreePrimes X :=
    isPiNumber_iff.1 isPiNumber_natCard_commutator q (Nat.mem_primeFactors.2
      ⟨hqp, hd.trans (natCard_commutator_dvd H), Nat.card_pos.ne'⟩)
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact absurd h2 (piOnePrimes_disjoint_piTwoPrimes q h1)
    · exact absurd h2 (piOnePrimes_disjoint_piThreePrimes q h1)

theorem isMulCommutative_of_isHallSubgroup_piOnePrimes [Finite X] {H : Subgroup X}
    (hH : IsHallSubgroup (piOnePrimes X) H) : IsMulCommutative H := by
  have hbot : commutator H = ⊥ := by
    refine Subgroup.card_eq_one.1 (eq_one_of_isPiNumber_of_isPiNumber (π := piOnePrimes X)
      (ρ := piTwoPrimes X ∪ piThreePrimes X) Nat.card_pos.ne' ?_ ?_ ?_)
    · exact hH.natCard.of_dvd (Subgroup.card_subgroup_dvd_card _) Nat.card_pos.ne'
    · exact isPiNumber_natCard_commutator.of_dvd (natCard_commutator_dvd H) Nat.card_pos.ne'
    · rintro q hq (h2 | h3)
      · exact piOnePrimes_disjoint_piTwoPrimes q hq h2
      · exact piOnePrimes_disjoint_piThreePrimes q hq h3
  exact (commutator_eq_bot_iff H).1 hbot

theorem isCyclic_of_isHallSubgroup_piOnePrimes [Finite X] {H : Subgroup X}
    (hH : IsHallSubgroup (piOnePrimes X) H) : IsCyclic H := by
  have : IsMulCommutative H := isMulCommutative_of_isHallSubgroup_piOnePrimes hH
  have : IsZGroup H :=
    isZGroup_of_isHallSubgroup hH fun _ hq Q => (mem_piOnePrimes_iff.1 hq).2.1 Q
  have : Group.IsNilpotent H := isNilpotent_of_isMulCommutative _
  infer_instance

section PiThree

variable [Finite X]

theorem sylow_normal_of_mem_piThreePrimes (hnil : Group.IsNilpotent (commutator X))
    (hq : q ∈ piThreePrimes X) (Q : Sylow q X) : (Q : Subgroup X).Normal := by
  have : Fact q.Prime := ⟨prime_of_mem_piThreePrimes hq⟩
  have := (mem_piThreePrimes_iff.1 hq).2.1 Q
  exact cyclicSylow_normal hnil Q (mem_piThreePrimes_iff.1 hq).2.2

theorem sylow_le_commutator_of_mem_piThreePrimes (hq : q ∈ piThreePrimes X) (Q : Sylow q X) :
    (Q : Subgroup X) ≤ commutator X := by
  have : Fact q.Prime := ⟨prime_of_mem_piThreePrimes hq⟩
  have := (mem_piThreePrimes_iff.1 hq).2.1 Q
  exact cyclicSylow_le_commutator Q (mem_piThreePrimes_iff.1 hq).2.2

theorem sylow_inf_center_eq_bot_of_mem_piThreePrimes (hnil : Group.IsNilpotent (commutator X))
    (hq : q ∈ piThreePrimes X) (Q : Sylow q X) : (Q : Subgroup X) ⊓ center X = ⊥ := by
  have : Fact q.Prime := ⟨prime_of_mem_piThreePrimes hq⟩
  have := (mem_piThreePrimes_iff.1 hq).2.1 Q
  exact cyclicSylow_inf_center_eq_bot hnil Q (mem_piThreePrimes_iff.1 hq).2.2

theorem inf_center_eq_bot_of_isPiSubgroup_piThreePrimes
    (hnil : Group.IsNilpotent (commutator X)) {H : Subgroup X}
    (hH : IsPiSubgroup (piThreePrimes X) H) : H ⊓ center X = ⊥ := by
  by_contra hne
  have hcard : Nat.card (H ⊓ center X : Subgroup X) ≠ 1 := fun h =>
    hne (Subgroup.card_eq_one.1 h)
  obtain ⟨r, hrp, hrd⟩ := (Nat.card (H ⊓ center X : Subgroup X)).exists_prime_and_dvd hcard
  obtain ⟨y, hyH, hyord⟩ := exists_mem_orderOf_eq_of_dvd hrp hrd
  obtain ⟨-, hyZ⟩ := Subgroup.mem_inf.1 hyH
  have hr3 : r ∈ piThreePrimes X :=
    isPiSubgroup_iff.1 hH r (Nat.mem_primeFactors.2 ⟨hrp,
      hrd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
  have : Fact r.Prime := ⟨hrp⟩
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (p := r) (P := zpowers y)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyord, pow_one]))
  have hmem : y ∈ (Q : Subgroup X) ⊓ center X :=
    Subgroup.mem_inf.2 ⟨hQ (mem_zpowers y), hyZ⟩
  rw [sylow_inf_center_eq_bot_of_mem_piThreePrimes hnil hr3 Q] at hmem
  have hy1 : y = 1 := hmem
  rw [hy1, orderOf_one] at hyord
  exact hrp.ne_one hyord.symm

theorem isPiSubgroup_sylowPiPart_piThreePrimes (hnil : Group.IsNilpotent (commutator X)) :
    IsPiSubgroup (piThreePrimes X) (sylowPiPart (piThreePrimes X) X) := by
  refine (isPiSubgroup_piCore (piThreePrimes X) X).of_le (sylowPiPart_le fun p hp hπ P => ?_)
  have : Fact p.Prime := ⟨hp⟩
  exact le_piCore (sylow_normal_of_mem_piThreePrimes hnil hπ P)
    (((isPiSubgroup_singleton_iff hp _).2 P.isPGroup').mono (Set.singleton_subset_iff.2 hπ))

theorem isHallSubgroup_sylowPiPart_piThreePrimes (hnil : Group.IsNilpotent (commutator X)) :
    IsHallSubgroup (piThreePrimes X) (sylowPiPart (piThreePrimes X) X) where
  natCard := isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_sylowPiPart_piThreePrimes hnil)
  index := isPiNumber_compl_index_sylowPiPart _ _

theorem sylowPiPart_piThreePrimes_le_commutator :
    sylowPiPart (piThreePrimes X) X ≤ commutator X :=
  sylowPiPart_le fun _ _ hπ P => sylow_le_commutator_of_mem_piThreePrimes hπ P

theorem isCyclic_sylowPiPart_piThreePrimes (hnil : Group.IsNilpotent (commutator X)) :
    IsCyclic (sylowPiPart (piThreePrimes X) X) := by
  have : Group.IsNilpotent (sylowPiPart (piThreePrimes X) X) :=
    have := hnil
    (Group.isNilpotent_congr
      (Subgroup.subgroupOfEquivOfLe (sylowPiPart_piThreePrimes_le_commutator (X := X)))).1
      inferInstance
  have : IsZGroup (sylowPiPart (piThreePrimes X) X) :=
    isZGroup_of_isHallSubgroup (isHallSubgroup_sylowPiPart_piThreePrimes hnil)
      fun _ hq Q => (mem_piThreePrimes_iff.1 hq).2.1 Q
  infer_instance

theorem sylowPiPart_piThreePrimes_inf_center_eq_bot
    (hnil : Group.IsNilpotent (commutator X)) :
    sylowPiPart (piThreePrimes X) X ⊓ center X = ⊥ :=
  inf_center_eq_bot_of_isPiSubgroup_piThreePrimes hnil
    (isPiSubgroup_sylowPiPart_piThreePrimes hnil)

end PiThree

structure IsThreePrimeDecomposition (X₁ X₂ X₃ : Subgroup X) : Prop where
  hallOne : IsHallSubgroup (piOnePrimes X) X₁
  hallTwo : IsHallSubgroup (piTwoPrimes X) X₂
  hallThree : IsHallSubgroup (piThreePrimes X) X₃
  normalThree : X₃.Normal
  isComplementThree : X₃.IsComplement' (X₂ ⊔ X₁)
  normalTwo : (X₂.subgroupOf (X₂ ⊔ X₁)).Normal
  isComplementTwo : (X₂.subgroupOf (X₂ ⊔ X₁)).IsComplement' (X₁.subgroupOf (X₂ ⊔ X₁))
  isCyclicOne : IsCyclic X₁
  isCyclicThree : IsCyclic X₃
  threeLeCommutator : X₃ ≤ commutator X
  infCenterThree : X₃ ⊓ center X = ⊥
  normalTwoSupThree : (X₂ ⊔ X₃).Normal

theorem exists_isThreePrimeDecomposition (X : Type*) [Group X] [Finite X] [Group.IsSolvable X]
    (hnil : Group.IsNilpotent (commutator X)) :
    ∃ X₁ X₂ X₃ : Subgroup X, IsThreePrimeDecomposition X₁ X₂ X₃ := by
  classical
  set X₃ := sylowPiPart (piThreePrimes X) X with hX₃def
  have hX₃ : IsHallSubgroup (piThreePrimes X) X₃ :=
    isHallSubgroup_sylowPiPart_piThreePrimes hnil
  have hn₃ : X₃.Normal := sylowPiPart_normal _ _
  obtain ⟨H, hH⟩ := exists_isHallSubgroup (X := X) (piTwoPrimes X ∪ piOnePrimes X)
  have hd₃ : ∀ r ∈ piThreePrimes X, r ∉ piTwoPrimes X ∪ piOnePrimes X := by
    rintro r hr (h | h)
    · exact piTwoPrimes_disjoint_piThreePrimes r h hr
    · exact piOnePrimes_disjoint_piThreePrimes r h hr
  have hcov₃ : ∀ r ∈ (Nat.card X).primeFactors,
      r ∈ piThreePrimes X ∨ r ∈ piTwoPrimes X ∪ piOnePrimes X := by
    intro r hr
    rcases mem_piOnePrimes_or_piTwoPrimes_or_piThreePrimes hr with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  obtain ⟨S₂, hS₂⟩ := exists_isHallSubgroup (X := H) (piTwoPrimes X)
  obtain ⟨S₁, hS₁⟩ := exists_isHallSubgroup (X := H) (piOnePrimes X)
  have hn₂' : S₂.Normal :=
    Subgroup.Normal.of_commutator_le _
      (hS₂.normal_le (isPiNumber_natCard_commutator_of_isHallSubgroup hH))
  have hd₂ : ∀ r ∈ piTwoPrimes X, r ∉ piOnePrimes X :=
    fun r hr h => piOnePrimes_disjoint_piTwoPrimes r h hr
  have hcov₂ : ∀ r ∈ (Nat.card H).primeFactors, r ∈ piTwoPrimes X ∨ r ∈ piOnePrimes X :=
    fun r hr => isPiNumber_iff.1 hH.natCard r hr
  have hcompl₂ : S₂.IsComplement' S₁ := hS₂.isComplement' hS₁ hd₂ hcov₂
  set X₂ := S₂.map H.subtype with hX₂def
  set X₁ := S₁.map H.subtype with hX₁def
  have hX₂ : IsHallSubgroup (piTwoPrimes X) X₂ := hH.map_subtype hS₂ Set.subset_union_left
  have hX₁ : IsHallSubgroup (piOnePrimes X) X₁ := hH.map_subtype hS₁ Set.subset_union_right
  have hsup : X₂ ⊔ X₁ = H := by
    have h2 := congrArg (Subgroup.map H.subtype) hcompl₂.sup_eq_top
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    exact h2
  have hX₂₃ : IsHallSubgroup (piTwoPrimes X ∪ piThreePrimes X) (X₂ ⊔ X₃) :=
    hX₂.sup hX₃ piTwoPrimes_disjoint_piThreePrimes
  have hn₂₃ : (X₂ ⊔ X₃).Normal :=
    Subgroup.Normal.of_commutator_le _ (hX₂₃.normal_le isPiNumber_natCard_commutator)
  refine ⟨X₁, X₂, X₃, hX₁, hX₂, hX₃, hn₃, ?_, ?_, ?_,
    isCyclic_of_isHallSubgroup_piOnePrimes hX₁, isCyclic_sylowPiPart_piThreePrimes hnil,
    sylowPiPart_piThreePrimes_le_commutator, sylowPiPart_piThreePrimes_inf_center_eq_bot hnil,
    hn₂₃⟩
  · rw [hsup]
    exact hX₃.isComplement' hH hd₃ hcov₃
  · rw [hsup, hX₂def, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact hn₂'
  · rw [hsup, hX₂def, hX₁def, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact hcompl₂

theorem IsThreePrimeDecomposition.ne_bot_one [Group.IsSolvable X] [Nontrivial X]
    {X₁ X₂ X₃ : Subgroup X} (h : IsThreePrimeDecomposition X₁ X₂ X₃) (h2 : X₂ = ⊥) : X₁ ≠ ⊥ := by
  intro h1
  have hsup : X₂ ⊔ X₁ = ⊥ := by rw [h1, h2, sup_idem]
  have htop : X₃ = ⊤ := by
    have hc := h.isComplementThree
    rw [hsup] at hc
    simpa using hc.sup_eq_top
  have hcomm : commutator X = ⊤ := le_antisymm le_top (htop ▸ h.threeLeCommutator)
  exact absurd (subsingleton_of_isSolvable_of_commutator_eq_top X hcomm)
    (not_subsingleton_iff_nontrivial.2 inferInstance)

end

end CFSG.FeitThompson

