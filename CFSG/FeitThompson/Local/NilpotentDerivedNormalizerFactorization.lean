module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic

open Pointwise Subgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] {p : ℕ}

theorem eq_top_of_forall_sylow_le {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (h : ∀ q : ℕ, q.Prime → ∀ Q : Sylow q G, (Q : Subgroup G) ≤ K) : K = ⊤ := by
  refine Subgroup.eq_top_of_card_eq _
    (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card _) ?_)
  refine (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').1 ?_
  refine (Finsupp.le_iff _ _).2 fun q hq => ?_
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqp⟩
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  refine (hqp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 ?_
  exact Q.card_eq_multiplicity ▸ Subgroup.card_dvd_of_le (h q hqp Q)

theorem isPiSubgroup_compl_of_isPGroup [Finite X] {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    {N : Subgroup X} (hN : IsPGroup q N) : IsPiSubgroup {r : ℕ | r.Prime ∧ r ≠ p} N := by
  have h : IsPiSubgroup ({q} : Set ℕ) N := (isPiSubgroup_singleton_iff hq N).2 hN
  refine isPiSubgroup_iff.2 fun r hr => ?_
  have hrq : r = q := isPiSubgroup_iff.1 h r hr
  exact ⟨hrq ▸ hq, hrq ▸ hqp⟩

theorem pCore_sup_pComplCore_eq_top (hp : p.Prime) (G : Type*) [Group G] [Finite G]
    [Group.IsNilpotent G] : pCore p G ⊔ pComplCore p G = ⊤ := by
  refine eq_top_of_forall_sylow_le fun q hq Q => ?_
  have : Fact q.Prime := ⟨hq⟩
  have hQn : (Q : Subgroup G).Normal := sylow_normal_of_isNilpotent Q
  by_cases hqp : q = p
  · subst hqp
    exact le_trans (le_pCore hp hQn Q.isPGroup') le_sup_left
  · refine le_trans ?_ le_sup_right
    rw [pComplCore_eq_piCore]
    exact le_piCore hQn (isPiSubgroup_compl_of_isPGroup hq hqp Q.isPGroup')

theorem natCard_eq_pow_factorization_of_le [Finite X] (hp : p.Prime) {P K : Subgroup X}
    (hPK : P ≤ K) (hP : Nat.card P = p ^ (Nat.card X).factorization p) :
    Nat.card P = p ^ (Nat.card K).factorization p := by
  have hK : (Nat.card K).factorization p = (Nat.card X).factorization p :=
    le_antisymm
      ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
        ((Nat.ordProj_dvd _ _).trans (Subgroup.card_subgroup_dvd_card K)))
      ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
        (hP ▸ Subgroup.card_dvd_of_le hPK))
  rw [hK, hP]

def derivedPCore (p : ℕ) (X : Type*) [Group X] [Finite X] : Subgroup X :=
  (pCore p (commutator X)).map (commutator X).subtype

def derivedPComplCore (p : ℕ) (X : Type*) [Group X] [Finite X] : Subgroup X :=
  (pComplCore p (commutator X)).map (commutator X).subtype

theorem derivedPCore_eq_map [Finite X] :
    derivedPCore p X = (pCore p (commutator X)).map (commutator X).subtype := (rfl)

theorem derivedPComplCore_eq_map [Finite X] :
    derivedPComplCore p X = (pComplCore p (commutator X)).map (commutator X).subtype := (rfl)

theorem mem_derivedPComplCore_iff [Finite X] {x : X} :
    x ∈ derivedPComplCore p X ↔
      ∃ h : x ∈ commutator X, (⟨x, h⟩ : commutator X) ∈ pComplCore p (commutator X) := by
  rw [derivedPComplCore_eq_map, Subgroup.mem_map]
  exact ⟨fun ⟨y, hy, hxy⟩ => ⟨hxy ▸ y.2, by simpa [← hxy] using hy⟩,
    fun ⟨h, hx⟩ => ⟨⟨x, h⟩, hx, rfl⟩⟩

instance derivedPComplCore_normal (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (derivedPComplCore p X).Normal := by
  rw [derivedPComplCore_eq_map]; exact ConjAct.normal_of_characteristic_of_normal

instance derivedPCore_normal (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (derivedPCore p X).Normal := by
  rw [derivedPCore_eq_map]; exact ConjAct.normal_of_characteristic_of_normal

theorem derivedPCore_le_commutator [Finite X] : derivedPCore p X ≤ commutator X := by
  rw [derivedPCore_eq_map]
  exact (Subgroup.map_le_range _ _).trans_eq (Subgroup.range_subtype _)

theorem derivedPComplCore_le_commutator [Finite X] : derivedPComplCore p X ≤ commutator X := by
  rw [derivedPComplCore_eq_map]
  exact (Subgroup.map_le_range _ _).trans_eq (Subgroup.range_subtype _)

theorem isPGroup_derivedPCore [Finite X] (hp : p.Prime) : IsPGroup p (derivedPCore p X) := by
  rw [derivedPCore_eq_map]
  exact (isPGroup_pCore hp _).map _

theorem not_dvd_natCard_derivedPComplCore [Finite X] (hp : p.Prime) :
    ¬ p ∣ Nat.card (derivedPComplCore p X) := by
  rw [derivedPComplCore_eq_map, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact not_dvd_natCard_pComplCore hp _

theorem coprime_natCard_derivedPComplCore [Finite X] (hp : p.Prime) :
    (Nat.card (derivedPComplCore p X)).Coprime p :=
  ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_natCard_derivedPComplCore hp)).symm

theorem derivedPCore_sup_derivedPComplCore [Finite X] (hp : p.Prime)
    (hX : Group.IsNilpotent (commutator X)) :
    derivedPCore p X ⊔ derivedPComplCore p X = commutator X := by
  have : Group.IsNilpotent (commutator X) := hX
  rw [derivedPCore_eq_map, derivedPComplCore_eq_map, ← Subgroup.map_sup,
    pCore_sup_pComplCore_eq_top hp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem derivedPCore_le_of_natCard_eq [Finite X] (hp : p.Prime) {P : Subgroup X}
    (hP : Nat.card P = p ^ (Nat.card X).factorization p) : derivedPCore p X ≤ P := by
  have : Fact p.Prime := ⟨hp⟩
  have h := (isPGroup_derivedPCore (X := X) hp).le_sylow_of_normal (Sylow.ofCard P hP)
  rwa [Sylow.coe_ofCard] at h

theorem derivedPComplCore_sup_normalizer_eq_top [Finite X] (hp : p.Prime)
    (hX : Group.IsNilpotent (commutator X)) {P : Subgroup X}
    (hP : Nat.card P = p ^ (Nat.card X).factorization p) :
    derivedPComplCore p X ⊔ normalizer (P : Set X) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hKnormal : (commutator X ⊔ P).Normal := Normal.of_commutator_le X le_sup_left
  have hfrat : commutator X ⊔ P ⊔ normalizer (P : Set X) = ⊤ :=
    sup_normalizer_eq_top_of_normal le_sup_right
      (natCard_eq_pow_factorization_of_le hp le_sup_right hP)
  refine top_le_iff.1 (hfrat.ge.trans (sup_le (sup_le ?_ ?_) le_sup_right))
  ·
    rw [← derivedPCore_sup_derivedPComplCore hp hX]
    exact sup_le ((derivedPCore_le_of_natCard_eq hp hP).trans (le_normalizer.trans le_sup_right))
      le_sup_left
  · exact le_normalizer.trans le_sup_right

theorem coe_derivedPComplCore_mul_coe_normalizer_eq_univ [Finite X] (hp : p.Prime)
    (hX : Group.IsNilpotent (commutator X)) {P : Subgroup X}
    (hP : Nat.card P = p ^ (Nat.card X).factorization p) :
    (derivedPComplCore p X : Set X) * (normalizer (P : Set X) : Set X) = Set.univ := by
  rw [← Subgroup.normal_mul, derivedPComplCore_sup_normalizer_eq_top hp hX hP, Subgroup.coe_top]

theorem exists_mem_derivedPComplCore_mul_mem_normalizer [Finite X] (hp : p.Prime)
    (hX : Group.IsNilpotent (commutator X)) {P : Subgroup X}
    (hP : Nat.card P = p ^ (Nat.card X).factorization p) (x : X) :
    ∃ c ∈ derivedPComplCore p X, ∃ n ∈ normalizer (P : Set X), x = c * n := by
  have hx : x ∈ (derivedPComplCore p X : Set X) * (normalizer (P : Set X) : Set X) := by
    rw [coe_derivedPComplCore_mul_coe_normalizer_eq_univ hp hX hP]; trivial
  obtain ⟨c, hc, n, hn, hcn⟩ := hx
  exact ⟨c, hc, n, hn, hcn.symm⟩

theorem derivedPComplCore_normal_and_not_dvd_natCard_and_sup_normalizer_eq_top [Finite X]
    [Fact p.Prime] (hX : Group.IsNilpotent (commutator X)) (P : Sylow p X) :
    (derivedPComplCore p X).Normal ∧ ¬ p ∣ Nat.card (derivedPComplCore p X) ∧
      derivedPComplCore p X ⊔ normalizer ((P : Subgroup X) : Set X) = ⊤ :=
  ⟨derivedPComplCore_normal p X, not_dvd_natCard_derivedPComplCore Fact.out,
    derivedPComplCore_sup_normalizer_eq_top Fact.out hX P.card_eq_multiplicity⟩

end

end CFSG.FeitThompson
