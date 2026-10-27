module

public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.OddFrobeniusComplementCentralizesFitting
import CFSG.FeitThompson.Local.OddFrobeniusComplementCyclicSylows
import CFSG.FeitThompson.Foundations.FittingContainsCentralizerSolvable
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle

open Pointwise

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {L : Type*} [Group L] {p : ℕ}

theorem characteristic_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (K : Subgroup C) : K.Characteristic :=
  Subgroup.characteristic_iff_map_eq.2 fun φ =>
    eq_of_natCard_eq_of_isCyclic (Subgroup.card_map_of_injective (EquivLike.injective φ))

theorem isCyclic_pCore_of_isZGroup {X : Type*} [Group X] [Finite X] [IsZGroup X] (hp : p.Prime) :
    IsCyclic ↥(pCore p X) := by
  have := Fact.mk hp
  obtain ⟨S, hS⟩ := (isPGroup_pCore hp X).exists_le_sylow
  have : IsCyclic ↥(S : Subgroup X) := IsZGroup.isZGroup p hp S
  exact Subgroup.isCyclic_of_le hS

variable [Finite L]

theorem isCyclic_pCore_of_free_complement (hodd : Odd (Nat.card L)) {H E : Subgroup L} [H.Normal]
    (hH : H ≠ ⊥) [Group.IsSolvable ↥H]
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥) (hp : p.Prime) :
    IsCyclic ↥(pCore p ↥E) :=
  haveI := isZGroup_of_free_complement hodd hH hfree
  isCyclic_pCore_of_isZGroup hp

theorem isCyclic_pCoreIn_of_free_complement (hodd : Odd (Nat.card L)) {H E : Subgroup L} [H.Normal]
    (hH : H ≠ ⊥) [Group.IsSolvable ↥H]
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥) (hp : p.Prime) :
    IsCyclic ↥(pCoreIn p E) := by
  have := isCyclic_pCore_of_free_complement (E := E) hodd hH hfree hp
  rw [pCoreIn_eq]
  exact isCyclic_of_surjective
    (Subgroup.equivMapOfInjective (pCore p ↥E) E.subtype E.subtype_injective).toMonoidHom
    (MulEquiv.surjective _)

variable [Group.IsSolvable L]

theorem le_pCore_of_natCard_eq_prime (hodd : Odd (Nat.card L)) {H E : Subgroup L} [H.Normal]
    (hH : H ≠ ⊥) (hnil : Group.IsNilpotent ↥H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    (hp : p.Prime) {P : Subgroup ↥E} (hP : Nat.card ↥P = p) : P ≤ pCore p ↥E :=
  le_pCore_of_isPGroup_of_le_fittingRaw hp (IsPGroup.of_card (n := 1) (by rw [hP, pow_one]))
    (le_fittingRaw_of_le_centralizer_fittingRaw
      (le_centralizer_fittingRaw_of_natCard_eq_prime hodd hH hnil hfree hp hP))

theorem characteristic_subgroupOf_pCore_of_natCard_eq_prime (hodd : Odd (Nat.card L))
    {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) (hnil : Group.IsNilpotent ↥H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    (hp : p.Prime) (P : Subgroup ↥E) (_hP : Nat.card ↥P = p) :
    (P.subgroupOf (pCore p ↥E)).Characteristic := by
  have : Group.IsSolvable ↥H := by have := hnil; infer_instance
  have := isCyclic_pCore_of_free_complement (E := E) hodd hH hfree hp
  exact characteristic_of_isCyclic _

theorem normal_of_natCard_eq_prime (hodd : Odd (Nat.card L))
    {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) (hnil : Group.IsNilpotent ↥H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    (hp : p.Prime) {P : Subgroup ↥E} (hP : Nat.card ↥P = p) : P.Normal := by
  have := pCore_normal p ↥E
  have := characteristic_subgroupOf_pCore_of_natCard_eq_prime hodd hH hnil hfree hp P hP
  exact normal_of_characteristic_subgroupOf_of_normal
    (le_pCore_of_natCard_eq_prime hodd hH hnil hfree hp hP)

theorem eq_of_natCard_eq_prime (hodd : Odd (Nat.card L))
    {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) (hnil : Group.IsNilpotent ↥H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    (hp : p.Prime) {P₁ P₂ : Subgroup ↥E} (hP₁ : Nat.card ↥P₁ = p) (hP₂ : Nat.card ↥P₂ = p) :
    P₁ = P₂ := by
  have : Group.IsSolvable ↥H := by have := hnil; infer_instance
  have := isCyclic_pCore_of_free_complement (E := E) hodd hH hfree hp
  exact eq_of_le_of_natCard_eq_of_isCyclic (A := pCore p ↥E)
    (le_pCore_of_natCard_eq_prime hodd hH hnil hfree hp hP₁)
    (le_pCore_of_natCard_eq_prime hodd hH hnil hfree hp hP₂) (by rw [hP₁, hP₂])

theorem existsUnique_natCard_eq_prime (hodd : Odd (Nat.card L))
    {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) (hnil : Group.IsNilpotent ↥H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    (hp : p.Prime) (hdvd : p ∣ Nat.card ↥E) : ∃! P : Subgroup ↥E, Nat.card ↥P = p := by
  have := Fact.mk hp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) p hdvd
  have hz : Nat.card ↥(Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  exact ⟨Subgroup.zpowers x, hz, fun Q hQ => eq_of_natCard_eq_prime hodd hH hnil hfree hp hQ hz⟩

theorem le_pCoreIn_of_natCard_eq_prime (hodd : Odd (Nat.card L)) {H E : Subgroup L} [H.Normal]
    (hH : H ≠ ⊥) (hnil : Group.IsNilpotent ↥H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    (hp : p.Prime) {P : Subgroup L} (hPE : P ≤ E) (hP : Nat.card ↥P = p) : P ≤ pCoreIn p E := by
  have hcard : Nat.card ↥(P.subgroupOf E) = p := by rw [natCard_subgroupOf_of_le' hPE, hP]
  rw [pCoreIn_eq, ← Subgroup.map_subgroupOf_eq_of_le hPE]
  exact Subgroup.map_mono (le_pCore_of_natCard_eq_prime hodd hH hnil hfree hp hcard)

theorem characteristic_subgroupOf_pCoreIn_of_natCard_eq_prime (hodd : Odd (Nat.card L))
    {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) (hnil : Group.IsNilpotent ↥H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    (hp : p.Prime) (P : Subgroup L) (_hPE : P ≤ E) (_hP : Nat.card ↥P = p) :
    (P.subgroupOf (pCoreIn p E)).Characteristic := by
  have : Group.IsSolvable ↥H := by have := hnil; infer_instance
  have := isCyclic_pCoreIn_of_free_complement (E := E) hodd hH hfree hp
  exact characteristic_of_isCyclic _

theorem le_normalizer_of_natCard_eq_prime (hodd : Odd (Nat.card L))
    {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) (hnil : Group.IsNilpotent ↥H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    (hp : p.Prime) {P : Subgroup L} (hPE : P ≤ E) (hP : Nat.card ↥P = p) :
    E ≤ Subgroup.normalizer (P : Set L) := by
  have hcard : Nat.card ↥(P.subgroupOf E) = p := by rw [natCard_subgroupOf_of_le' hPE, hP]
  exact le_normalizer_of_normal_subgroupOf hPE
    (normal_of_natCard_eq_prime hodd hH hnil hfree hp hcard)

theorem characteristic_and_normal_of_frobenius_decomposition
    (hodd : Odd (Nat.card L)) {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) (_hE : E ≠ ⊥)
    (_hmul : (H : Set L) * (E : Set L) = Set.univ) (_hdisj : H ⊓ E = ⊥)
    (hnil : Group.IsNilpotent ↥H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥) :
    (∀ q : ℕ, q.Prime → ∀ P : Subgroup ↥E, Nat.card ↥P = q →
        P ≤ pCore q ↥E ∧ (P.subgroupOf (pCore q ↥E)).Characteristic ∧ P.Normal) ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥E → ∃! P : Subgroup ↥E, Nat.card ↥P = q :=
  ⟨fun _q hq P hP =>
      ⟨le_pCore_of_natCard_eq_prime hodd hH hnil hfree hq hP,
        characteristic_subgroupOf_pCore_of_natCard_eq_prime hodd hH hnil hfree hq P hP,
        normal_of_natCard_eq_prime hodd hH hnil hfree hq hP⟩,
    fun _q hq hdvd => existsUnique_natCard_eq_prime hodd hH hnil hfree hq hdvd⟩

theorem characteristic_and_normal_of_frobenius_decomposition_ambient
    (hodd : Odd (Nat.card L)) {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥)
    (_hE : E ≠ ⊥) (_hmul : (H : Set L) * (E : Set L) = Set.univ) (_hdisj : H ⊓ E = ⊥)
    (hnil : Group.IsNilpotent ↥H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥) :
    (∀ q : ℕ, q.Prime → ∀ P : Subgroup L, P ≤ E → Nat.card ↥P = q →
        P ≤ pCoreIn q E ∧ (P.subgroupOf (pCoreIn q E)).Characteristic ∧
          E ≤ Subgroup.normalizer (P : Set L)) ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥E →
        ∃! P : Subgroup L, P ≤ E ∧ Nat.card ↥P = q := by
  refine ⟨fun _q hq P hPE hP =>
    ⟨le_pCoreIn_of_natCard_eq_prime hodd hH hnil hfree hq hPE hP,
      characteristic_subgroupOf_pCoreIn_of_natCard_eq_prime hodd hH hnil hfree hq P hPE hP,
      le_normalizer_of_natCard_eq_prime hodd hH hnil hfree hq hPE hP⟩, fun q hq hdvd => ?_⟩
  obtain ⟨P, hP, huniq⟩ := existsUnique_natCard_eq_prime hodd hH hnil hfree hq hdvd
  refine ⟨P.map E.subtype, ⟨Subgroup.map_subtype_le P, ?_⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hP]
  · rintro Q ⟨hQE, hQ⟩
    have hcard : Nat.card ↥(Q.subgroupOf E) = q := by rw [natCard_subgroupOf_of_le' hQE, hQ]
    rw [← Subgroup.map_subgroupOf_eq_of_le hQE, huniq _ hcard]

end CFSG.FeitThompson

end
