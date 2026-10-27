module

public import CFSG.GroupTheory.GL52.SylowTools
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.NormNum.Prime

public noncomputable section

namespace CFSG.GroupTheory.GL52

open scoped Pointwise

section Count

variable {K : Type*} [Group K] [Finite K]

theorem ncard_orderOf_eq_prime_of_sylow {p : ℕ} [Fact p.Prime]
    (hP : ∀ P : Sylow p K, Nat.card P = p) :
    {x : K | orderOf x = p}.ncard = Nat.card (Sylow p K) * (p - 1) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (Sylow p K) := Fintype.ofFinite _
  have hpp : p.Prime := Fact.out
  have hgen : ∀ (P : Sylow p K) (x : K), x ∈ P → x ≠ 1 →
      (P : Subgroup K) = Subgroup.zpowers x := by
    intro P x hx hx1
    have hle : Subgroup.zpowers x ≤ P := (Subgroup.zpowers_le).2 hx
    have hdvd : orderOf x ∣ p := by
      rw [← hP P, ← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _
    have hord : orderOf x = p := by
      rcases (Nat.dvd_prime hpp).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [Nat.card_zpowers, hord, hP P]
  set t : Sylow p K → Finset K := fun P => (Finset.univ.filter (· ∈ P)).erase 1
  have hset : {x : K | orderOf x = p}.toFinset = (Finset.univ : Finset (Sylow p K)).biUnion t := by
    ext x
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_biUnion, Finset.mem_univ,
      true_and, t, Finset.mem_erase, Finset.mem_filter]
    constructor
    · intro hx
      have hZ : IsPGroup p (Subgroup.zpowers x) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
      obtain ⟨P, hP'⟩ := hZ.exists_le_sylow
      refine ⟨P, fun h1 => ?_, hP' (Subgroup.mem_zpowers x)⟩
      rw [h1, orderOf_one] at hx
      exact hpp.one_lt.ne hx
    · rintro ⟨P, hx1, hxP⟩
      have hdvd : orderOf x ∣ p := by
        rw [← hP P, ← Subgroup.orderOf_mk x hxP]
        exact orderOf_dvd_natCard _
      rcases (Nat.dvd_prime hpp).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hx1
      · exact h1
  have hdisj : ((Finset.univ : Finset (Sylow p K)) : Set (Sylow p K)).PairwiseDisjoint t := by
    intro P _ P' _ hPP'
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [t, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    apply hPP'
    apply Sylow.ext
    rw [hgen P x hx.2 hx.1, hgen P' x hx'.2 hx'.1]
  rw [Set.ncard_eq_toFinset_card', hset, Finset.card_biUnion hdisj]
  have hcard : ∀ P : Sylow p K, (t P).card = p - 1 := by
    intro P
    simp only [t]
    rw [Finset.card_erase_of_mem (by simp)]
    have h1 : (Finset.univ.filter (· ∈ P)).card = Nat.card P := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp; rfl))
    rw [h1, hP P]
  rw [Finset.sum_congr rfl (fun P _ => hcard P), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.card_eq_fintype_card]

end Count

theorem card_normalizer_sylow_subgroup_dvd {H : Subgroup G52} {p n : ℕ} [Fact p.Prime]
    (hp : ∀ P : Sylow p G52, Nat.card P = p)
    (hN : ∀ P : Sylow p G52, Nat.card (Subgroup.normalizer (P : Set G52)) = n)
    (Q : Sylow p H) (hQ : Nat.card Q = p) :
    Nat.card (Subgroup.normalizer (Q : Set H)) ∣ n := by
  have hinj : Function.Injective H.subtype := Subtype.coe_injective
  have hQ' : Nat.card ((Q : Subgroup H).map H.subtype) = p := by
    rw [Subgroup.card_map_of_injective hinj, hQ]
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_card hQ' hp
  have hle := Subgroup.le_normalizer_map (H := (Q : Subgroup H)) H.subtype
  rw [← hP] at hle
  have h := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective hinj] at h
  have hP' : ((P : Set G52)) = ((P : Subgroup G52) : Set G52) := rfl
  have hQs : ((Q : Set H)) = ((Q : Subgroup H) : Set H) := rfl
  rw [← hN P, hP', hQs]
  exact h

theorem card_sylow_mul_card_normalizer {H : Subgroup G52} {p : ℕ} [Fact p.Prime] (Q : Sylow p H) :
    Nat.card (Sylow p H) * Nat.card (Subgroup.normalizer (Q : Set H)) =
      Nat.card H ∧ Nat.card (Sylow p H) % p = 1 % p := by
  refine ⟨?_, (card_sylow_modEq_one p H : _)⟩
  rw [Sylow.card_eq_index_normalizer Q]
  exact Subgroup.index_mul_card _

end CFSG.GroupTheory.GL52
