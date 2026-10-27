module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NVBasic
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

variable {G : Type} [Group G] {t z : G}

private lemma conj_eq_self_iff_comm {g y : G} : g * y * g⁻¹ = y ↔ g * y = y * g := by
  constructor
  · intro h
    calc g * y = (g * y * g⁻¹) * g := by group
      _ = y * g := by rw [h]
  · intro h
    rw [h]
    group

theorem card_le_two_mul_card_inf_centralizer_t [Finite G] (ht : t ^ 2 = 1) (hz : z ^ 2 = 1)
    (hc : t * z = z * t) (hzt : ¬ IsConj t z) (htz : IsConj t (t * z)) {P : Subgroup G}
    (hP : P ≤ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G)) :
    Nat.card P ≤ 2 * Nat.card ↥(P ⊓ centralizer ({t} : Set G)) := by
  classical
  let H : Subgroup P := (P ⊓ centralizer ({t} : Set G)).subgroupOf P
  let F : P → Bool := fun p => decide ((p : G) * t * (p : G)⁻¹ = t)
  have hcase : ∀ r : P, (r : G) * t * (r : G)⁻¹ = t ∨ (r : G) * t * (r : G)⁻¹ = t * z :=
    fun r => conj_t_of_mem_normalizer_V ht hz hc hzt htz (hP r.2)
  have hFcompat : ∀ p q : P, QuotientGroup.leftRel H p q → F p = F q := by
    intro p q hpq
    have hpq' : p⁻¹ * q ∈ H := QuotientGroup.leftRel_apply.mp hpq
    have hmem : ((p⁻¹ * q : P) : G) ∈ centralizer ({t} : Set G) := by
      have h := Subgroup.mem_subgroupOf.mp
        (show p⁻¹ * q ∈ (P ⊓ centralizer ({t} : Set G)).subgroupOf P from hpq')
      exact h.2
    have hcomm : ((p : G)⁻¹ * (q : G)) * t = t * ((p : G)⁻¹ * (q : G)) := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hmem
      simpa using h
    have hconj : (q : G) * t * (q : G)⁻¹ = (p : G) * t * (p : G)⁻¹ := by
      have hc' : ((p : G)⁻¹ * (q : G)) * t * ((p : G)⁻¹ * (q : G))⁻¹ = t :=
        conj_eq_self_iff_comm.mpr hcomm
      calc (q : G) * t * (q : G)⁻¹
          = ((p : G) * ((p : G)⁻¹ * (q : G))) * t * ((p : G) * ((p : G)⁻¹ * (q : G)))⁻¹ := by
            group
        _ = (p : G) * (((p : G)⁻¹ * (q : G)) * t * ((p : G)⁻¹ * (q : G))⁻¹) * (p : G)⁻¹ := by
            group
        _ = (p : G) * t * (p : G)⁻¹ := by rw [hc']
    simp only [F]
    rw [hconj]
  let φ : P ⧸ H → Bool := Quotient.lift F hFcompat
  have hφinj : Function.Injective φ := by
    intro x y
    refine Quotient.inductionOn₂' x y ?_
    intro p q hxy
    have hFeq : F p = F q := by simpa [φ] using hxy
    have hAB : (p : G) * t * (p : G)⁻¹ = (q : G) * t * (q : G)⁻¹ := by
      rcases hcase p with hp | hp <;> rcases hcase q with hq | hq
      · rw [hp, hq]
      · have hqeq : (q : G) * t * (q : G)⁻¹ = t := by
          have htrue : F q = true := by rw [← hFeq]; simp [F, hp]
          exact of_decide_eq_true (by simpa [F] using htrue)
        rw [hp, hqeq]
      · have hpeq : (p : G) * t * (p : G)⁻¹ = t := by
          have htrue : F p = true := by rw [hFeq]; simp [F, hq]
          exact of_decide_eq_true (by simpa [F] using htrue)
        rw [hpeq, hq]
      · rw [hp, hq]
    have hconj : ((p : G)⁻¹ * (q : G)) * t * ((p : G)⁻¹ * (q : G))⁻¹ = t := by
      calc ((p : G)⁻¹ * (q : G)) * t * ((p : G)⁻¹ * (q : G))⁻¹
          = (p : G)⁻¹ * ((q : G) * t * (q : G)⁻¹) * (p : G) := by group
        _ = (p : G)⁻¹ * ((p : G) * t * (p : G)⁻¹) * (p : G) := by rw [← hAB]
        _ = t := by group
    have hcomm : ((p : G)⁻¹ * (q : G)) * t = t * ((p : G)⁻¹ * (q : G)) :=
      conj_eq_self_iff_comm.mp hconj
    have hmemH : p⁻¹ * q ∈ H := by
      change p⁻¹ * q ∈ (P ⊓ centralizer ({t} : Set G)).subgroupOf P
      rw [Subgroup.mem_subgroupOf]
      refine ⟨(p⁻¹ * q : P).2, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    exact Quotient.sound' (QuotientGroup.leftRel_apply.mpr hmemH)
  have hHcard : Nat.card H = Nat.card ↥(P ⊓ centralizer ({t} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : P ⊓ centralizer ({t} : Set G) ≤ P)).toEquiv
  have hidx : H.index ≤ 2 := by
    have hle := Nat.card_le_card_of_injective φ hφinj
    change Nat.card (P ⧸ H) ≤ 2
    refine hle.trans ?_
    rw [Nat.card_eq_fintype_card]
    decide
  calc Nat.card P = H.index * Nat.card H := (Subgroup.index_mul_card H).symm
    _ ≤ 2 * Nat.card H := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_right hidx (Nat.card H)
    _ = 2 * Nat.card ↥(P ⊓ centralizer ({t} : Set G)) := by rw [hHcard]


end CFSG.EvenSporadicStandard.HNRecog.Harada
