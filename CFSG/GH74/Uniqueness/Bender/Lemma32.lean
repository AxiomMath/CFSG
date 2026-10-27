module

public import CFSG.GH74.Uniqueness.Bender.Models

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup
open scoped commutatorElement

variable {K : Type*} [Group K]

structure Lemma32 (n i e : ℕ) (P : Subgroup K) (t : K) : Prop where
  index_eq : (borel P).index = (2 ^ n) ^ i + 1
  bruhat : ∀ g, g ∉ borel P → ∃ p ∈ P, ∃ m ∈ borel P, g = p * t * m
  involutions_iff : ∀ g : K, (g ∈ borel P ∧ orderOf g = 2) ↔ (g ∈ rootCenter P ∧ g ≠ 1)
  elemAbelian_center : CFSG.Open.IsElemAbelian 2 (rootCenter P)
  card_center : Nat.card (rootCenter P) = 2 ^ n
  closure_involutions : Subgroup.closure {g : K | g ∈ borel P ∧ orderOf g = 2} = rootCenter P
  involutions_conj : ∀ z ∈ rootCenter P, z ≠ 1 → ∀ z' ∈ rootCenter P, z' ≠ 1 →
    ∃ d ∈ cartan P t, z' = d⁻¹ * z * d
  card_sylow : Nat.card P = (2 ^ n) ^ i
  sup_cartan : P ⊔ cartan P t = borel P
  inf_cartan : P ⊓ cartan P t = ⊥
  isCyclic_cartan : IsCyclic (cartan P t)
  card_cartan : Nat.card (cartan P t) = (2 ^ n - 1) * e
  isCyclic_commutator : IsCyclic ↥⁅cartan P t, Subgroup.zpowers t⁆
  card_commutator : Nat.card ↥⁅cartan P t, Subgroup.zpowers t⁆ = 2 ^ n - 1
  inverted : ∀ x ∈ ⁅cartan P t, Subgroup.zpowers t⁆, t * x * t = x⁻¹
  regular : ∀ z ∈ rootCenter P, z ≠ 1 → ∀ z' ∈ rootCenter P, z' ≠ 1 →
    ∃! d, d ∈ ⁅cartan P t, Subgroup.zpowers t⁆ ∧ z' = d⁻¹ * z * d
  isCyclic_fix : IsCyclic (fixCartan P t)
  card_fix : Nat.card (fixCartan P t) = e
  cartan_eq_commutator : i ≠ 3 → cartan P t = ⁅cartan P t, Subgroup.zpowers t⁆
  involutions_class : ∀ t' : K, t' * t' = 1 → t' ∉ borel P → ∃ m ∈ borel P, t' = m⁻¹ * t * m
  sup_zpowers : ∀ x, x ∉ borel P → P ⊔ Subgroup.zpowers x = ⊤

theorem BenderType.lemma_3_2
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) (Q : Sylow 2 K)
    {t : K} (ht : t * t = 1) (htQ : t ∉ borel (Q : Subgroup K)) :
    Lemma32 n i e (Q : Subgroup K) t := by
  have hc := h.benderCore Q ht htQ
  have : IsSimpleGroup K := h.isSimple
  refine
    { index_eq := hc.index_eq
      bruhat := fun g hg => hc.bruhat hg
      involutions_iff := fun g => hc.involution_iff
      elemAbelian_center := ?_
      card_center := hc.card_center
      closure_involutions := hc.closure_involutions
      involutions_conj := fun z hz hz1 z' hz' hz1' => hc.exists_cartan_conj hz hz1 hz' hz1'
      card_sylow := hc.card_eq
      sup_cartan := hc.sup_eq
      inf_cartan := hc.inf_eq
      isCyclic_cartan := hc.isCyclic
      card_cartan := hc.card_cartan
      isCyclic_commutator := hc.isCyclic_commutator
      card_commutator := hc.card_commutator_cartan
      inverted := fun x hx => (hc.mem_commutator_cartan_iff.mp hx).2
      regular := fun z hz hz1 z' hz' hz1' => hc.existsUnique_commutator_conj hz hz1 hz' hz1'
      isCyclic_fix := hc.isCyclic_fixCartan
      card_fix := hc.card_fixCartan
      cartan_eq_commutator := ?_
      involutions_class := fun t' ht' htM' => hc.exists_conj_eq ht' htM'
      sup_zpowers := fun x hx => hc.sup_zpowers_eq_top hx }
  · refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      have hx' := mem_rootCenter_iff.mp x.2
      have hy' := mem_rootCenter_iff.mp y.2
      exact (hx'.2 y hy'.1).symm
    · rw [sq]
      exact hc.center_sq x hx
  · intro hi3
    apply hc.cartan_eq_commutator
    rcases h.cases' with ⟨-, he, -⟩ | ⟨-, he, -⟩ | ⟨hi, -, -⟩
    · exact he
    · exact he
    · exact absurd hi hi3

theorem unitary_e_gt_one (n : ℕ) (hn : 2 ≤ n) : 1 < (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hg : Nat.gcd 3 (2 ^ n + 1) = 1 ∨ Nat.gcd 3 (2 ^ n + 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left _ _)
  rcases hg with hg | hg
  · rw [hg, Nat.div_one]; omega
  · rw [hg]
    have h3 : 3 ∣ 2 ^ n + 1 := hg ▸ Nat.gcd_dvd_right _ _
    omega

theorem BenderType.lemma_3_2_h_unitary_ne_top
    [Finite K] {n e : ℕ} (h : BenderType K n 3 e)
    (Q : Sylow 2 K) {t : K} (ht : t * t = 1) (htQ : t ∉ borel (Q : Subgroup K)) {z : K}
    (hz : z ∈ rootCenter (Q : Subgroup K)) (hz1 : z ≠ 1) :
    Subgroup.closure ({z, t} : Set K) ⊔ ⁅cartan (Q : Subgroup K) t, Subgroup.zpowers t⁆ ≠ ⊤ := by
  have hc := h.benderCore Q ht htQ
  have : IsSimpleGroup K := h.isSimple
  have hnc : ¬ ∀ x y : K, x * y = y * x := h.isSimpleBenderGroup.not_commutative
  have he : 1 < e := by
    rcases h.cases' with ⟨hi, -, -⟩ | ⟨hi, -, -⟩ | ⟨-, he, hn⟩
    · omega
    · omega
    · rw [he]; exact unitary_e_gt_one n hn
  exact hc.lemma32h_ne_top he hnc hz hz1

theorem BenderType.lemma_3_2_h_linear
    [Finite K] {n e : ℕ} (h : BenderType K n 1 e)
    (Q : Sylow 2 K) {t : K} (ht : t * t = 1) (htQ : t ∉ borel (Q : Subgroup K)) {z : K}
    (hz : z ∈ rootCenter (Q : Subgroup K)) (hz1 : z ≠ 1) :
    Subgroup.closure ({z, t} : Set K) ⊔ ⁅cartan (Q : Subgroup K) t, Subgroup.zpowers t⁆ = ⊤ := by
  have hc := h.benderCore Q ht htQ
  have : IsSimpleGroup K := h.isSimple
  exact hc.lemma32h_top_of_card_eq rfl hz hz1

theorem BenderType.lemma_3_4_b
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) (Q : Sylow 2 K)
    {t : K} (ht : t * t = 1) (htQ : t ∉ borel (Q : Subgroup K)) {u : K}
    (hu : u ∈ borel (Q : Subgroup K) ∧ orderOf u = 2) :
    centralizer ({u} : Set K) ≤ borel (Q : Subgroup K) ∧
      centralizer ({u} : Set K) = (Q : Subgroup K) ⊔ fixCartan (Q : Subgroup K) t ∧
      Nat.card ↥(centralizer ({u} : Set K)) = (2 ^ n) ^ i * e ∧
      Nat.card ↥(borel (Q : Subgroup K)) = (2 ^ n - 1) * Nat.card ↥(centralizer ({u} : Set K)) ∧
      Group.IsSolvable ↥(centralizer ({u} : Set K)) ∧ IsCyclic (fixCartan (Q : Subgroup K) t) ∧
      Nat.card (fixCartan (Q : Subgroup K) t) = e := by
  have hc := h.benderCore Q ht htQ
  obtain ⟨hz, hz1⟩ := hc.involution_iff.mp hu
  have hcen := hc.centralizer_eq hz hz1
  have hle : centralizer ({u} : Set K) ≤ borel (Q : Subgroup K) := by
    rw [hcen]
    exact sup_le (le_borel _) ((fixCartan_le_cartan _ t).trans (cartan_le_borel _ t))
  have hcard := hc.card_centralizer hz hz1
  refine ⟨hle, hcen, hcard, ?_, ?_, hc.isCyclic_fixCartan, hc.card_fixCartan⟩
  · rw [hc.card_borel, hcard]
    ring
  · have := hc.isSolvable_borel
    exact isSolvable_of_le_isSolvable hle

theorem BenderType.lemma_3_4_a
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) {u v : K}
    (hu : u * u = 1) (hu1 : u ≠ 1) (hv : v * v = 1) (hv1 : v ≠ 1) : IsConj u v := by
  obtain ⟨t, hc⟩ := h.exists_benderCore (default : Sylow 2 K)
  exact hc.isConj_of_involutions hu hu1 hv hv1

theorem BenderType.lemma_3_5_d
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) (Q : Sylow 2 K)
    {t : K} (ht : t * t = 1) (htQ : t ∉ borel (Q : Subgroup K)) :
    centralizer (rootCenter (Q : Subgroup K) : Set K) =
      (Q : Subgroup K) ⊔ fixCartan (Q : Subgroup K) t :=
  (h.benderCore Q ht htQ).centralizer_rootCenter_eq

theorem BenderType.le_borel_of_sylow_le
    [Finite K] {n i e : ℕ} (h : BenderType K n i e)
    (Q : Sylow 2 K) {J : Subgroup K} (hQJ : (Q : Subgroup K) ≤ J) (hJ : J ≠ ⊤) :
    J ≤ borel (Q : Subgroup K) := by
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have : IsSimpleGroup K := h.isSimple
  exact hc.le_borel_of_le hQJ hJ

end CFSG.GH74.Uniqueness.Bender
