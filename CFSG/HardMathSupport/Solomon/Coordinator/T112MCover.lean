module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112MSylow
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MLocal
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MOrder
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open Equiv

section Cover

variable {K : Type*} [Group K] [Finite K]

theorem t112m_sylow_cover {Q : Type*} [Group Q] (hperf : commutator K = ⊤)
    (hZ : Nat.card (Subgroup.center K) = 3) (e : (K ⧸ Subgroup.center K) ≃* Q) {m : ℕ}
    (hQ : Nat.card Q = 3 ^ 2 * m) (hm : ¬ 3 ∣ m) (R : Sylow 3 K) :
    Nat.card ↥(R : Subgroup K) = 27 ∧
      (∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup K), r ^ 3 = 1 := by
  refine t112m_sylow_of_perfect hperf le_rfl hZ (t112m_factorization_eq_three (m := m) ?_ hm) R
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K),
    Nat.card_congr e.toEquiv, hQ, hZ]
  ring

theorem t112m_sylow_hatSix (h : IsHatSix K) (R : Sylow 3 K) :
    Nat.card ↥(R : Subgroup K) = 27 ∧
      (∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup K), r ^ 3 = 1 := by
  obtain ⟨hc, hZ, ⟨e⟩⟩ := h
  refine t112m_sylow_cover hc hZ e (m := 40) ?_ (by norm_num) R
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem t112m_sylow_hatSeven (h : IsHatSeven K) (R : Sylow 3 K) :
    Nat.card ↥(R : Subgroup K) = 27 ∧
      (∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup K), r ^ 3 = 1 := by
  obtain ⟨hc, hZ, ⟨e⟩⟩ := h
  refine t112m_sylow_cover hc hZ e (m := 280) ?_ (by norm_num) R
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

end Cover

section Alt

theorem t112m_alt_data {α : Type*} [Fintype α] [DecidableEq α] {S : Finset (Perm α)}
    (hS1 : 1 ∈ S) (hSm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hS2 : ∀ a ∈ S, a * a = 1)
    (hSA : ∀ a ∈ S, Perm.sign a = 1) {t : Perm α} (htS : t ∈ S) (ht1 : t ≠ 1)
    {c : Perm α} (hcA : Perm.sign c = 1) (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1)
    (hcS : ∀ a ∈ S, c * a * c⁻¹ ∈ S) (hcS' : ∀ a ∈ S, c⁻¹ * a * c ∈ S) :
    ∃ (V : Subgroup ↥(alternatingGroup α)) (x : ↥(alternatingGroup α)),
      V ≠ ⊥ ∧ (∀ a ∈ V, a ^ 2 = 1) ∧ x ≠ 1 ∧ x ^ 3 = 1 ∧
        x ∈ Subgroup.normalizer (V : Set ↥(alternatingGroup α)) := by
  let V₀ : Subgroup (Perm α) :=
    { carrier := ↑S
      mul_mem' := fun {a b} ha hb => hSm a ha b hb
      one_mem' := hS1
      inv_mem' := fun {a} ha => by
        have h := hS2 a ha
        rw [mul_eq_one_iff_eq_inv] at h
        rw [Finset.mem_coe, ← h]
        exact ha }
  have hV₀ : ∀ a, a ∈ V₀ ↔ a ∈ S := fun a => Iff.rfl
  set V : Subgroup ↥(alternatingGroup α) := V₀.subgroupOf (alternatingGroup α) with hV
  have hmemV : ∀ a : ↥(alternatingGroup α), a ∈ V ↔ (a : Perm α) ∈ S := fun a => by
    rw [hV, Subgroup.mem_subgroupOf, hV₀]
  refine ⟨V, ⟨c, Perm.mem_alternatingGroup.2 hcA⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro hVb
    have h1 : (⟨t, Perm.mem_alternatingGroup.2 (hSA t htS)⟩ : ↥(alternatingGroup α)) ∈ V :=
      (hmemV _).2 htS
    rw [hVb, Subgroup.mem_bot] at h1
    exact ht1 (congrArg Subtype.val h1)
  · intro a ha
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two]
    exact hS2 _ ((hmemV a).1 ha)
  · intro h
    exact hc1 (congrArg Subtype.val h)
  · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hc3)
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hmemV, hmemV]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · exact hcS _
    · intro h'
      have := hcS' _ h'
      simpa [mul_assoc] using this

theorem t112m_alt6_data :
    ∃ (V : Subgroup ↥(alternatingGroup (Fin 6))) (x : ↥(alternatingGroup (Fin 6))),
      V ≠ ⊥ ∧ (∀ a ∈ V, a ^ 2 = 1) ∧ x ≠ 1 ∧ x ^ 3 = 1 ∧
        x ∈ Subgroup.normalizer (V : Set ↥(alternatingGroup (Fin 6))) := by
  refine t112m_alt_data (S := {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2})
    (t := swap 0 1 * swap 2 3) (c := swap 0 1 * swap 1 2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]) <;>
    (try and_intros) <;> decide

theorem t112m_alt7_data :
    ∃ (V : Subgroup ↥(alternatingGroup (Fin 7))) (x : ↥(alternatingGroup (Fin 7))),
      V ≠ ⊥ ∧ (∀ a ∈ V, a ^ 2 = 1) ∧ x ≠ 1 ∧ x ^ 3 = 1 ∧
        x ∈ Subgroup.normalizer (V : Set ↥(alternatingGroup (Fin 7))) := by
  refine t112m_alt_data (S := {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2})
    (t := swap 0 1 * swap 2 3) (c := swap 0 1 * swap 1 2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]) <;>
    (try and_intros) <;> decide

theorem t112m_data_of_mulEquiv {Q A : Type*} [Group Q] [Group A] (e : Q ≃* A)
    (h : ∃ (V : Subgroup A) (x : A), V ≠ ⊥ ∧ (∀ a ∈ V, a ^ 2 = 1) ∧ x ≠ 1 ∧ x ^ 3 = 1 ∧
      x ∈ Subgroup.normalizer (V : Set A)) :
    ∃ (V : Subgroup Q) (x : Q), V ≠ ⊥ ∧ (∀ a ∈ V, a ^ 2 = 1) ∧ x ≠ 1 ∧ x ^ 3 = 1 ∧
      x ∈ Subgroup.normalizer (V : Set Q) := by
  obtain ⟨V, x, hV1, hV2, hx1, hx3, hxV⟩ := h
  refine ⟨V.comap e.toMonoidHom, e.symm x, ?_, ?_, ?_, ?_, ?_⟩
  · intro hb
    apply hV1
    rw [eq_bot_iff]
    intro a ha
    have h1 : e.symm a ∈ V.comap e.toMonoidHom := by
      show e (e.symm a) ∈ V
      rw [MulEquiv.apply_symm_apply]
      exact ha
    rw [hb, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply e a, h1, map_one]
  · intro a ha
    have h1 := hV2 _ ha
    apply e.injective
    rw [map_pow, map_one]
    exact h1
  · intro h1
    apply hx1
    rw [← MulEquiv.apply_symm_apply e x, h1, map_one]
  · apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]
    exact hx3
  · rw [Subgroup.mem_normalizer_iff]
    intro a
    show e a ∈ V ↔ e (e.symm x * a * (e.symm x)⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_normalizer_iff.1 hxV (e a)

end Alt

section TwoLocal

variable {K : Type} [Group K] [Finite K]

theorem t112m_twoLocal_hatSix (h : IsHatSix K) : 2 ≤ GLATwoLocalRank 3 K := by
  have hexp := fun R => (t112m_sylow_hatSix h R).2.2
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  obtain ⟨V, x, hV1, hV2, hx1, hx3, hxV⟩ := t112m_data_of_mulEquiv e t112m_alt6_data
  exact t112m_cover_twoLocal hZ hexp hV1 hV2 hx1 hx3 hxV

theorem t112m_twoLocal_hatSeven (h : IsHatSeven K) : 2 ≤ GLATwoLocalRank 3 K := by
  have hexp := fun R => (t112m_sylow_hatSeven h R).2.2
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  obtain ⟨V, x, hV1, hV2, hx1, hx3, hxV⟩ := t112m_data_of_mulEquiv e t112m_alt7_data
  exact t112m_cover_twoLocal hZ hexp hV1 hV2 hx1 hx3 hxV

end TwoLocal

end CFSG.HardMathSupport.Solomon.Coordinator
