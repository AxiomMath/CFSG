module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviModules
public import CFSG.LinearAlgebra.DesarguesianPlanes.SteinbergRecognition
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviCentralizers

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup Matrix
open scoped commutatorElement MatrixGroups

@[expose] def a2Swap (i : Fin 3) : Fin 3 := if i = 0 then 1 else if i = 1 then 0 else i

@[expose] def a2Act : Bool → Fin 3 × Fin 3 × Fin 3 × Fin 3 → Fin 3 × Fin 3 × Fin 3 × Fin 3
  | false, x => (Fin.rev x.2.1, Fin.rev x.1, Fin.rev x.2.2.2, Fin.rev x.2.2.1)
  | true, x => (a2Swap x.1, a2Swap x.2.1, a2Swap x.2.2.1, a2Swap x.2.2.2)

@[expose] def a2ActList : List Bool → Fin 3 × Fin 3 × Fin 3 × Fin 3 → Fin 3 × Fin 3 × Fin 3 × Fin 3
  | [], x => x
  | b :: l, x => a2Act b (a2ActList l x)

@[expose] def a2Words : List (List Bool) :=
  [[], [false], [true], [false, true], [true, false], [false, true, false],
    [true, false, true], [false, true, false, true], [true, false, true, false],
    [false, true, false, true, false], [true, false, true, false, true],
    [false, true, false, true, false, true]]

theorem a2Act_a2Act (b : Bool) (x : Fin 3 × Fin 3 × Fin 3 × Fin 3) : a2Act b (a2Act b x) = x := by
  revert x
  cases b <;> decide

theorem exists_a2Words : ∀ x : Fin 3 × Fin 3 × Fin 3 × Fin 3, x.1 ≠ x.2.1 → x.2.2.1 ≠ x.2.2.2 →
    ¬ (x.2.2.1 = x.2.1 ∧ x.2.2.2 = x.1) → ∃ w ∈ a2Words,
      (a2ActList w x).1 < (a2ActList w x).2.1 ∧
        (a2ActList w x).2.2.1 < (a2ActList w x).2.2.2 := by
  decide

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem neg_Γ₀ (a : d.Γ₀) : -a = a := by
  rw [← neg_one_mul, d.neg_one_Γ₀, one_mul]

@[expose] def negRoot (x : d.Γ₀ → X) (c : d.Γ₀) : X := d.w₀ * x c * d.w₀

@[expose] def a2 : Fin 3 → Fin 3 → d.Γ₀ → X :=
  ![![fun _ => 1, d.x₂, d.x₆],
    ![d.negRoot d.x₂, fun _ => 1, d.x₅],
    ![d.negRoot d.x₆, d.negRoot d.x₅, fun _ => 1]]

theorem a2_01 : d.a2 0 1 = d.x₂ := rfl
theorem a2_12 : d.a2 1 2 = d.x₅ := rfl
theorem a2_02 : d.a2 0 2 = d.x₆ := rfl
theorem a2_10 : d.a2 1 0 = d.negRoot d.x₂ := rfl
theorem a2_21 : d.a2 2 1 = d.negRoot d.x₅ := rfl
theorem a2_20 : d.a2 2 0 = d.negRoot d.x₆ := rfl

theorem u_mul_w₀ : d.u * d.w₀ = d.w₀ * d.u :=
  d.gen_mul_w₀ false

theorem v_mul_w₀ : d.v * d.w₀ = d.w₀ * d.v :=
  d.gen_mul_w₀ true

theorem u_negRoot (x : d.Γ₀ → X) (a : d.Γ₀) :
    d.u * d.negRoot x a * d.u = d.w₀ * (d.u * x a * d.u) * d.w₀ := by
  rw [negRoot]
  calc d.u * (d.w₀ * x a * d.w₀) * d.u = (d.u * d.w₀) * x a * (d.w₀ * d.u) := by group
    _ = (d.w₀ * d.u) * x a * (d.u * d.w₀) := by rw [d.u_mul_w₀]
    _ = d.w₀ * (d.u * x a * d.u) * d.w₀ := by group

theorem v_negRoot (x : d.Γ₀ → X) (a : d.Γ₀) :
    d.v * d.negRoot x a * d.v = d.w₀ * (d.v * x a * d.v) * d.w₀ := by
  rw [negRoot]
  calc d.v * (d.w₀ * x a * d.w₀) * d.v = (d.v * d.w₀) * x a * (d.w₀ * d.v) := by group
    _ = (d.w₀ * d.v) * x a * (d.v * d.w₀) := by rw [d.v_mul_w₀]
    _ = d.w₀ * (d.v * x a * d.v) * d.w₀ := by group

theorem uvuvu_mul_self :
    d.u * d.v * d.u * d.v * d.u * (d.u * d.v * d.u * d.v * d.u) = 1 := by
  have uu (a : X) : d.u * (d.u * a) = a := by rw [← mul_assoc, d.u_mul_self, one_mul]
  have vv (a : X) : d.v * (d.v * a) = a := by rw [← mul_assoc, d.v_mul_self, one_mul]
  simp only [mul_assoc, uu, vv, d.u_mul_self]

theorem uvuvu_conj_x₂ (a : d.Γ₀) :
    d.u * d.v * d.u * d.v * d.u * d.x₂ a * (d.u * d.v * d.u * d.v * d.u)⁻¹ = d.x₂ a := by
  rw [conj_mul_conj, conj_mul_conj, conj_mul_conj, conj_mul_conj, d.u_conj_x₂, d.v_conj_x₅,
    d.u_conj_x₆, d.v_conj_x₆, d.u_conj_x₅]

theorem negRoot_x₂ (a : d.Γ₀) : d.negRoot d.x₂ a = d.v * d.x₂ a * d.v := by
  have hP : (d.u * d.v * d.u * d.v * d.u)⁻¹ = d.u * d.v * d.u * d.v * d.u :=
    inv_eq_of_mul_eq_one_right d.uvuvu_mul_self
  have h1 : d.w₀ = d.v * (d.u * d.v * d.u * d.v * d.u) := by
    rw [d.w₀_eq, show d.u * (d.v * (d.u * (d.v * (d.u * d.v)))) =
      d.u * d.v * d.u * d.v * d.u * d.v by group, d.uv_cube]
    group
  have h2 : d.w₀ = d.u * d.v * d.u * d.v * d.u * d.v := by
    rw [d.w₀_eq]
    group
  have h3 := d.uvuvu_conj_x₂ a
  rw [hP] at h3
  rw [negRoot]
  nth_rewrite 1 [h1]
  rw [h2]
  calc d.v * (d.u * d.v * d.u * d.v * d.u) * d.x₂ a * (d.u * d.v * d.u * d.v * d.u * d.v) =
      d.v * (d.u * d.v * d.u * d.v * d.u * d.x₂ a * (d.u * d.v * d.u * d.v * d.u)) * d.v := by
        group
    _ = d.v * d.x₂ a * d.v := by rw [h3]

theorem negRoot_x₅ (a : d.Γ₀) : d.negRoot d.x₅ a = d.u * (d.v * d.x₂ a * d.v) * d.u := by
  rw [← d.negRoot_x₂, d.u_negRoot, d.u_x₂, negRoot]

theorem negRoot_x₆ (a : d.Γ₀) : d.negRoot d.x₆ a = d.v * d.negRoot d.x₅ a * d.v := by
  rw [d.v_negRoot, d.v_x₅, negRoot]

theorem u_x₅ (a : d.Γ₀) : d.u * d.x₅ a * d.u = d.x₂ a :=
  conj_symm_of_involution d.u_mul_self d.u_x₂ a

theorem v_x₆ (a : d.Γ₀) : d.v * d.x₆ a * d.v = d.x₅ a :=
  conj_symm_of_involution d.v_mul_self d.v_x₅ a

theorem u_conj_a2 {i j : Fin 3} (hij : i ≠ j) (a : d.Γ₀) :
    d.u * d.a2 i j a * d.u = d.a2 (Fin.rev j) (Fin.rev i) a := by
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢
  · exact absurd rfl hij
  · exact d.u_x₂ a
  · exact d.u_x₆ a
  · rw [a2_10, d.u_negRoot, d.u_x₂]
    rfl
  · exact absurd rfl hij
  · exact d.u_x₅ a
  · rw [a2_20, d.u_negRoot, d.u_x₆]
    rfl
  · rw [a2_21, d.u_negRoot, d.u_x₅]
    rfl
  · exact absurd rfl hij

theorem v_conj_a2 {i j : Fin 3} (hij : i ≠ j) (a : d.Γ₀) :
    d.v * d.a2 i j a * d.v = d.a2 (a2Swap i) (a2Swap j) a := by
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢
  · exact absurd rfl hij
  · exact (d.negRoot_x₂ a).symm
  · exact d.v_x₆ a
  · rw [a2_10, d.negRoot_x₂]
    calc d.v * (d.v * d.x₂ a * d.v) * d.v = (d.v * d.v) * d.x₂ a * (d.v * d.v) := by group
      _ = d.x₂ a := by rw [d.v_mul_self, one_mul, mul_one]
  · exact absurd rfl hij
  · exact d.v_x₅ a
  · rw [a2_20, d.v_negRoot, d.v_x₆]
    rfl
  · rw [a2_21, d.v_negRoot, d.v_x₅]
    rfl
  · exact absurd rfl hij

theorem a2_add {i j : Fin 3} (hij : i ≠ j) (a b : d.Γ₀) :
    d.a2 i j a * d.a2 i j b = d.a2 i j (a + b) := by
  have hneg : ∀ x : d.Γ₀ → X, (∀ a b, x (a + b) = x a * x b) →
      d.negRoot x a * d.negRoot x b = d.negRoot x (a + b) := fun x hx => by
    rw [negRoot, negRoot, negRoot, hx]
    calc d.w₀ * x a * d.w₀ * (d.w₀ * x b * d.w₀) = d.w₀ * x a * (d.w₀ * d.w₀) * x b * d.w₀ := by
          group
      _ = d.w₀ * (x a * x b) * d.w₀ := by rw [d.w₀_mul_self, mul_one]; group
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢
  · exact absurd rfl hij
  · exact (d.x₂_add a b).symm
  · exact (d.x₆_add a b).symm
  · exact hneg _ d.x₂_add
  · exact absurd rfl hij
  · exact (d.x₅_add a b).symm
  · exact hneg _ d.x₆_add
  · exact hneg _ d.x₅_add
  · exact absurd rfl hij

theorem a2_mem_leviJ₀ (i j : Fin 3) (a : d.Γ₀) : d.a2 i j a ∈ d.leviJ₀ := by
  have h2 : d.negRoot d.x₂ a ∈ d.leviJ₀ := by
    rw [d.negRoot_x₂]
    exact mul_mem (mul_mem d.v_mem_leviJ₀ (d.U₂_le_leviJ₀ (d.x₂_mem_U₂ a))) d.v_mem_leviJ₀
  have h5 : d.negRoot d.x₅ a ∈ d.leviJ₀ := by
    rw [d.negRoot_x₅, ← d.negRoot_x₂]
    exact d.u_conj_mem_leviJ₀ h2
  have h6 : d.negRoot d.x₆ a ∈ d.leviJ₀ := by
    rw [d.negRoot_x₆]
    exact mul_mem (mul_mem d.v_mem_leviJ₀ h5) d.v_mem_leviJ₀
  fin_cases i <;> fin_cases j
  · exact one_mem _
  · exact d.U₂_le_leviJ₀ (d.x₂_mem_U₂ a)
  · exact d.U₆_le_leviJ₀ (d.x₆_mem_V a)
  · exact h2
  · exact one_mem _
  · exact d.U₅_le_leviJ₀ (d.x₅_mem_U₅ a)
  · exact h6
  · exact h5
  · exact one_mem _

@[expose] def A2Rel (i j k l : Fin 3) : Prop :=
  i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → ∀ a b : d.Γ₀,
    ⁅d.a2 i j a, d.a2 k l b⁆ =
      if j = k then d.a2 i l (a * b) else if i = l then d.a2 k j (-(a * b)) else 1

@[expose] def A2RelQ (x : Fin 3 × Fin 3 × Fin 3 × Fin 3) : Prop :=
  d.A2Rel x.1 x.2.1 x.2.2.1 x.2.2.2

theorem commutatorElement_conj_involution {g a b : X} (hg : g * g = 1) :
    ⁅g * a * g, g * b * g⁆ = g * ⁅a, b⁆ * g := by
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [commutatorElement_def, commutatorElement_def]
  nth_rewrite 2 [← hg']
  nth_rewrite 4 [← hg']
  nth_rewrite 6 [← hg']
  nth_rewrite 8 [← hg']
  nth_rewrite 10 [← hg']
  group

theorem A2RelQ.act_u {x : Fin 3 × Fin 3 × Fin 3 × Fin 3} (h : d.A2RelQ x) :
    d.A2RelQ (a2Act false x) := by
  obtain ⟨i, j, k, l⟩ := x
  intro hij hkl hex a b
  change Fin.rev j ≠ Fin.rev i at hij
  change Fin.rev l ≠ Fin.rev k at hkl
  change ¬ (Fin.rev l = Fin.rev i ∧ Fin.rev k = Fin.rev j) at hex
  change ⁅d.a2 (Fin.rev j) (Fin.rev i) a, d.a2 (Fin.rev l) (Fin.rev k) b⁆ =
    if Fin.rev i = Fin.rev l then d.a2 (Fin.rev j) (Fin.rev k) (a * b)
    else if Fin.rev j = Fin.rev k then d.a2 (Fin.rev l) (Fin.rev i) (-(a * b)) else 1
  have hij' : i ≠ j := fun e => hij (by rw [e])
  have hkl' : k ≠ l := fun e => hkl (by rw [e])
  have hex' : ¬ (k = j ∧ l = i) := fun ⟨e1, e2⟩ => hex ⟨by rw [e2], by rw [e1]⟩
  have hrel : ⁅d.a2 i j a, d.a2 k l b⁆ =
      if j = k then d.a2 i l (a * b) else if i = l then d.a2 k j (-(a * b)) else 1 :=
    h hij' hkl' hex' a b
  have e1 : ⁅d.a2 (Fin.rev j) (Fin.rev i) a, d.a2 (Fin.rev l) (Fin.rev k) b⁆ =
      d.u * ⁅d.a2 i j a, d.a2 k l b⁆ * d.u := by
    rw [← d.u_conj_a2 hij' a, ← d.u_conj_a2 hkl' b]
    exact commutatorElement_conj_involution d.u_mul_self
  rw [e1, hrel]
  by_cases hjk : j = k
  · have hil : i ≠ l := fun e => hex' ⟨hjk.symm, e.symm⟩
    have hil' : Fin.rev i ≠ Fin.rev l := fun e => hil (Fin.rev_inj.1 e)
    have hjk' : Fin.rev j = Fin.rev k := by rw [hjk]
    rw [ite_eq_left hjk, ite_eq_right hil', ite_eq_left hjk', d.u_conj_a2 hil, d.neg_Γ₀]
  · have hjk' : Fin.rev j ≠ Fin.rev k := fun e => hjk (Fin.rev_inj.1 e)
    rw [ite_eq_right hjk]
    by_cases hil : i = l
    · have hil' : Fin.rev i = Fin.rev l := by rw [hil]
      rw [ite_eq_left hil, ite_eq_left hil', d.u_conj_a2 (Ne.symm hjk), d.neg_Γ₀]
    · have hil' : Fin.rev i ≠ Fin.rev l := fun e => hil (Fin.rev_inj.1 e)
      rw [ite_eq_right hil, ite_eq_right hil', ite_eq_right hjk', mul_one, d.u_mul_self]

theorem A2RelQ.act_v {x : Fin 3 × Fin 3 × Fin 3 × Fin 3} (h : d.A2RelQ x) :
    d.A2RelQ (a2Act true x) := by
  obtain ⟨i, j, k, l⟩ := x
  have hinj : Function.Injective a2Swap := by decide
  intro hij hkl hex a b
  change a2Swap i ≠ a2Swap j at hij
  change a2Swap k ≠ a2Swap l at hkl
  change ¬ (a2Swap k = a2Swap j ∧ a2Swap l = a2Swap i) at hex
  change ⁅d.a2 (a2Swap i) (a2Swap j) a, d.a2 (a2Swap k) (a2Swap l) b⁆ =
    if a2Swap j = a2Swap k then d.a2 (a2Swap i) (a2Swap l) (a * b)
    else if a2Swap i = a2Swap l then d.a2 (a2Swap k) (a2Swap j) (-(a * b)) else 1
  have hij' : i ≠ j := fun e => hij (by rw [e])
  have hkl' : k ≠ l := fun e => hkl (by rw [e])
  have hex' : ¬ (k = j ∧ l = i) := fun ⟨e1, e2⟩ => hex ⟨by rw [e1], by rw [e2]⟩
  have hrel : ⁅d.a2 i j a, d.a2 k l b⁆ =
      if j = k then d.a2 i l (a * b) else if i = l then d.a2 k j (-(a * b)) else 1 :=
    h hij' hkl' hex' a b
  have e1 : ⁅d.a2 (a2Swap i) (a2Swap j) a, d.a2 (a2Swap k) (a2Swap l) b⁆ =
      d.v * ⁅d.a2 i j a, d.a2 k l b⁆ * d.v := by
    rw [← d.v_conj_a2 hij' a, ← d.v_conj_a2 hkl' b]
    exact commutatorElement_conj_involution d.v_mul_self
  rw [e1, hrel]
  by_cases hjk : j = k
  · have hil : i ≠ l := fun e => hex' ⟨hjk.symm, e.symm⟩
    have hjk' : a2Swap j = a2Swap k := by rw [hjk]
    rw [ite_eq_left hjk, ite_eq_left hjk', d.v_conj_a2 hil]
  · have hjk' : a2Swap j ≠ a2Swap k := fun e => hjk (hinj e)
    rw [ite_eq_right hjk, ite_eq_right hjk']
    by_cases hil : i = l
    · have hil' : a2Swap i = a2Swap l := by rw [hil]
      rw [ite_eq_left hil, ite_eq_left hil', d.v_conj_a2 (Ne.symm hjk)]
    · have hil' : a2Swap i ≠ a2Swap l := fun e => hil (hinj e)
      rw [ite_eq_right hil, ite_eq_right hil', mul_one, d.v_mul_self]

theorem A2RelQ.act {b : Bool} {x : Fin 3 × Fin 3 × Fin 3 × Fin 3} (h : d.A2RelQ x) :
    d.A2RelQ (a2Act b x) := by
  cases b
  · exact h.act_u
  · exact h.act_v

theorem A2RelQ.of_actList (w : List Bool) {x : Fin 3 × Fin 3 × Fin 3 × Fin 3}
    (h : d.A2RelQ (a2ActList w x)) : d.A2RelQ x := by
  induction w generalizing x with
  | nil => exact h
  | cons b l ih =>
    apply ih
    have h1 := (show d.A2RelQ (a2Act b (a2ActList l x)) from h).act (b := b)
    rwa [a2Act_a2Act] at h1

theorem commute_x₂_x₂ (a b : d.Γ₀) : Commute (d.x₂ a) (d.x₂ b) := by
  rw [Commute, SemiconjBy, ← d.x₂_add, ← d.x₂_add, add_comm]

theorem commute_x₅_x₅ (a b : d.Γ₀) : Commute (d.x₅ a) (d.x₅ b) := by
  rw [Commute, SemiconjBy, ← d.x₅_add, ← d.x₅_add, add_comm]

theorem commute_x₆_x₆ (a b : d.Γ₀) : Commute (d.x₆ a) (d.x₆ b) := by
  rw [Commute, SemiconjBy, ← d.x₆_add, ← d.x₆_add, add_comm]

theorem A2Rel_of_lt {i j k l : Fin 3} (hij : i < j) (hkl : k < l) : d.A2Rel i j k l := by
  intro _ _ _ a b
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceLT, Fin.isValue, Fin.reduceEq,
      ↓reduceIte] at hij hkl ⊢
  · exact commutatorElement_eq_one_iff_commute.2 (d.commute_x₂_x₂ a b)
  · exact commutatorElement_eq_one_iff_commute.2 (d.commute₂₆ a b)
  · exact d.comm₂₅ a b
  · exact commutatorElement_eq_one_iff_commute.2 (d.commute₂₆ b a).symm
  · exact commutatorElement_eq_one_iff_commute.2 (d.commute_x₆_x₆ a b)
  · exact commutatorElement_eq_one_iff_commute.2 (d.commute₅₆ b a).symm
  · rw [← commutatorElement_inv]
    change (⁅d.x₂ b, d.x₅ a⁆)⁻¹ = d.x₆ (-(a * b))
    rw [d.comm₂₅, d.neg_Γ₀, d.x₆_inv, mul_comm]
  · exact commutatorElement_eq_one_iff_commute.2 (d.commute₅₆ a b)
  · exact commutatorElement_eq_one_iff_commute.2 (d.commute_x₅_x₅ a b)

theorem A2Rel_all (i j k l : Fin 3) : d.A2Rel i j k l := by
  intro hij hkl hex
  obtain ⟨w, -, h1, h2⟩ := exists_a2Words (i, j, k, l) hij hkl hex
  exact (A2RelQ.of_actList d w (d.A2Rel_of_lt h1 h2)) hij hkl hex

theorem isSteinbergFamily_a2 : CFSG.DesarguesianPlanes.IsSteinbergFamily d.a2 :=
  ⟨fun _ _ hij a b => d.a2_add hij a b, fun i j k l => d.A2Rel_all i j k l⟩

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
