module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

open Subgroup
open scoped Pointwise commutatorElement

variable {X : Type*} [Group X]

theorem card_sup_le_of_le_normalizer [Finite X] {A B : Subgroup X}
    (h : B ≤ normalizer (A : Set X)) : Nat.card (A ⊔ B : Subgroup X) ≤ Nat.card A * Nat.card B := by
  have hc : ((A ⊔ B : Subgroup X) : Set X) = (A : Set X) * (B : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B h
  calc Nat.card (A ⊔ B : Subgroup X) = Nat.card ((A : Set X) * (B : Set X)) := by
        rw [← hc]
        rfl
    _ ≤ Nat.card (A : Set X) * Nat.card (B : Set X) := Set.natCard_mul_le
    _ = Nat.card A * Nat.card B := rfl

theorem card_closure_le_two_pow [Finite X] (S : Finset X)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hsq : ∀ a ∈ S, a ^ 2 = 1) :
    Nat.card (closure (S : Set X)) ≤ 2 ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, closure_empty, Finset.card_empty, pow_zero]
    exact le_of_eq (Subgroup.card_bot)
  | insert a S haS ih =>
    have ih' := ih (fun x hx y hy => hcomm x (Finset.mem_insert_of_mem hx) y
      (Finset.mem_insert_of_mem hy)) fun x hx => hsq x (Finset.mem_insert_of_mem hx)
    have ha : a ∈ insert a S := Finset.mem_insert_self a S
    have hza : Nat.card (zpowers a) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (hsq a ha))
    have hle : zpowers a ≤ normalizer (closure (S : Set X) : Set X) := by
      have hcen : zpowers a ≤ centralizer (closure (S : Set X) : Set X) := by
        rw [zpowers_le, mem_centralizer_iff]
        intro x hx
        induction hx using Subgroup.closure_induction with
        | mem y hy => exact hcomm y (Finset.mem_insert_of_mem hy) a ha
        | one => rw [one_mul, mul_one]
        | mul y z _ _ hy hz => rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]
        | inv y _ hy =>
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hy, mul_inv_cancel_right]
      exact hcen.trans (Subgroup.centralizer_le_normalizer _)
    rw [Finset.coe_insert, Set.insert_eq, closure_union, ← zpowers_eq_closure, sup_comm,
      Finset.card_insert_of_notMem haS, pow_succ]
    calc Nat.card (closure (S : Set X) ⊔ zpowers a : Subgroup X)
        ≤ Nat.card (closure (S : Set X)) * Nat.card (zpowers a) :=
          card_sup_le_of_le_normalizer hle
      _ ≤ 2 ^ S.card * 2 := Nat.mul_le_mul ih' hza

@[expose] def normOp (j v : X) : X :=
  v * MulAut.conj j v * MulAut.conj j (MulAut.conj j v)

section Norm

variable {C V : Subgroup X} {j : X}

theorem normOp_mem (hjV : ∀ v ∈ V, MulAut.conj j v ∈ V) {v : X} (hv : v ∈ V) :
    normOp j v ∈ V :=
  mul_mem (mul_mem hv (hjV v hv)) (hjV _ (hjV v hv))

theorem conj_normOp (hj3 : j ^ 3 = 1) (hjV : ∀ v ∈ V, MulAut.conj j v ∈ V)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {v : X} (hv : v ∈ V) :
    MulAut.conj j (normOp j v) = normOp j v := by
  have hj3' : j * j * j = 1 := by rw [← pow_three', hj3]
  have h3 : MulAut.conj j (MulAut.conj j (MulAut.conj j v)) = v := by
    simp only [MulAut.conj_apply]
    calc j * (j * (j * v * j⁻¹) * j⁻¹) * j⁻¹ = (j * j * j) * v * (j * j * j)⁻¹ := by group
      _ = v := by rw [hj3', one_mul, inv_one, mul_one]
  have h1 := hjV v hv
  have h2 := hjV _ h1
  rw [normOp, map_mul, map_mul, h3, hVc _ (mul_mem h1 h2) v hv, mul_assoc]

theorem normOp_mul (hjV : ∀ v ∈ V, MulAut.conj j v ∈ V)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {v w : X} (hv : v ∈ V) (hw : w ∈ V) :
    normOp j (v * w) = normOp j v * normOp j w := by
  have hv1 := hjV v hv
  have hv2 := hjV _ hv1
  have hw1 := hjV w hw
  have hw2 := hjV _ hw1
  simp only [normOp, map_mul]
  have key : ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, ∀ d ∈ V, ∀ e ∈ V, ∀ f ∈ V,
      a * b * (c * d) * (e * f) = a * c * e * (b * d * f) := by
    intro a ha b hb c hc d hd e he f hf
    calc a * b * (c * d) * (e * f) = a * (b * c) * d * (e * f) := by group
      _ = a * (c * b) * d * (e * f) := by rw [hVc b hb c hc]
      _ = a * c * (b * d * e) * f := by group
      _ = a * c * (e * (b * d)) * f := by rw [hVc _ (mul_mem hb hd) e he]
      _ = a * c * e * (b * d * f) := by group
  exact key _ hv _ hw _ hv1 _ hw1 _ hv2 _ hw2

theorem normOp_one : normOp j (1 : X) = 1 := by
  simp [normOp]

theorem normOp_inv (hjV : ∀ v ∈ V, MulAut.conj j v ∈ V)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {v : X} (hv : v ∈ V) :
    normOp j v⁻¹ = (normOp j v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← normOp_mul hjV hVc (inv_mem hv) hv, inv_mul_cancel, normOp_one]

theorem mul_normOp_eq (hjV : ∀ v ∈ V, MulAut.conj j v ∈ V) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    {v : X} (hv : v ∈ V) : v * normOp j v = ⁅MulAut.conj j v, j⁆ := by
  have h1 := hjV v hv
  set w := MulAut.conj j v with hw
  have hinv : w⁻¹ = w := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hV2 _ h1]
  have hv' : v * v = 1 := by rw [← sq, hV2 v hv]
  calc v * normOp j v = (v * v) * (w * MulAut.conj j w) := by
        rw [normOp, ← hw]
        simp only [mul_assoc]
    _ = w * MulAut.conj j w := by rw [hv', one_mul]
    _ = w * j * w⁻¹ * j⁻¹ := by
        rw [hinv, MulAut.conj_apply]
        simp only [mul_assoc]
    _ = ⁅w, j⁆ := (commutatorElement_def w j).symm

theorem normOp_of_central {c : X} (hc : ∀ g : X, g * c = c * g) (hc2 : c ^ 2 = 1) :
    normOp j c = c := by
  have hfix : MulAut.conj j c = c := by
    rw [MulAut.conj_apply, hc j, mul_inv_cancel_right]
  rw [normOp, hfix, hfix, ← sq, hc2, one_mul]

theorem normOp_conj {j' : X} (hjj : j' * j = j * j') (v : X) :
    normOp j (MulAut.conj j' v) = MulAut.conj j' (normOp j v) := by
  have hc : ∀ w : X, MulAut.conj j (MulAut.conj j' w) = MulAut.conj j' (MulAut.conj j w) := by
    intro w
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hjj]
  simp only [normOp, map_mul, hc]

variable (hj3 : j ^ 3 = 1) (hjV : ∀ v ∈ V, MulAut.conj j v ∈ V)
  (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
  (hCV : C ≤ V) (hCZ : ∀ c ∈ C, ∀ g : X, g * c = c * g)
  (hfix : ∀ v ∈ V, MulAut.conj j v = v → v ∈ C)
include hj3 hjV hVc hV2 hCV hCZ hfix

omit hV2 hCV hCZ in
theorem normOp_mem_C {v : X} (hv : v ∈ V) : normOp j v ∈ C :=
  hfix _ (normOp_mem hjV hv) (conj_normOp hj3 hjV hVc hv)

omit hj3 hjV hVc hfix in
theorem normOp_eq_self_of_mem {c : X} (hc : c ∈ C) : normOp j c = c :=
  normOp_of_central (hCZ c hc) (hV2 c (hCV hc))

omit hCV in
theorem mem_commutator_iff_normOp {J : Subgroup X} (hjJ : j ∈ J)
    (hJc : ∀ j' ∈ J, j' * j = j * j') (hJV : ∀ j' ∈ J, ∀ v ∈ V, MulAut.conj j' v ∈ V) {x : X} :
    x ∈ ⁅V, J⁆ ↔ x ∈ V ∧ normOp j x = 1 := by
  constructor
  · intro hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, j', hj', rfl⟩ := hy
      have hconj : j' * v⁻¹ * j'⁻¹ = MulAut.conj j' v⁻¹ := (MulAut.conj_apply j' v⁻¹).symm
      have hmem : MulAut.conj j' v⁻¹ ∈ V := hJV j' hj' _ (inv_mem hv)
      have hy : ⁅v, j'⁆ = v * MulAut.conj j' v⁻¹ := by
        rw [commutatorElement_def, ← hconj]
        group
      refine ⟨by rw [hy]; exact mul_mem hv hmem, ?_⟩
      rw [hy, normOp_mul hjV hVc hv hmem, normOp_conj (hJc j' hj'), normOp_inv hjV hVc hv]
      have hNC := normOp_mem_C hj3 hjV hVc hfix hv
      simp only [MulAut.conj_apply]
      rw [hCZ _ (inv_mem hNC) j', mul_inv_cancel_right, mul_inv_cancel]
    | one => exact ⟨one_mem _, normOp_one⟩
    | mul y z _ _ hy hz =>
      exact ⟨mul_mem hy.1 hz.1, by rw [normOp_mul hjV hVc hy.1 hz.1, hy.2, hz.2, one_mul]⟩
    | inv y _ hy =>
      exact ⟨inv_mem hy.1, by rw [normOp_inv hjV hVc hy.1, hy.2, inv_one]⟩
  · rintro ⟨hx, h1⟩
    have h := mul_normOp_eq hjV hV2 hx
    rw [h1, mul_one] at h
    rw [h]
    exact Subgroup.commutator_mem_commutator (hjV x hx) hjJ

theorem inf_commutator_eq_bot {J : Subgroup X} (hjJ : j ∈ J)
    (hJc : ∀ j' ∈ J, j' * j = j * j') (hJV : ∀ j' ∈ J, ∀ v ∈ V, MulAut.conj j' v ∈ V) :
    C ⊓ ⁅V, J⁆ = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨hc, hcJ⟩
  have h := ((mem_commutator_iff_normOp hj3 hjV hVc hV2 hCZ hfix hjJ hJc hJV).1 hcJ).2
  rw [normOp_eq_self_of_mem hV2 hCV hCZ hc] at h
  rw [Subgroup.mem_bot]
  exact h

theorem sup_commutator_eq {J : Subgroup X} (hjJ : j ∈ J)
    (hJc : ∀ j' ∈ J, j' * j = j * j') (hJV : ∀ j' ∈ J, ∀ v ∈ V, MulAut.conj j' v ∈ V) :
    C ⊔ ⁅V, J⁆ = V := by
  refine le_antisymm (sup_le hCV fun x hx =>
    ((mem_commutator_iff_normOp hj3 hjV hVc hV2 hCZ hfix hjJ hJc hJV).1 hx).1)
    fun v hv => ?_
  have hN := normOp_mem_C hj3 hjV hVc hfix hv
  have hmem : v * normOp j v ∈ ⁅V, J⁆ := by
    rw [mul_normOp_eq hjV hV2 hv]
    exact Subgroup.commutator_mem_commutator (hjV v hv) hjJ
  have hv' : v = (v * normOp j v) * (normOp j v)⁻¹ := by group
  rw [hv']
  exact mul_mem (Subgroup.mem_sup_right hmem) (Subgroup.mem_sup_left (inv_mem hN))

end Norm

section CommutatorIdentities

variable {a a' b b' c d : X}

theorem commutatorElement_mul_left_eq (h : ⁅a', b⁆ * a = a * ⁅a', b⁆) :
    ⁅a * a', b⁆ = ⁅a', b⁆ * ⁅a, b⁆ := by
  calc ⁅a * a', b⁆ = a * ⁅a', b⁆ * (b * a⁻¹ * b⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = ⁅a', b⁆ * a * (b * a⁻¹ * b⁻¹) := by rw [← h]
    _ = ⁅a', b⁆ * ⁅a, b⁆ := by
        simp only [commutatorElement_def]
        group

theorem commutatorElement_mul_right_eq (h : ⁅a, b'⁆ * b = b * ⁅a, b'⁆) :
    ⁅a, b * b'⁆ = ⁅a, b⁆ * ⁅a, b'⁆ := by
  calc ⁅a, b * b'⁆ = ⁅a, b⁆ * (b * ⁅a, b'⁆) * b⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅a, b⁆ * (⁅a, b'⁆ * b) * b⁻¹ := by rw [h]
    _ = ⁅a, b⁆ * ⁅a, b'⁆ := by group

theorem commutatorElement_inv_left_eq (h : ⁅a, b⁆ * a = a * ⁅a, b⁆) :
    ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
  have h' : ⁅a, b⁆⁻¹ * a = a * ⁅a, b⁆⁻¹ := (Commute.inv_left (show Commute ⁅a, b⁆ a from h)).eq
  calc ⁅a⁻¹, b⁆ = a⁻¹ * ⁅a, b⁆⁻¹ * a := by
        simp only [commutatorElement_def]
        group
    _ = ⁅a, b⁆⁻¹ := by rw [mul_assoc, h', inv_mul_cancel_left]

theorem commutatorElement_inv_right_eq (h : ⁅a, b⁆ * b = b * ⁅a, b⁆) :
    ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
  have h' : ⁅a, b⁆⁻¹ * b = b * ⁅a, b⁆⁻¹ := (Commute.inv_left (show Commute ⁅a, b⁆ b from h)).eq
  calc ⁅a, b⁻¹⁆ = b⁻¹ * ⁅a, b⁆⁻¹ * b := by
        simp only [commutatorElement_def]
        group
    _ = ⁅a, b⁆⁻¹ := by rw [mul_assoc, h', inv_mul_cancel_left]

theorem commutatorElement_mul_mul_eq (hac : a * c = c * a) (hbd : b * d = d * b)
    (h1 : ⁅b, c⁆ * a = a * ⁅b, c⁆) (h2 : ⁅a, d⁆ * c = c * ⁅a, d⁆) :
    ⁅a * b, c * d⁆ = ⁅b, c⁆ * ⁅a, d⁆ := by
  have e1 : b * c = ⁅b, c⁆ * c * b := by
    simp only [commutatorElement_def]
    group
  have e2 : a * d = ⁅a, d⁆ * d * a := by
    simp only [commutatorElement_def]
    group
  have key : a * b * (c * d) = ⁅b, c⁆ * ⁅a, d⁆ * (c * d) * (a * b) := by
    calc a * b * (c * d) = a * (b * c) * d := by group
      _ = (a * ⁅b, c⁆) * c * b * d := by rw [e1]; group
      _ = ⁅b, c⁆ * (a * c) * (b * d) := by rw [← h1]; group
      _ = ⁅b, c⁆ * c * (a * d) * b := by rw [hac, hbd]; group
      _ = ⁅b, c⁆ * (c * ⁅a, d⁆) * d * a * b := by rw [e2]; group
      _ = ⁅b, c⁆ * ⁅a, d⁆ * (c * d) * (a * b) := by rw [← h2]; group
  calc ⁅a * b, c * d⁆ = a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹ := commutatorElement_def _ _
    _ = ⁅b, c⁆ * ⁅a, d⁆ := by rw [key]; group

theorem commutatorElement_central_mul (hc : ∀ g : X, g * c = c * g)
    (hd : ∀ g : X, g * d = d * g) : ⁅c * a, d * b⁆ = ⁅a, b⁆ := by
  have hc1 : ⁅c, d * b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hc _).symm
  have hd1 : ⁅a, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hd a)
  rw [commutatorElement_mul_left_eq (hc _), hc1, mul_one,
    commutatorElement_mul_right_eq (hd _), hd1, one_mul]

end CommutatorIdentities

section Bilinear

variable {T Z D : Subgroup X}
  (hcent : ∀ u ∈ T, ∀ v ∈ T, ∀ w ∈ T, ⁅u, v⁆ * w = w * ⁅u, v⁆)
  (hZc : ∀ z ∈ Z, ∀ w ∈ T, z * w = w * z) (hZT : Z ≤ T)
include hcent hZc hZT

theorem commutator_mem_of_mem_sup_right {x y₁ y₂ : X} (hx : x ∈ T) (hy₁ : y₁ ∈ T) (hy₂ : y₂ ∈ T)
    (h₁ : ⁅x, y₁⁆ ∈ D) (h₂ : ⁅x, y₂⁆ ∈ D) :
    ∀ b ∈ Z ⊔ zpowers y₁ ⊔ zpowers y₂, ⁅x, b⁆ ∈ D := by
  let Bx : Subgroup X :=
    { carrier := {b | b ∈ T ∧ ⁅x, b⁆ ∈ D}
      mul_mem' := fun {b b'} hb hb' => ⟨mul_mem hb.1 hb'.1, by
        rw [commutatorElement_mul_right_eq (hcent x hx b' hb'.1 b hb.1)]
        exact mul_mem hb.2 hb'.2⟩
      one_mem' := ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
      inv_mem' := fun {b} hb => ⟨inv_mem hb.1, by
        rw [commutatorElement_inv_right_eq (hcent x hx b hb.1 b hb.1)]
        exact inv_mem hb.2⟩ }
  have hZB : Z ≤ Bx := fun z hz => ⟨hZT hz, by
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hZc z hz x hx).symm]
    exact one_mem _⟩
  have hle : Z ⊔ zpowers y₁ ⊔ zpowers y₂ ≤ Bx :=
    sup_le (sup_le hZB ((zpowers_le).2 ⟨hy₁, h₁⟩)) ((zpowers_le).2 ⟨hy₂, h₂⟩)
  exact fun b hb => (hle hb).2

theorem commutator_mem_of_mem_sup_left {b x₁ x₂ : X} (hb : b ∈ T) (hx₁ : x₁ ∈ T) (hx₂ : x₂ ∈ T)
    (h₁ : ⁅x₁, b⁆ ∈ D) (h₂ : ⁅x₂, b⁆ ∈ D) :
    ∀ a ∈ Z ⊔ zpowers x₁ ⊔ zpowers x₂, ⁅a, b⁆ ∈ D := by
  let Ab : Subgroup X :=
    { carrier := {a | a ∈ T ∧ ⁅a, b⁆ ∈ D}
      mul_mem' := fun {a a'} ha ha' => ⟨mul_mem ha.1 ha'.1, by
        rw [commutatorElement_mul_left_eq (hcent a' ha'.1 b hb a ha.1)]
        exact mul_mem ha'.2 ha.2⟩
      one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        rw [commutatorElement_inv_left_eq (hcent a ha.1 b hb a ha.1)]
        exact inv_mem ha.2⟩ }
  have hZA : Z ≤ Ab := fun z hz => ⟨hZT hz, by
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hZc z hz b hb)]
    exact one_mem _⟩
  have hle : Z ⊔ zpowers x₁ ⊔ zpowers x₂ ≤ Ab :=
    sup_le (sup_le hZA ((zpowers_le).2 ⟨hx₁, h₁⟩)) ((zpowers_le).2 ⟨hx₂, h₂⟩)
  exact fun a ha => (hle ha).2

theorem commutator_le_closure_four {A B : Subgroup X} {x₁ x₂ y₁ y₂ : X} (hx₁ : x₁ ∈ T)
    (hx₂ : x₂ ∈ T) (hy₁ : y₁ ∈ T) (hy₂ : y₂ ∈ T)
    (hA : A ≤ Z ⊔ zpowers x₁ ⊔ zpowers x₂) (hB : B ≤ Z ⊔ zpowers y₁ ⊔ zpowers y₂)
    (hBT : B ≤ T) :
    ⁅A, B⁆ ≤ closure {⁅x₁, y₁⁆, ⁅x₁, y₂⁆, ⁅x₂, y₁⁆, ⁅x₂, y₂⁆} := by
  set D := closure ({⁅x₁, y₁⁆, ⁅x₁, y₂⁆, ⁅x₂, y₁⁆, ⁅x₂, y₂⁆} : Set X) with hD
  have hgen : ∀ g ∈ ({⁅x₁, y₁⁆, ⁅x₁, y₂⁆, ⁅x₂, y₁⁆, ⁅x₂, y₂⁆} : Set X), g ∈ D :=
    fun g hg => subset_closure hg
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hb' := hB hb
  have h1 : ⁅x₁, b⁆ ∈ D := commutator_mem_of_mem_sup_right (D := D) hcent hZc hZT hx₁ hy₁ hy₂
    (hgen _ (by simp)) (hgen _ (by simp)) b hb'
  have h2 : ⁅x₂, b⁆ ∈ D := commutator_mem_of_mem_sup_right (D := D) hcent hZc hZT hx₂ hy₁ hy₂
    (hgen _ (by simp)) (hgen _ (by simp)) b hb'
  exact commutator_mem_of_mem_sup_left (D := D) hcent hZc hZT (hBT hb) hx₁ hx₂ h1 h2 a (hA ha)

end Bilinear

end CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
