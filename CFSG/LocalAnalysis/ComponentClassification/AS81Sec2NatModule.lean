module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ComponentClassification.AS81.Sec2Nat

open Equiv Equiv.Perm
open scoped Pointwise

@[expose] def act (σ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  fun i => v (σ⁻¹ i)

@[simp] theorem act_apply (σ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) (i : Fin 6) :
    act σ v i = v (σ⁻¹ i) := rfl

theorem act_mul (σ τ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) :
    act (σ * τ) v = act σ (act τ v) := by
  funext i
  simp [mul_inv_rev]

theorem act_one (v : Fin 6 → ZMod 2) : act 1 v = v := by
  funext i
  simp

theorem act_add (σ : Perm (Fin 6)) (v w : Fin 6 → ZMod 2) :
    act σ (v + w) = act σ v + act σ w := rfl

theorem act_zero (σ : Perm (Fin 6)) : act σ 0 = 0 := rfl

theorem act_ones (σ : Perm (Fin 6)) : act σ 1 = 1 := rfl

theorem act_inv_act (σ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) : act σ⁻¹ (act σ v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_injective (σ : Perm (Fin 6)) : Function.Injective (act σ) := fun v w h => by
  rw [← act_inv_act σ v, h, act_inv_act]

theorem act_conj (g σ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) :
    act g⁻¹ (act (g * σ * g⁻¹) (act g v)) = act σ v := by
  rw [← act_mul, ← act_mul]
  congr 1
  group

theorem sum_act (σ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) : ∑ i, act σ v i = ∑ i, v i :=
  Equiv.sum_comp σ⁻¹ v

theorem sum_add_act (σ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) : ∑ i, (v + act σ v) i = 0 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, sum_act]
  exact CharTwo.add_self_eq_zero _

@[expose] def lay {ι : Type*} (D : ι → Perm (Fin 6)) : ℕ → Set (Fin 6 → ZMod 2)
  | 0 => {v | v = 0 ∨ v = 1}
  | k + 1 => {v | ∀ i, v + act (D i) v ∈ lay D k}

theorem mem_lay_zero {ι : Type*} (D : ι → Perm (Fin 6)) (v : Fin 6 → ZMod 2) :
    v ∈ lay D 0 ↔ v = 0 ∨ v = 1 := Iff.rfl

theorem mem_lay_succ {ι : Type*} (D : ι → Perm (Fin 6)) (k : ℕ) (v : Fin 6 → ZMod 2) :
    v ∈ lay D (k + 1) ↔ ∀ i, v + act (D i) v ∈ lay D k := Iff.rfl

theorem mem_lay_conj {ι : Type*} (D : ι → Perm (Fin 6)) (g : Perm (Fin 6)) (k : ℕ)
    (v : Fin 6 → ZMod 2) : v ∈ lay (fun i => g * D i * g⁻¹) k ↔ act g⁻¹ v ∈ lay D k := by
  induction k generalizing v with
  | zero =>
    simp only [mem_lay_zero]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl (act_zero _)
      · exact Or.inr (act_ones _)
    · rintro (h | h)
      · exact Or.inl (act_injective g⁻¹ (h.trans (act_zero _).symm))
      · exact Or.inr (act_injective g⁻¹ (h.trans (act_ones _).symm))
  | succ k ih =>
    simp only [mem_lay_succ, ih]
    refine forall_congr' fun i => ?_
    rw [act_add, ← act_mul, show g⁻¹ * (g * D i * g⁻¹) = D i * g⁻¹ by group, act_mul]

@[expose] def d0 : Fin 8 → Perm (Fin 6) :=
  ![1, swap 0 2 * swap 1 3, swap 0 1 * swap 2 3, swap 0 3 * swap 1 2,
    swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, swap 0 3 * swap 3 2 * swap 2 1 * swap 4 5,
    swap 0 2 * swap 4 5, swap 1 3 * swap 4 5]

theorem d0_mul : ∀ i j : Fin 8, ∃ k, d0 i * d0 j = d0 k := by
  decide +kernel

theorem d0_inv : ∀ i : Fin 8, ∃ k, (d0 i)⁻¹ = d0 k := by
  decide +kernel

theorem d0_sign : ∀ i : Fin 8, sign (d0 i) = 1 := by
  decide +kernel

theorem d0_injective : Function.Injective d0 := by
  decide +kernel

theorem d0_mem (i : Fin 8) : d0 i ∈ alternatingGroup (Fin 6) :=
  mem_alternatingGroup.mpr (d0_sign i)

@[expose] def D0 : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {x | ∃ i, d0 i = x.1}
  mul_mem' := by
    rintro x y ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hk⟩ := d0_mul i j
    exact ⟨k, by rw [← hk, hi, hj]; rfl⟩
  one_mem' := ⟨0, rfl⟩
  inv_mem' := by
    rintro x ⟨i, hi⟩
    obtain ⟨k, hk⟩ := d0_inv i
    exact ⟨k, by rw [← hk, hi]; rfl⟩

theorem mem_D0 {x : alternatingGroup (Fin 6)} : x ∈ D0 ↔ ∃ i, d0 i = x.1 := Iff.rfl

theorem card_D0 : Nat.card D0 = 8 := by
  let e : Fin 8 ≃ D0 := Equiv.ofBijective (fun i => ⟨⟨d0 i, d0_mem i⟩, i, rfl⟩)
    ⟨fun i j h => d0_injective (congrArg (fun x : D0 => x.1.1) h),
      fun ⟨_, i, hi⟩ => ⟨i, Subtype.ext (Subtype.ext hi)⟩⟩
  rw [← Nat.card_congr e, Nat.card_fin]

theorem exists_conj_D0 (P : Sylow 2 (alternatingGroup (Fin 6))) :
    ∃ g : alternatingGroup (Fin 6), ∀ x : alternatingGroup (Fin 6),
      x ∈ (P : Subgroup (alternatingGroup (Fin 6))) ↔ g⁻¹ * x * g ∈ D0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl
  have hidx : ¬ 2 ∣ D0.index := by
    intro h2
    have := D0.card_mul_index
    rw [card_D0, hA] at this
    omega
  have hp : IsPGroup 2 D0 := IsPGroup.of_card (n := 3) (by rw [card_D0]; norm_num)
  let P₀ : Sylow 2 (alternatingGroup (Fin 6)) := hp.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) P₀ P
  refine ⟨g, fun x => ?_⟩
  have h2 : ((g • P₀ : Sylow 2 (alternatingGroup (Fin 6))) : Subgroup (alternatingGroup (Fin 6))) =
      (P : Subgroup (alternatingGroup (Fin 6))) := by rw [hg]
  have h3 : x ∈ (P : Subgroup (alternatingGroup (Fin 6))) ↔
      g⁻¹ * x * g ∈ (P₀ : Subgroup (alternatingGroup (Fin 6))) := by
    rw [← h2, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  exact h3

@[expose] def z0 : Fin 6 → ZMod 2 := ![1, 1, 1, 1, 0, 0]

private theorem lay_one_aux : ∀ v : Fin 6 → ZMod 2, v 0 + v 1 + v 2 + v 3 + v 4 + v 5 = 0 →
    ((∀ i, v + act (d0 i) v = 0 ∨ v + act (d0 i) v = 1) ↔
      (v = 0 ∨ v = 1 ∨ v = z0 ∨ v = z0 + 1)) := by
  decide +kernel

theorem mem_lay_d0_one {v : Fin 6 → ZMod 2} (hv : ∑ i, v i = 0) :
    v ∈ lay d0 1 ↔ v = 0 ∨ v = 1 ∨ v = z0 ∨ v = z0 + 1 := by
  rw [Fin.sum_univ_six] at hv
  exact lay_one_aux v hv

private theorem lay_two_aux : ∀ v : Fin 6 → ZMod 2, v 0 + v 1 + v 2 + v 3 + v 4 + v 5 = 0 →
    ((∀ i, v + act (d0 i) v = 0 ∨ v + act (d0 i) v = 1 ∨ v + act (d0 i) v = z0 ∨
        v + act (d0 i) v = z0 + 1) ↔
      (v 0 = v 2 ∧ v 1 = v 3 ∧ v 4 = v 5)) := by
  decide +kernel

theorem mem_lay_d0_two {v : Fin 6 → ZMod 2} (hv : ∑ i, v i = 0) :
    v ∈ lay d0 2 ↔ v 0 = v 2 ∧ v 1 = v 3 ∧ v 4 = v 5 := by
  rw [Fin.sum_univ_six] at hv
  exact (forall_congr' fun i => mem_lay_d0_one (sum_add_act (d0 i) v)).trans (lay_two_aux v hv)

private theorem lay_three_aux : ∀ v : Fin 6 → ZMod 2, v 0 + v 1 + v 2 + v 3 + v 4 + v 5 = 0 →
    ((∀ i, (v + act (d0 i) v) 0 = (v + act (d0 i) v) 2 ∧
        (v + act (d0 i) v) 1 = (v + act (d0 i) v) 3 ∧
        (v + act (d0 i) v) 4 = (v + act (d0 i) v) 5) ↔
      v 0 + v 1 + v 2 + v 3 = 0) := by
  decide +kernel

theorem mem_lay_d0_three {v : Fin 6 → ZMod 2} (hv : ∑ i, v i = 0) :
    v ∈ lay d0 3 ↔ v 0 + v 1 + v 2 + v 3 = 0 := by
  rw [Fin.sum_univ_six] at hv
  exact (forall_congr' fun i => mem_lay_d0_two (sum_add_act (d0 i) v)).trans
    (lay_three_aux v hv)

@[expose] def w1 : Fin 6 → ZMod 2 := ![1, 0, 0, 0, 1, 0]

theorem sum_w1 : ∑ i, w1 i = 0 := by
  rw [Fin.sum_univ_six]
  decide

theorem w1_not_mem_lay_three : w1 ∉ lay d0 3 := by
  rw [mem_lay_d0_three sum_w1]
  decide

private theorem flag_aux : ∀ i : Fin 8,
    (∀ w : Fin 6 → ZMod 2, w 0 + w 1 + w 2 + w 3 + w 4 + w 5 = 0 → w 0 + w 1 + w 2 + w 3 = 0 →
      w + act (d0 i) w = 0 ∨ w + act (d0 i) w = 1 ∨ w + act (d0 i) w = z0 ∨
        w + act (d0 i) w = z0 + 1) →
    i.val < 4 := by
  decide +kernel

theorem lt_four_of_flag {i : Fin 8}
    (h : ∀ w : Fin 6 → ZMod 2, ∑ j, w j = 0 → w ∈ lay d0 3 → w + act (d0 i) w ∈ lay d0 1) :
    i.val < 4 := by
  refine flag_aux i fun w hw hw3 => ?_
  have hw' : ∑ j, w j = 0 := by rw [Fin.sum_univ_six]; exact hw
  exact (mem_lay_d0_one (sum_add_act _ _)).mp (h w hw' ((mem_lay_d0_three hw').mpr hw3))

@[expose] def ConjU0 (t : Fin 6 → Fin 6) : Prop :=
  ∀ i : Fin 8, i.val < 4 → ∃ j : Fin 8, ∀ k : Fin 6, d0 j (t k) = t (d0 i k)

instance (t : Fin 6 → Fin 6) : Decidable (ConjU0 t) := by
  unfold ConjU0
  infer_instance

private theorem conj_aux : ∀ a : Fin 6, z0 a = 1 → ∀ b : Fin 6, z0 b = 1 → a ≠ b →
    ∀ c : Fin 6, z0 c = 1 → a ≠ c → b ≠ c → ∀ d : Fin 6, z0 d = 1 → a ≠ d → b ≠ d → c ≠ d →
    ∀ e : Fin 6, z0 e = 0 → ∀ f : Fin 6, z0 f = 0 → e ≠ f → ConjU0 ![a, b, c, d, e, f] := by
  decide +kernel

private theorem three_zero_aux : ∀ a b c : Fin 6, z0 a = 0 → z0 b = 0 → z0 c = 0 → a ≠ b →
    a ≠ c → b ≠ c → False := by
  decide +kernel

theorem conj_u0 (τ : Perm (Fin 6)) (hτ : act τ z0 = z0 ∨ act τ z0 = z0 + 1) {i : Fin 8}
    (hi : i.val < 4) : ∃ j, τ * d0 i * τ⁻¹ = d0 j := by
  have hval : ∀ k, act τ z0 (τ k) = z0 k := fun k => by simp
  have hne : ∀ {a b : Fin 6}, a ≠ b → τ a ≠ τ b := fun h h' => h (τ.injective h')
  rcases hτ with hτ | hτ
  · have hz : ∀ k, z0 (τ k) = z0 k := fun k => by rw [← hval k, hτ]
    obtain ⟨j, hj⟩ := conj_aux (τ 0) (hz 0) (τ 1) (hz 1) (hne (by decide)) (τ 2) (hz 2)
      (hne (by decide)) (hne (by decide)) (τ 3) (hz 3) (hne (by decide)) (hne (by decide))
      (hne (by decide)) (τ 4) (hz 4) (τ 5) (hz 5) (hne (by decide)) i hi
    have htv : ∀ k, (![τ 0, τ 1, τ 2, τ 3, τ 4, τ 5] : Fin 6 → Fin 6) k = τ k := by
      intro k
      fin_cases k <;> rfl
    refine ⟨j, Equiv.ext fun m => ?_⟩
    obtain ⟨k, rfl⟩ := τ.surjective m
    have := hj k
    rw [htv, htv] at this
    rw [Perm.mul_apply, Perm.mul_apply, show τ⁻¹ (τ k) = k from Perm.inv_eq_iff_eq.mpr rfl]
    exact this.symm
  · have hz : ∀ k, z0 (τ k) = z0 k + 1 := fun k => by
      rw [← hval k, hτ, Pi.add_apply, Pi.one_apply, add_assoc, CharTwo.add_self_eq_zero,
        add_zero]
    exact (three_zero_aux (τ 0) (τ 1) (τ 2) (by rw [hz]; decide) (by rw [hz]; decide)
      (by rw [hz]; decide) (hne (by decide)) (hne (by decide)) (hne (by decide))).elim

end CFSG.ComponentClassification.AS81.Sec2Nat
