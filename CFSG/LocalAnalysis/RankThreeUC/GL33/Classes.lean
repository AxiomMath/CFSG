module

public import CFSG.LocalAnalysis.RankThreeUC.GL33.Closure
import Mathlib.Algebra.Field.ZMod
public import CFSG.LocalAnalysis.RankThreeUC.GL33.Group
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GL33

open CFSG.GL33.Native Subgroup
open scoped Matrix

abbrev V := Fin 3 → ZMod 3

@[expose] def act (x : G) (v : V) : V := Matrix.mulVec (x : Matrix (Fin 3) (Fin 3) (ZMod 3)) v

theorem act_mul (a b : G) (v : V) : act (a * b) v = act a (act b v) := by
  simp only [act, Units.val_mul, Matrix.mulVec_mulVec]

theorem act_one (v : V) : act 1 v = v := by
  simp only [act, Units.val_one, Matrix.one_mulVec]

theorem act_inv_act (a : G) (v : V) : act a⁻¹ (act a v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (a : G) (v : V) : act a (act a⁻¹ v) = v := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_add (a : G) (v w : V) : act a (v + w) = act a v + act a w := by
  unfold act
  exact Matrix.mulVec_add _ _ _

theorem act_sub (a : G) (v w : V) : act a (v - w) = act a v - act a w := by
  unfold act
  exact Matrix.mulVec_sub _ _ _

theorem act_zero (a : G) : act a 0 = 0 := by
  unfold act
  exact Matrix.mulVec_zero _

theorem act_neg (a : G) (v : V) : act a (-v) = -act a v := by
  unfold act
  exact Matrix.mulVec_neg _ _

theorem act_smul (a : G) (c : ZMod 3) (v : V) : act a (c • v) = c • act a v := by
  unfold act
  exact Matrix.mulVec_smul _ _ _

theorem act_injective (a : G) : Function.Injective (act a) := fun v w h => by
  rw [← act_inv_act a v, h, act_inv_act]

theorem act_ofCode {c : ℕ} (hc : Good c) (v : ℕ) : act (ofCode c) (toV v) = toV (vecC c v) := by
  rw [act, coe_ofCode hc, toV_vecC]

@[expose] def actHom (x : G) : V →+ V where
  toFun := act x
  map_zero' := act_zero x
  map_add' := act_add x

theorem eq_one_of_act {x : G} (h : ∀ v, act x v = v) : x = 1 := by
  apply Units.ext
  rw [Units.val_one]
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simp only [act, Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [this, Matrix.one_apply, Pi.single_apply]

@[expose] def Irr (W : Subgroup G) : Prop :=
  ∀ B : AddSubgroup V, (∀ w ∈ W, ∀ b ∈ B, act w b ∈ B) → B = ⊥ ∨ B = ⊤

@[expose] def fixA (X : Subgroup G) : AddSubgroup V where
  carrier := {v | ∀ x ∈ X, act x v = v}
  zero_mem' := fun x _ => act_zero x
  add_mem' {v w} hv hw x hx := by
    simp only [Set.mem_setOf_eq] at *
    rw [act_add, hv x hx, hw x hx]
  neg_mem' {v} hv x hx := by
    simp only [Set.mem_setOf_eq] at *
    rw [act_neg, hv x hx]

@[expose] def comA (X : Subgroup G) : AddSubgroup V :=
  AddSubgroup.closure {u | ∃ x ∈ X, ∃ v, u = act x v - v}

@[expose] def Normalizes (W X : Subgroup G) : Prop := ∀ w ∈ W, ∀ x ∈ X, w⁻¹ * x * w ∈ X

theorem fixA_inv {W X : Subgroup G} (hN : Normalizes W X) :
    ∀ w ∈ W, ∀ b ∈ fixA X, act w b ∈ fixA X := by
  intro w hw b hb x hx
  have e : x * w = w * (w⁻¹ * x * w) := by group
  rw [← act_mul, e, act_mul, hb _ (hN w hw x hx)]

theorem comA_inv {W X : Subgroup G} (hN : Normalizes W X) (hW : ∀ w ∈ W, w⁻¹ ∈ W) :
    ∀ w ∈ W, ∀ b ∈ comA X, act w b ∈ comA X := by
  intro w hw b hb
  induction hb using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨x, hx, v, rfl⟩ := hu
    apply AddSubgroup.subset_closure
    refine ⟨w * x * w⁻¹, ?_, act w v, ?_⟩
    · have := hN w⁻¹ (hW w hw) x hx
      simpa [mul_assoc] using this
    · rw [act_sub, ← act_mul, ← act_mul, show w * x * w⁻¹ * w = w * x by group]
  | zero => rw [act_zero]; exact AddSubgroup.zero_mem _
  | add u v _ _ hu hv => rw [act_add]; exact AddSubgroup.add_mem _ hu hv
  | neg u _ hu =>
    rw [act_neg]
    exact AddSubgroup.neg_mem _ hu

theorem eq_bot_of_fixA {X : Subgroup G} (h : fixA X = ⊤) : X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact eq_one_of_act fun v => (h ▸ AddSubgroup.mem_top v : v ∈ fixA X) x hx

theorem eq_bot_of_comA {X : Subgroup G} (h : comA X = ⊥) : X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  refine eq_one_of_act fun v => ?_
  have hm : act x v - v ∈ comA X := AddSubgroup.subset_closure ⟨x, hx, v, rfl⟩
  rw [h, AddSubgroup.mem_bot, sub_eq_zero] at hm
  exact hm

theorem fixA_comA_of_irr {W X : Subgroup G} (hW : Irr W) (hN : Normalizes W X) (hX : X ≠ ⊥) :
    fixA X = ⊥ ∧ comA X = ⊤ := by
  refine ⟨?_, ?_⟩
  · rcases hW (fixA X) (fixA_inv hN) with h | h
    · exact h
    · exact absurd (eq_bot_of_fixA h) hX
  · rcases hW (comA X) (comA_inv hN fun w hw => W.inv_mem hw) with h | h
    · exact absurd (eq_bot_of_comA h) hX
    · exact h

theorem three_nsmul_V (v : V) : 3 • v = 0 := by
  funext t
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  rw [show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]

@[expose] def fixer (w : V) : Subgroup G where
  carrier := {x | act x w = w}
  one_mem' := act_one w
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [act_mul, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    calc act a⁻¹ w = act a⁻¹ (act a w) := by rw [ha]
      _ = w := act_inv_act a w

@[expose] def cofixer (f : V) : Subgroup G where
  carrier := {x | f ᵥ* (x : Matrix (Fin 3) (Fin 3) (ZMod 3)) = f}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul] at *
    rw [← Matrix.vecMul_vecMul, ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    calc f ᵥ* ((a⁻¹ : G) : Matrix (Fin 3) (Fin 3) (ZMod 3))
        = (f ᵥ* (a : Matrix (Fin 3) (Fin 3) (ZMod 3))) ᵥ* ((a⁻¹ : G) : Matrix _ _ _) := by
          rw [ha]
      _ = f := by rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.vecMul_one]

@[expose] def lineStab (w : V) : Subgroup G where
  carrier := {x | act x w = w ∨ act x w = -w}
  one_mem' := Or.inl (act_one w)
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rcases hb with hb | hb <;> rcases ha with ha | ha <;>
      simp [act_mul, hb, ha, act_neg]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    rcases ha with ha | ha
    · left
      calc act a⁻¹ w = act a⁻¹ (act a w) := by rw [ha]
        _ = w := act_inv_act a w
    · right
      calc act a⁻¹ w = act a⁻¹ (-(act a w)) := by rw [ha, neg_neg]
        _ = -w := by rw [act_neg, act_inv_act]

theorem closure_le_of_gens {K : Subgroup G} {a b : ℕ} (ha : ofCode a ∈ K) (hb : ofCode b ∈ K) :
    sub2 a b ≤ K := by
  rw [sub2, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ha
  · exact hb

theorem toV_ne_zero {v : ℕ} (h0 : v ≠ 0) (h : v < 27) : toV v ≠ 0 := by
  intro e
  exact h0 (eq_of_toV_eq h (by norm_num) (by rw [e, toV_zero]))

private theorem conj_mem_map {M : Subgroup G} {g x : G} (hx : x ∈ M) :
    g * x * g⁻¹ ∈ M.map (MulAut.conj g).toMonoidHom :=
  ⟨x, hx, by simp⟩

private theorem mem_map_conj {M : Subgroup G} {g y : G}
    (hy : y ∈ M.map (MulAut.conj g).toMonoidHom) : g⁻¹ * y * g ∈ M := by
  obtain ⟨x, hx, rfl⟩ := hy
  simpa [mul_assoc] using hx

theorem mem_normalizer_of_conj_mem {X : Type*} [Group X] [Finite X] {H : Subgroup X} {n : X}
    (h : ∀ k ∈ H, n * k * n⁻¹ ∈ H) : n ∈ normalizer (H : Set X) := by
  have := mem_normalizer_of_conj (s := (H : Set X)) (n := n) (by rw [Subgroup.closure_eq]; exact h)
  rwa [Subgroup.closure_eq] at this

theorem conj_mem_normalizer {W M : Subgroup G} {g : G}
    (hN : Normalizes W (M.map (MulAut.conj g).toMonoidHom)) {w : G} (hw : w ∈ W) :
    g⁻¹ * w * g ∈ normalizer (M : Set G) := by
  have h1 : g⁻¹ * w⁻¹ * g ∈ normalizer (M : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro k hk
    have := mem_map_conj (hN w hw _ (conj_mem_map (g := g) hk))
    have e : g⁻¹ * w⁻¹ * g * k * (g⁻¹ * w⁻¹ * g)⁻¹ = g⁻¹ * (w⁻¹ * (g * k * g⁻¹) * w) * g := by
      group
    rw [e]
    exact this
  have := (normalizer (M : Set G)).inv_mem h1
  simpa [mul_assoc] using this

theorem act_single_of_monoC {c : ℕ} (hc : Good c) (hm : monoC c = true) (j : Fin 3) :
    ∃ i : Fin 3, act (ofCode c) (Pi.single j 1) ∈ AddSubgroup.zmultiples (Pi.single i 1 : V) := by
  unfold monoC at hm
  rw [List.all_eq_true] at hm
  have hj := hm j (List.mem_range.2 j.2)
  rw [beq_iff_eq, List.length_eq_one_iff] at hj
  obtain ⟨i₀, hi₀⟩ := hj
  have hmem : ∀ i < 3, ent c i j ≠ 0 ↔ i = i₀ := by
    intro i hi
    have := congrArg (fun l => i ∈ l) hi₀
    simp only [List.mem_filter, List.mem_range, bne_iff_ne, ne_eq, List.mem_singleton,
      eq_iff_iff] at this
    rw [← this]
    simp [hi]
  have hi₀3 : i₀ < 3 := by
    have := congrArg (fun l => i₀ ∈ l) hi₀
    simp only [List.mem_filter, List.mem_range, List.mem_singleton, eq_iff_iff, iff_true] at this
    exact this.1
  refine ⟨⟨i₀, hi₀3⟩, AddSubgroup.mem_zmultiples_iff.2 ⟨(ent c i₀ j : ℤ), ?_⟩⟩
  funext i
  rw [act, coe_ofCode hc, Matrix.mulVec_single_one]
  simp only [Pi.smul_apply, Pi.single_apply, Matrix.col_apply, toM, zsmul_eq_mul, mul_ite,
    mul_one, mul_zero]
  by_cases h : (i : ℕ) = i₀
  · have hi : i = ⟨i₀, hi₀3⟩ := Fin.ext h
    subst hi
    simp
  · have hi : i ≠ ⟨i₀, hi₀3⟩ := fun e => h (congrArg Fin.val e)
    rw [if_neg hi]
    have := (hmem i i.2).not.2 h
    push Not at this
    rw [this, Nat.cast_zero]

theorem card_zmultiples_V {v : V} (hv : v ≠ 0) : Nat.card (AddSubgroup.zmultiples v) = 3 := by
  rw [Nat.card_zmultiples]
  exact addOrderOf_eq_prime (three_nsmul_V v) hv

theorem card_top_V : Nat.card (⊤ : AddSubgroup V) = 27 := by
  rw [AddSubgroup.card_top, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

end CFSG.GL33

end
