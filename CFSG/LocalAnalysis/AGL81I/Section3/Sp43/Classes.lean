module

public import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.Closure
public import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.Gen

public section

namespace CFSG.Sp43

open CFSG.Sp43.Native Subgroup

theorem card_normalizer_sylow_eq {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p X) :
    Nat.card (normalizer (P : Set X)) = Nat.card (normalizer (Q : Set X)) := by
  have h1 := Subgroup.card_mul_index (normalizer (P : Set X))
  have h2 := Subgroup.card_mul_index (normalizer (Q : Set X))
  rw [← Sylow.card_eq_index_normalizer] at h1 h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

theorem genProp_map_conj {H : Subgroup G} (g : G) (h : GenProp H) :
    GenProp (H.map (MulAut.conj g).toMonoidHom) :=
  genProp_of_mulEquiv (H.equivMapOfInjective _ (MulAut.conj g).injective) h

private theorem ix_lt' (a : Fin 2 ⊕ Fin 2) : ix a < 4 := by
  rcases a with i | i <;> simp only [ix] <;> omega

theorem mem_normalizer_of_conj_mem {X : Type*} [Group X] [Finite X] {H : Subgroup X} {n : X}
    (h : ∀ k ∈ H, n * k * n⁻¹ ∈ H) : n ∈ normalizer (H : Set X) := by
  have := mem_normalizer_of_conj (s := (H : Set X)) (n := n) (by rw [Subgroup.closure_eq]; exact h)
  rwa [Subgroup.closure_eq] at this

def act (x : G) (w : Fin 2 ⊕ Fin 2 → ZMod 3) : Fin 2 ⊕ Fin 2 → ZMod 3 :=
  Matrix.mulVec (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) w

theorem act_mul (a b : G) (w : Fin 2 ⊕ Fin 2 → ZMod 3) : act (a * b) w = act a (act b w) := by
  simp only [act, MulMemClass.coe_mul, Matrix.mulVec_mulVec]

theorem act_one (w : Fin 2 ⊕ Fin 2 → ZMod 3) : act 1 w = w := by
  simp only [act, OneMemClass.coe_one, Matrix.one_mulVec]

theorem act_inv_act (a : G) (w : Fin 2 ⊕ Fin 2 → ZMod 3) : act a⁻¹ (act a w) = w := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (a : G) (w : Fin 2 ⊕ Fin 2 → ZMod 3) : act a (act a⁻¹ w) = w := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_neg (a : G) (w : Fin 2 ⊕ Fin 2 → ZMod 3) : act a (-w) = -act a w := by
  unfold act
  exact Matrix.mulVec_neg _ _

theorem act_zero (a : G) : act a 0 = 0 := by
  unfold act
  exact Matrix.mulVec_zero _

theorem eq_zero_of_act_eq_zero {a : G} {w : Fin 2 ⊕ Fin 2 → ZMod 3} (h : act a w = 0) : w = 0 := by
  rw [← act_inv_act a w, h, act_zero]

theorem act_ofCode {c : ℕ} (hc : Symp c) (v : ℕ) : act (ofCode c) (toV v) = toV (vecC c v) := by
  rw [act, coe_ofCode hc, toV_vecC]

def encV (w : Fin 2 ⊕ Fin 2 → ZMod 3) : ℕ := horner ((List.range 4).map fun k => (w (idx k)).val)

private theorem idx_ix' (a : Fin 2 ⊕ Fin 2) : idx (ix a) = a := by
  rcases a with ⟨i, hi⟩ | ⟨i, hi⟩ <;> interval_cases i <;> rfl

private theorem dig_horner_map4 (f : ℕ → ℕ) {k : ℕ} (hk : k < 4) :
    dig (horner ((List.range 4).map f)) k = f k % 3 := by
  rw [dig_horner, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp

theorem encV_lt (w : Fin 2 ⊕ Fin 2 → ZMod 3) : encV w < 81 :=
  lt_of_lt_of_eq (horner_lt _) (by simp)

theorem toV_encV (w : Fin 2 ⊕ Fin 2 → ZMod 3) : toV (encV w) = w := by
  funext a
  simp only [toV, encV]
  rw [dig_horner_map4 _ (ix_lt' a), idx_ix', Nat.mod_eq_of_lt (ZMod.val_lt _),
    ZMod.natCast_zmod_val]

theorem toV_negV (v : ℕ) : toV (negV v) = -toV v := by
  funext a
  simp only [toV, negV, Pi.neg_apply]
  rw [dig_horner_map4 _ (ix_lt' a), ZMod.natCast_mod, Nat.cast_mul,
    show ((2 : ℕ) : ZMod 3) = -1 by decide, neg_one_mul]

theorem negV_lt (v : ℕ) : negV v < 81 := lt_of_lt_of_eq (horner_lt _) (by simp)

theorem toV_zero : toV 0 = 0 := by
  funext a
  simp [toV, dig]

theorem mem_smul_sylow_iff {X : Type*} [Group X] {p : ℕ} (g : X) (S : Sylow p X) (x : X) :
    x ∈ ((g • S : Sylow p X) : Subgroup X) ↔ g⁻¹ * x * g ∈ (S : Subgroup X) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

end CFSG.Sp43
