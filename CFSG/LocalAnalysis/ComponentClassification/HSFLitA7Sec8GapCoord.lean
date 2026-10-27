module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MBFacts

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

namespace MB

@[expose] def c : MB := t * v

@[expose] def coord (a : Fin 3 → ZMod 4) : MB := w₁ ^ (a 0).val * w₂ ^ (a 1).val * c ^ (a 2).val

theorem w₁_pow_four : w₁ ^ 4 = 1 := by decide +kernel
theorem w₂_pow_four : w₂ ^ 4 = 1 := by decide +kernel
theorem c_pow_four : c ^ 4 = 1 := by decide +kernel
theorem w₁_comm_w₂ : Commute w₁ w₂ := by unfold Commute SemiconjBy; decide +kernel
theorem w₁_comm_c : Commute w₁ c := by unfold Commute SemiconjBy; decide +kernel
theorem w₂_comm_c : Commute w₂ c := by unfold Commute SemiconjBy; decide +kernel

theorem pow_val_add {g : MB} (hg : g ^ 4 = 1) (x y : ZMod 4) :
    g ^ (x + y).val = g ^ x.val * g ^ y.val := by
  rw [← pow_add, ZMod.val_add, ← Nat.mod_add_div (x.val + y.val) 4, pow_add, pow_mul, hg, one_pow,
    mul_one, Nat.mod_add_div]

theorem coord_add (a b : Fin 3 → ZMod 4) : coord (a + b) = coord a * coord b := by
  simp only [coord, Pi.add_apply, pow_val_add w₁_pow_four, pow_val_add w₂_pow_four,
    pow_val_add c_pow_four]
  have h12 : Commute (w₁ ^ (b 0).val) (w₂ ^ (a 1).val) := w₁_comm_w₂.pow_pow _ _
  have h1c : Commute (w₁ ^ (b 0).val) (c ^ (a 2).val) := w₁_comm_c.pow_pow _ _
  have h2c : Commute (w₂ ^ (b 1).val) (c ^ (a 2).val) := w₂_comm_c.pow_pow _ _
  calc w₁ ^ (a 0).val * w₁ ^ (b 0).val * (w₂ ^ (a 1).val * w₂ ^ (b 1).val) *
        (c ^ (a 2).val * c ^ (b 2).val)
      = w₁ ^ (a 0).val * (w₁ ^ (b 0).val * w₂ ^ (a 1).val) * w₂ ^ (b 1).val *
        (c ^ (a 2).val * c ^ (b 2).val) := by group
    _ = w₁ ^ (a 0).val * (w₂ ^ (a 1).val * w₁ ^ (b 0).val) * w₂ ^ (b 1).val *
        (c ^ (a 2).val * c ^ (b 2).val) := by rw [h12.eq]
    _ = w₁ ^ (a 0).val * w₂ ^ (a 1).val * (w₁ ^ (b 0).val * (w₂ ^ (b 1).val * c ^ (a 2).val)) *
        c ^ (b 2).val := by group
    _ = w₁ ^ (a 0).val * w₂ ^ (a 1).val * (w₁ ^ (b 0).val * (c ^ (a 2).val * w₂ ^ (b 1).val)) *
        c ^ (b 2).val := by rw [h2c.eq]
    _ = w₁ ^ (a 0).val * w₂ ^ (a 1).val * ((w₁ ^ (b 0).val * c ^ (a 2).val) * w₂ ^ (b 1).val) *
        c ^ (b 2).val := by group
    _ = w₁ ^ (a 0).val * w₂ ^ (a 1).val * ((c ^ (a 2).val * w₁ ^ (b 0).val) * w₂ ^ (b 1).val) *
        c ^ (b 2).val := by rw [h1c.eq]
    _ = w₁ ^ (a 0).val * w₂ ^ (a 1).val * c ^ (a 2).val *
        (w₁ ^ (b 0).val * w₂ ^ (b 1).val * c ^ (b 2).val) := by group

theorem coord_zero : coord 0 = 1 := by
  simp [coord]

theorem coord_neg (a : Fin 3 → ZMod 4) : coord (-a) = (coord a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← coord_add, neg_add_cancel, coord_zero]

theorem coord_sub (a b : Fin 3 → ZMod 4) : coord (a - b) = coord a * (coord b)⁻¹ := by
  rw [sub_eq_add_neg, coord_add, coord_neg]

theorem coord_nsmul (n : ℕ) (a : Fin 3 → ZMod 4) : coord (n • a) = coord a ^ n := by
  induction n with
  | zero => rw [zero_nsmul, coord_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, coord_add, ih, pow_succ]

theorem vec_eta (a : Fin 3 → ZMod 4) : a = ![a 0, a 1, a 2] := by
  ext i; fin_cases i <;> rfl

theorem coord_eq_one_aux : ∀ x y w : ZMod 4, coord ![x, y, w] = 1 → ![x, y, w] = 0 := by
  decide +kernel

theorem coord_eq_one {a : Fin 3 → ZMod 4} (h : coord a = 1) : a = 0 := by
  rw [vec_eta a] at h ⊢
  exact coord_eq_one_aux _ _ _ h

theorem coord_injective : Function.Injective coord := by
  intro a b h
  have : coord (a - b) = 1 := by rw [coord_sub, h, mul_inv_cancel]
  exact sub_eq_zero.mp (coord_eq_one this)

theorem inQC_coord_aux : ∀ x y w : ZMod 4, inQC (coord ![x, y, w]) = true := by
  decide +kernel

theorem inQC_coord (a : Fin 3 → ZMod 4) : inQC (coord a) = true := by
  rw [vec_eta a]; exact inQC_coord_aux _ _ _

@[expose] def QC : Subgroup MB := ofPred inQC (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem card_QC : Nat.card QC = 64 := by
  rw [QC, card_ofPred]; decide +kernel

theorem exists_coord {x : MB} (hx : inQC x = true) : ∃ a, coord a = x := by
  classical
  let f : (Fin 3 → ZMod 4) → QC := fun a => ⟨coord a, inQC_coord a⟩
  have hf : Function.Injective f := fun a b h => coord_injective (congrArg Subtype.val h)
  have hcard : Nat.card QC ≤ Nat.card (Fin 3 → ZMod 4) := by
    rw [card_QC, Nat.card_eq_fintype_card]; decide
  have hsurj : Function.Surjective f :=
    (Function.Injective.bijective_of_nat_card_le hf hcard).2
  obtain ⟨a, ha⟩ := hsurj ⟨x, hx⟩
  exact ⟨a, congrArg Subtype.val ha⟩

theorem coord_e0 : coord ![1, 0, 0] = w₁ := by decide +kernel
theorem coord_e1 : coord ![0, 1, 0] = w₂ := by decide +kernel
theorem coord_e2 : coord ![0, 0, 1] = c := by decide +kernel
theorem coord_z : coord ![2, 0, 0] = z := by decide +kernel
theorem coord_y : coord ![0, 2, 0] = y := by decide +kernel
theorem coord_k : coord ![0, 0, 2] = k := by decide +kernel

@[expose] def uvec (a : Fin 3 → ZMod 4) : Fin 3 → ZMod 4 := ![a 1 - a 0, a 1, a 2]

theorem t_conj_coord_aux : ∀ x y w : ZMod 4, t * coord ![x, y, w] * t⁻¹ = coord (-![x, y, w]) := by
  decide +kernel

theorem t_conj_coord (a : Fin 3 → ZMod 4) : t * coord a * t⁻¹ = coord (-a) := by
  rw [vec_eta a]; exact t_conj_coord_aux _ _ _

theorem u_conj_coord_aux : ∀ x y w : ZMod 4,
    u * coord ![x, y, w] * u⁻¹ = coord (uvec ![x, y, w]) := by
  decide +kernel

theorem u_conj_coord (a : Fin 3 → ZMod 4) : u * coord a * u⁻¹ = coord (uvec a) := by
  rw [vec_eta a]; exact u_conj_coord_aux _ _ _

end MB

end Sec8

end CFSG.ComponentClassification.HSFLit
