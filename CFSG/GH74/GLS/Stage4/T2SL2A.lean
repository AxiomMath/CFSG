module

public import CFSG.GH74.GLS.Stage4.T2SL2Defs
public import Mathlib.Order.CompletePartialOrder

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Rest.T2

open CFSG.GH74.GLS.Stage4.Hex Subgroup

variable {F : Type} [Field F]

theorem t2A_ext {A B : SL2 F}
    (h00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = (B : Matrix (Fin 2) (Fin 2) F) 0 0)
    (h01 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = (B : Matrix (Fin 2) (Fin 2) F) 0 1)
    (h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = (B : Matrix (Fin 2) (Fin 2) F) 1 0)
    (h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (B : Matrix (Fin 2) (Fin 2) F) 1 1) : A = B := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem t2A_det (x : SL2 F) :
    (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (x : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  have h := x.2
  rwa [Matrix.det_fin_two] at h

theorem sl2D_mul (a b : Fˣ) : sl2D a * sl2D b = (sl2D (a * b) : SL2 F) := by
  apply t2A_ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem sl2D_one : (sl2D (1 : Fˣ) : SL2 F) = 1 := by
  apply t2A_ext <;> simp

theorem sl2D_neg_one : (sl2D (-1 : Fˣ) : SL2 F) = negOne F := by
  apply t2A_ext <;> simp

theorem t2A_sl2D_inv (t : Fˣ) : (sl2D t : SL2 F)⁻¹ = sl2D t⁻¹ := by
  apply t2A_ext <;> simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem t2A_conj_U (t : Fˣ) (c : F) :
    (sl2D t : SL2 F) * sl2U c * (sl2D t : SL2 F)⁻¹ = sl2U ((t : F) ^ 2 * c) := by
  rw [t2A_sl2D_inv]
  apply t2A_ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem t2A_conj_L (t : Fˣ) (c : F) :
    (sl2D t : SL2 F) * sl2L c * (sl2D t : SL2 F)⁻¹ = sl2L (((t⁻¹ : Fˣ) : F) ^ 2 * c) := by
  rw [t2A_sl2D_inv]
  apply t2A_ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem t2A_W_conj_U (c : F) : sl2W F * sl2U c * (sl2W F)⁻¹ = sl2L (-c) := by
  apply t2A_ext <;>
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem t2A_W_conj_L (c : F) : sl2W F * sl2L c * (sl2W F)⁻¹ = sl2U (-c) := by
  apply t2A_ext <;>
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem t2A_W_conj_D (t : Fˣ) : sl2W F * sl2D t * (sl2W F)⁻¹ = sl2D t⁻¹ := by
  apply t2A_ext <;>
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem t2A_sl2U_pow (c : F) (n : ℕ) : (sl2U c : SL2 F) ^ n = sl2U ((n : F) * c) := by
  induction n with
  | zero => simp [sl2U_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← sl2U_add]
    congr 1
    push_cast
    ring

theorem t2A_sl2L_pow (c : F) (n : ℕ) : (sl2L c : SL2 F) ^ n = sl2L ((n : F) * c) := by
  induction n with
  | zero => simp [sl2L_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← sl2L_add]
    congr 1
    push_cast
    ring

theorem mem_uSub {x : SL2 F} : x ∈ uSub F ↔ ∃ c : F, x = sl2U c := by
  constructor
  · rintro ⟨h00, h11, h10⟩
    refine ⟨(x : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
    apply t2A_ext <;> simp [h00, h11, h10]
  · rintro ⟨c, rfl⟩
    exact ⟨by simp, by simp, by simp⟩

theorem mem_lSub {x : SL2 F} : x ∈ lSub F ↔ ∃ c : F, x = sl2L c := by
  constructor
  · rintro ⟨h00, h11, h01⟩
    refine ⟨(x : Matrix (Fin 2) (Fin 2) F) 1 0, ?_⟩
    apply t2A_ext <;> simp [h00, h11, h01]
  · rintro ⟨c, rfl⟩
    exact ⟨by simp, by simp, by simp⟩

theorem mem_tSub {x : SL2 F} : x ∈ tSub F ↔ ∃ t : Fˣ, x = sl2D t := by
  constructor
  · rintro ⟨h01, h10⟩
    have hdet := t2A_det x
    rw [h01, h10] at hdet
    have hu : (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      simpa using hdet
    refine ⟨⟨(x : Matrix (Fin 2) (Fin 2) F) 0 0, (x : Matrix (Fin 2) (Fin 2) F) 1 1, hu,
      by rw [mul_comm]; exact hu⟩, ?_⟩
    apply t2A_ext <;> simp [h01, h10]
  · rintro ⟨t, rfl⟩
    exact ⟨by simp, by simp⟩

theorem sl2U_mem_uSub (c : F) : sl2U c ∈ uSub F := mem_uSub.2 ⟨c, rfl⟩

theorem sl2L_mem_lSub (c : F) : sl2L c ∈ lSub F := mem_lSub.2 ⟨c, rfl⟩

theorem sl2D_mem_tSub (t : Fˣ) : sl2D t ∈ tSub F := mem_tSub.2 ⟨t, rfl⟩

theorem negOne_mem_tSub : negOne F ∈ tSub F := ⟨by simp, by simp⟩

theorem negOne_mul_self : negOne F * negOne F = 1 := by
  apply t2A_ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem negOne_central (x : SL2 F) : negOne F * x = x * negOne F := by
  apply t2A_ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem negOne_ne_one (h2 : (2 : F) ≠ 0) : negOne F ≠ 1 := by
  intro h
  have h00 : (-1 : F) = 1 := by
    have := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simpa using this
  apply h2
  linear_combination (-1 : F) * h00

theorem uSub_comm : ∀ x ∈ uSub F, ∀ y ∈ uSub F, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := mem_uSub.1 hx
  obtain ⟨b, rfl⟩ := mem_uSub.1 hy
  rw [← sl2U_add, ← sl2U_add, add_comm]

theorem lSub_comm : ∀ x ∈ lSub F, ∀ y ∈ lSub F, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := mem_lSub.1 hx
  obtain ⟨b, rfl⟩ := mem_lSub.1 hy
  rw [← sl2L_add, ← sl2L_add, add_comm]

theorem tSub_comm : ∀ x ∈ tSub F, ∀ y ∈ tSub F, x * y = y * x := by
  intro x hx y hy
  obtain ⟨s, rfl⟩ := mem_tSub.1 hx
  obtain ⟨t, rfl⟩ := mem_tSub.1 hy
  rw [sl2D_mul, sl2D_mul, mul_comm]

theorem card_uSub [Finite F] : Nat.card (uSub F) = Nat.card F := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun c : F => (⟨sl2U c, sl2U_mem_uSub c⟩ : uSub F)) ⟨?_, ?_⟩
  · intro a b h
    exact sl2U_injective (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := mem_uSub.1 hx
    exact ⟨c, rfl⟩

theorem card_lSub [Finite F] : Nat.card (lSub F) = Nat.card F := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun c : F => (⟨sl2L c, sl2L_mem_lSub c⟩ : lSub F)) ⟨?_, ?_⟩
  · intro a b h
    exact sl2L_injective (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := mem_lSub.1 hx
    exact ⟨c, rfl⟩

theorem t2A_sl2D_injective : Function.Injective (sl2D : Fˣ → SL2 F) := by
  intro s t h
  have := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
  exact Units.ext (by simpa using this)

@[expose] def t2A_dHom (F : Type) [Field F] : Fˣ →* tSub F where
  toFun t := ⟨sl2D t, sl2D_mem_tSub t⟩
  map_one' := Subtype.ext sl2D_one
  map_mul' s t := Subtype.ext (sl2D_mul s t).symm

theorem t2A_dHom_bijective : Function.Bijective (t2A_dHom F) := by
  refine ⟨?_, ?_⟩
  · intro s t h
    exact t2A_sl2D_injective (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    obtain ⟨t, rfl⟩ := mem_tSub.1 hx
    exact ⟨t, rfl⟩

theorem card_tSub [Finite F] : Nat.card (tSub F) = Nat.card F - 1 := by
  rw [← Nat.card_units]
  exact (Nat.card_congr (Equiv.ofBijective (t2A_dHom F) t2A_dHom_bijective)).symm

theorem isCyclic_tSub [Finite F] : IsCyclic (tSub F) :=
  isCyclic_of_surjective (t2A_dHom F) t2A_dHom_bijective.2

theorem pow_char_uSub (p : ℕ) [CharP F p] : ∀ x ∈ uSub F, x ^ p = 1 := by
  intro x hx
  obtain ⟨c, rfl⟩ := mem_uSub.1 hx
  rw [t2A_sl2U_pow, CharP.cast_eq_zero, zero_mul, sl2U_zero]

theorem pow_char_lSub (p : ℕ) [CharP F p] : ∀ x ∈ lSub F, x ^ p = 1 := by
  intro x hx
  obtain ⟨c, rfl⟩ := mem_lSub.1 hx
  rw [t2A_sl2L_pow, CharP.cast_eq_zero, zero_mul, sl2L_zero]

theorem tSub_normalizes_uSub : ∀ h ∈ tSub F, ∀ x ∈ uSub F, h * x * h⁻¹ ∈ uSub F := by
  intro h hh x hx
  obtain ⟨t, rfl⟩ := mem_tSub.1 hh
  obtain ⟨c, rfl⟩ := mem_uSub.1 hx
  rw [t2A_conj_U]
  exact sl2U_mem_uSub _

theorem tSub_normalizes_lSub : ∀ h ∈ tSub F, ∀ x ∈ lSub F, h * x * h⁻¹ ∈ lSub F := by
  intro h hh x hx
  obtain ⟨t, rfl⟩ := mem_tSub.1 hh
  obtain ⟨c, rfl⟩ := mem_lSub.1 hx
  rw [t2A_conj_L]
  exact sl2L_mem_lSub _

theorem t2A_sq_eq_one {t : Fˣ} (ht : (t : F) ^ 2 = 1) (h1 : (sl2D t : SL2 F) ≠ 1)
    (hn : (sl2D t : SL2 F) ≠ negOne F) : False := by
  have hmul : (t : F) * (t : F) = 1 := by rw [← sq]; exact ht
  rcases mul_self_eq_one_iff.1 hmul with h | h
  · apply h1
    have : t = 1 := Units.ext h
    rw [this, sl2D_one]
  · apply hn
    apply t2A_ext <;> simp [h]

theorem tSub_fpf_uSub : ∀ h ∈ tSub F, h ≠ 1 → h ≠ negOne F → ∀ x ∈ uSub F,
    h * x * h⁻¹ = x → x = 1 := by
  intro h hh h1 hn x hx hfix
  obtain ⟨t, rfl⟩ := mem_tSub.1 hh
  obtain ⟨c, rfl⟩ := mem_uSub.1 hx
  rw [t2A_conj_U] at hfix
  have hc : (t : F) ^ 2 * c = c := sl2U_injective hfix
  by_cases hc0 : c = 0
  · rw [hc0, sl2U_zero]
  · exact (t2A_sq_eq_one (mul_right_cancel₀ hc0 (hc.trans (one_mul c).symm)) h1 hn).elim

theorem tSub_fpf_lSub : ∀ h ∈ tSub F, h ≠ 1 → h ≠ negOne F → ∀ x ∈ lSub F,
    h * x * h⁻¹ = x → x = 1 := by
  intro h hh h1 hn x hx hfix
  obtain ⟨t, rfl⟩ := mem_tSub.1 hh
  obtain ⟨c, rfl⟩ := mem_lSub.1 hx
  rw [t2A_conj_L] at hfix
  have hc : ((t⁻¹ : Fˣ) : F) ^ 2 * c = c := sl2L_injective hfix
  by_cases hc0 : c = 0
  · rw [hc0, sl2L_zero]
  · have hsq : ((t⁻¹ : Fˣ) : F) ^ 2 = 1 := mul_right_cancel₀ hc0 (hc.trans (one_mul c).symm)
    refine (t2A_sq_eq_one (t := t⁻¹) hsq ?_ ?_).elim
    · rw [← t2A_sl2D_inv]
      intro h'
      exact h1 (inv_eq_one.1 h')
    · rw [← t2A_sl2D_inv]
      intro h'
      exact hn ((inv_eq_iff_eq_inv.1 h').trans (inv_eq_of_mul_eq_one_right negOne_mul_self))

theorem uSub_inf_lSub : uSub F ⊓ lSub F = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨h00, h11, h10⟩, -, -, h01⟩
  rw [Subgroup.mem_bot]
  apply t2A_ext <;> simp [h00, h11, h10, h01]

theorem uSub_ne_lSub : uSub F ≠ lSub F := by
  intro h
  have h1 : (sl2U (1 : F) : SL2 F) ∈ lSub F := h ▸ sl2U_mem_uSub 1
  have := h1.2.2
  simp at this

theorem uSub_sup_lSub : uSub F ⊔ lSub F = ⊤ := by
  rw [eq_top_iff]
  intro A _
  have hU : ∀ c, (sl2U c : SL2 F) ∈ uSub F ⊔ lSub F := fun c =>
    Subgroup.mem_sup_left (sl2U_mem_uSub c)
  have hL : ∀ c, (sl2L c : SL2 F) ∈ uSub F ⊔ lSub F := fun c =>
    Subgroup.mem_sup_right (sl2L_mem_lSub c)
  have key : ∀ B : SL2 F, (B : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → B ∈ uSub F ⊔ lSub F := by
    intro B hc
    have hB : B = sl2U (((B : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) / (B : Matrix (Fin 2) (Fin 2) F) 1 0) *
        sl2L ((B : Matrix (Fin 2) (Fin 2) F) 1 0) *
        sl2U (((B : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) / (B : Matrix (Fin 2) (Fin 2) F) 1 0) := by
      have h := t2A_det B
      apply t2A_ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
        first | ring1 | linear_combination h | linear_combination -h
    rw [hB]
    exact mul_mem (mul_mem (hU _) (hL _)) (hU _)
  by_cases hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have h00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h
      have := t2A_det A
      rw [h, hc] at this
      simp at this
    have hLA : ((sl2L 1 * A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, hc, h00]
    have e : A = (sl2L 1)⁻¹ * (sl2L 1 * A) := by group
    rw [e]
    exact mul_mem (inv_mem (hL 1)) (key _ hLA)
  · exact key A hc

theorem sl2W_sq : sl2W F * sl2W F = negOne F := by
  apply t2A_ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2W_conj_uSub : ∀ x ∈ uSub F, sl2W F * x * (sl2W F)⁻¹ ∈ lSub F := by
  intro x hx
  obtain ⟨c, rfl⟩ := mem_uSub.1 hx
  rw [t2A_W_conj_U]
  exact sl2L_mem_lSub _

theorem sl2W_conj_lSub : ∀ x ∈ lSub F, sl2W F * x * (sl2W F)⁻¹ ∈ uSub F := by
  intro x hx
  obtain ⟨c, rfl⟩ := mem_lSub.1 hx
  rw [t2A_W_conj_L]
  exact sl2U_mem_uSub _

theorem sl2W_inv_tSub : ∀ h ∈ tSub F, sl2W F * h * (sl2W F)⁻¹ = h⁻¹ := by
  intro h hh
  obtain ⟨t, rfl⟩ := mem_tSub.1 hh
  rw [t2A_W_conj_D, t2A_sl2D_inv]

end CFSG.GH74.GLS.Stage4.Rest.T2
