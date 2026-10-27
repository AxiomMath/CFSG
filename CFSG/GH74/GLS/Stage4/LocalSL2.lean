module

public import CFSG.GH74.GLS.Stage4.HexSL2Defs
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GH74.GLS.IVK.L2.BorelMatrices

public section

namespace CFSG.GH74.GLS.Stage4.SL2

open Subgroup Matrix CFSG.GH74.GLS.Stage4.Hex CFSG.SL2MinimalFaithful CFSG.GH74.GLS.IVK.L2Borel
open scoped MatrixGroups Pointwise

variable {F : Type} [Field F]

@[expose] def upperHom (F : Type) [Field F] : Multiplicative F →* SL2 F where
  toFun t := sl2U t.toAdd
  map_one' := sl2U_zero
  map_mul' s t := sl2U_add s.toAdd t.toAdd

@[expose] def lowerHom (F : Type) [Field F] : Multiplicative F →* SL2 F where
  toFun t := sl2L t.toAdd
  map_one' := sl2L_zero
  map_mul' s t := sl2L_add s.toAdd t.toAdd

@[expose] def diagHom (F : Type) [Field F] : Fˣ →* SL2 F where
  toFun := sl2D
  map_one' := by
    apply sl2_ext
    simp [Matrix.one_fin_two]
  map_mul' a b := by
    apply sl2_ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

@[expose] def upperSub (F : Type) [Field F] : Subgroup (SL2 F) := (upperHom F).range

@[expose] def lowerSub (F : Type) [Field F] : Subgroup (SL2 F) := (lowerHom F).range

@[expose] def diagSub (F : Type) [Field F] : Subgroup (SL2 F) := (diagHom F).range

theorem mem_upperSub_iff (A : SL2 F) : A ∈ upperSub F ↔ ∃ t : F, A = sl2U t := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.toAdd, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd t, rfl⟩

theorem mem_lowerSub_iff (A : SL2 F) : A ∈ lowerSub F ↔ ∃ t : F, A = sl2L t := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.toAdd, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd t, rfl⟩

theorem mem_diagSub_iff (A : SL2 F) : A ∈ diagSub F ↔ ∃ t : Fˣ, A = sl2D t := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

theorem upperHom_injective : Function.Injective (upperHom F) := fun _ _ h =>
  Multiplicative.toAdd.injective (sl2U_injective h)

theorem lowerHom_injective : Function.Injective (lowerHom F) := fun _ _ h =>
  Multiplicative.toAdd.injective (sl2L_injective h)

theorem diagHom_injective : Function.Injective (diagHom F) := by
  intro a b h
  have := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  exact Units.ext (by simpa [diagHom] using this)

theorem card_upperSub [Finite F] : Nat.card (upperSub F) = Nat.card F :=
  (Nat.card_congr (MonoidHom.ofInjective upperHom_injective).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem card_lowerSub [Finite F] : Nat.card (lowerSub F) = Nat.card F :=
  (Nat.card_congr (MonoidHom.ofInjective lowerHom_injective).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem card_diagSub [Finite F] : Nat.card (diagSub F) = Nat.card F - 1 :=
  (Nat.card_congr (MonoidHom.ofInjective diagHom_injective).toEquiv).symm.trans
    (Nat.card_units F)


theorem sl2_entries (g : SL2 F) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  have := g.2
  rw [Matrix.det_fin_two] at this
  exact this

theorem coe_inv_entries (g : SL2 F) :
    ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      !![(g : Matrix (Fin 2) (Fin 2) F) 1 1, -(g : Matrix (Fin 2) (Fin 2) F) 0 1;
        -(g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 0 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem conj_sl2U_entries (g : SL2 F) (t : F) :
    ((g * sl2U t * g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      !![1 - (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 * t,
        (g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t;
        -(g : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2 * t,
        1 + (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 * t] := by
  have hdet := sl2_entries g
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hdet

theorem conj_sl2L_entries (g : SL2 F) (t : F) :
    ((g * sl2L t * g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      !![1 + (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 * t,
        -(g : Matrix (Fin 2) (Fin 2) F) 0 1 ^ 2 * t;
        (g : Matrix (Fin 2) (Fin 2) F) 1 1 ^ 2 * t,
        1 - (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 * t] := by
  have hdet := sl2_entries g
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hdet

theorem conj_sl2U_of_c_zero (g : SL2 F) (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (t : F) :
    g * sl2U t * g⁻¹ = sl2U ((g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t) := by
  apply sl2_ext
  rw [conj_sl2U_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc]

theorem conj_sl2L_of_b_zero (g : SL2 F) (hb : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) (t : F) :
    g * sl2L t * g⁻¹ = sl2L ((g : Matrix (Fin 2) (Fin 2) F) 1 1 ^ 2 * t) := by
  apply sl2_ext
  rw [conj_sl2L_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb]

theorem c_zero_of_conj_mem_upper (g : SL2 F) {t : F} (ht : t ≠ 0)
    (h : g * sl2U t * g⁻¹ ∈ upperSub F) : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨s, hs⟩ := (mem_upperSub_iff _).1 h
  have := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 1 0) hs
  simp only [conj_sl2U_entries, coe_sl2U] at this
  simp at this
  rcases this with h1 | h1
  · exact h1
  · exact absurd h1 ht

theorem b_zero_of_conj_mem_lower (g : SL2 F) {t : F} (ht : t ≠ 0)
    (h : g * sl2L t * g⁻¹ ∈ lowerSub F) : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
  obtain ⟨s, hs⟩ := (mem_lowerSub_iff _).1 h
  have := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) hs
  simp only [conj_sl2L_entries, coe_sl2L] at this
  simp at this
  rcases this with h1 | h1
  · exact h1
  · exact absurd h1 ht


theorem card_map_conj [Finite F] (g : SL2 F) (S : Subgroup (SL2 F)) :
    Nat.card (S.map (MulAut.conj g).toMonoidHom) = Nat.card S :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem map_conj_upper_eq [Finite F] (g : SL2 F) (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (upperSub F).map (MulAut.conj g).toMonoidHom = upperSub F := by
  have hle : (upperSub F).map (MulAut.conj g).toMonoidHom ≤ upperSub F := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, rfl⟩ := (mem_upperSub_iff x).1 hx
    show g * sl2U t * g⁻¹ ∈ upperSub F
    rw [conj_sl2U_of_c_zero g hc]
    exact (mem_upperSub_iff _).2 ⟨_, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_conj])

theorem map_conj_lower_eq [Finite F] (g : SL2 F) (hb : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) :
    (lowerSub F).map (MulAut.conj g).toMonoidHom = lowerSub F := by
  have hle : (lowerSub F).map (MulAut.conj g).toMonoidHom ≤ lowerSub F := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, rfl⟩ := (mem_lowerSub_iff x).1 hx
    show g * sl2L t * g⁻¹ ∈ lowerSub F
    rw [conj_sl2L_of_b_zero g hb]
    exact (mem_lowerSub_iff _).2 ⟨_, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_conj])

theorem mem_normalizer_upper_iff [Finite F] (g : SL2 F) :
    g ∈ normalizer (upperSub F : Set (SL2 F)) ↔ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  constructor
  · intro hg
    have h1 : sl2U (1 : F) ∈ upperSub F := (mem_upperSub_iff _).2 ⟨1, rfl⟩
    exact c_zero_of_conj_mem_upper g one_ne_zero ((mem_normalizer_iff.1 hg _).1 h1)
  · intro hc
    rw [mem_normalizer_iff]
    intro x
    have h := map_conj_upper_eq g hc
    constructor
    · intro hx
      have : g * x * g⁻¹ ∈ (upperSub F).map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
      rwa [h] at this
    · intro hx
      have hc' : ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
        rw [coe_inv_entries]; simp [hc]
      have h' := map_conj_upper_eq g⁻¹ hc'
      have : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ (upperSub F).map (MulAut.conj g⁻¹).toMonoidHom :=
        ⟨_, hx, rfl⟩
      rw [h'] at this
      simpa [mul_assoc] using this

theorem mem_normalizer_lower_iff [Finite F] (g : SL2 F) :
    g ∈ normalizer (lowerSub F : Set (SL2 F)) ↔ (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
  constructor
  · intro hg
    have h1 : sl2L (1 : F) ∈ lowerSub F := (mem_lowerSub_iff _).2 ⟨1, rfl⟩
    exact b_zero_of_conj_mem_lower g one_ne_zero ((mem_normalizer_iff.1 hg _).1 h1)
  · intro hb
    rw [mem_normalizer_iff]
    intro x
    have h := map_conj_lower_eq g hb
    constructor
    · intro hx
      have : g * x * g⁻¹ ∈ (lowerSub F).map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
      rwa [h] at this
    · intro hx
      have hb' : ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
        rw [coe_inv_entries]; simp [hb]
      have h' := map_conj_lower_eq g⁻¹ hb'
      have : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ (lowerSub F).map (MulAut.conj g⁻¹).toMonoidHom :=
        ⟨_, hx, rfl⟩
      rw [h'] at this
      simpa [mul_assoc] using this

theorem mem_diagSub_of (g : SL2 F) (hb : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0)
    (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) : g ∈ diagSub F := by
  have hdet := sl2_entries g
  rw [hb, hc] at hdet
  have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  refine (mem_diagSub_iff _).2 ⟨Units.mk0 _ ha, ?_⟩
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb, hc]
  field_simp
  linear_combination hdet

theorem sl2D_entries_zero (t : Fˣ) :
    (sl2D t : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (sl2D t : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  simp

theorem normalizer_upper_inf_lower [Finite F] :
    normalizer (upperSub F : Set (SL2 F)) ⊓ normalizer (lowerSub F : Set (SL2 F)) = diagSub F := by
  ext g
  rw [Subgroup.mem_inf, mem_normalizer_upper_iff, mem_normalizer_lower_iff]
  constructor
  · rintro ⟨hc, hb⟩
    exact mem_diagSub_of g hb hc
  · intro hg
    obtain ⟨t, rfl⟩ := (mem_diagSub_iff _).1 hg
    exact ⟨(sl2D_entries_zero t).2, (sl2D_entries_zero t).1⟩


theorem antidiag_of_swap_sq (g : SL2 F) (hs : g * sl2U 1 * g⁻¹ ∈ lowerSub F)
    (hsq : g * g ∈ diagSub F) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  have hdet := sl2_entries g
  obtain ⟨s, hs'⟩ := (mem_lowerSub_iff _).1 hs
  have h01 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) hs'
  simp only [conj_sl2U_entries] at h01
  simp at h01
  have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := h01
  obtain ⟨t, ht⟩ := (mem_diagSub_iff _).1 hsq
  have h2 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) ht
  rw [Matrix.SpecialLinearGroup.coe_mul] at h2
  simp [Matrix.mul_apply, Fin.sum_univ_two, ha] at h2
  have hb : (g : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := by
    intro h
    rw [ha, h] at hdet
    simp at hdet
  exact ⟨ha, h2.resolve_left hb⟩

theorem antidiag_eq (g : SL2 F) (h0 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 0)
    (h1 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0) : ∃ t : Fˣ, g = sl2W F * sl2D t := by
  have hdet := sl2_entries g
  rw [h0, h1] at hdet
  have hz : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    intro hz
    rw [hz] at hdet
    simp at hdet
  refine ⟨Units.mk0 (-(g : Matrix (Fin 2) (Fin 2) F) 1 0) (neg_ne_zero.2 hz), ?_⟩
  apply sl2_ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
  field_simp
  linear_combination -hdet

theorem sl2L_eq (c : F) (hc : c ≠ 0) :
    sl2L c = sl2U c⁻¹ * (sl2W F * sl2D (Units.mk0 (-c) (neg_ne_zero.2 hc))) * sl2U c⁻¹ := by
  apply sl2_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  ring


@[expose] def cj (g : SL2 F) (S : Subgroup (SL2 F)) : Subgroup (SL2 F) :=
  S.map (MulAut.conj g).toMonoidHom

theorem mem_cj_iff {g x : SL2 F} {S : Subgroup (SL2 F)} : x ∈ cj g S ↔ g⁻¹ * x * g ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem cj_cj (g h : SL2 F) (S : Subgroup (SL2 F)) : cj g (cj h S) = cj (g * h) S := by
  ext x
  rw [mem_cj_iff, mem_cj_iff, mem_cj_iff]
  simp [mul_assoc]

theorem cj_inv_cj (g : SL2 F) (S : Subgroup (SL2 F)) : cj g⁻¹ (cj g S) = S := by
  rw [cj_cj]
  ext x
  rw [mem_cj_iff]
  simp

theorem card_cj [Finite F] (g : SL2 F) (S : Subgroup (SL2 F)) : Nat.card (cj g S) = Nat.card S :=
  card_map_conj g S

theorem cj_upper_of_c_zero [Finite F] {g : SL2 F} (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    cj g (upperSub F) = upperSub F := map_conj_upper_eq g hc

theorem cj_wc_upper [Finite F] (c : F) (hc : c ≠ 0) : cj (wc c hc) (upperSub F) = lowerSub F := by
  ext x
  rw [mem_cj_iff]
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := (mem_upperSub_iff _).1 hx
    have h1 : wc c hc * (wc c hc)⁻¹ * x * (wc c hc * (wc c hc)⁻¹) = x := by simp
    have : x = wc c hc * sl2U t * (wc c hc)⁻¹ := by
      rw [← ht]; group
    rw [this]
    have e := wc_conj_unip c hc t
    have e' : CFSG.PSL2Table.unip t = sl2U t := rfl
    rw [e'] at e
    rw [e]
    exact (mem_lowerSub_iff _).2 ⟨_, rfl⟩
  · intro hx
    obtain ⟨t, rfl⟩ := (mem_lowerSub_iff _).1 hx
    have e := wc_conj_unip c hc (-(t / c ^ 2))
    have e' : CFSG.PSL2Table.unip (-(t / c ^ 2)) = sl2U (-(t / c ^ 2)) := rfl
    rw [e'] at e
    have h2 : -(c ^ 2 * -(t / c ^ 2)) = t := by field_simp
    rw [h2] at e
    have : (wc c hc)⁻¹ * sl2L t * wc c hc = sl2U (-(t / c ^ 2)) := by
      rw [show sl2L t = lowT t from rfl, ← e]; group
    rw [this]
    exact (mem_upperSub_iff _).2 ⟨_, rfl⟩


theorem sl2U_inv (t : F) : (sl2U t)⁻¹ = sl2U (-t) := by
  rw [inv_eq_iff_mul_eq_one, ← sl2U_add, add_neg_cancel, sl2U_zero]

theorem coe_sl2U_c (t : F) : (sl2U t : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simp

theorem cj_sl2U_upper [Finite F] (t : F) : cj (sl2U t) (upperSub F) = upperSub F :=
  cj_upper_of_c_zero (coe_sl2U_c t)

theorem cj_bruhat [Finite F] (k : SL2 F) (hc : (k : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    cj k (upperSub F) =
      cj (sl2U ((k : Matrix (Fin 2) (Fin 2) F) 0 0 / (k : Matrix (Fin 2) (Fin 2) F) 1 0))
        (lowerSub F) := by
  have h := unip_mul_mul_unip k hc
  have e1 : (CFSG.PSL2Table.unip : F → SL2 F) = sl2U := rfl
  rw [e1] at h
  have hk : k = sl2U ((k : Matrix (Fin 2) (Fin 2) F) 0 0 / (k : Matrix (Fin 2) (Fin 2) F) 1 0) *
      wc ((k : Matrix (Fin 2) (Fin 2) F) 1 0) hc *
      sl2U ((k : Matrix (Fin 2) (Fin 2) F) 1 1 / (k : Matrix (Fin 2) (Fin 2) F) 1 0) := by
    set x : F := (k : Matrix (Fin 2) (Fin 2) F) 0 0 / (k : Matrix (Fin 2) (Fin 2) F) 1 0 with hx
    set y : F := (k : Matrix (Fin 2) (Fin 2) F) 1 1 / (k : Matrix (Fin 2) (Fin 2) F) 1 0 with hy
    have i1 : sl2U x * sl2U (-x) = 1 := by rw [← sl2U_add, add_neg_cancel, sl2U_zero]
    have i2 : sl2U (-y) * sl2U y = 1 := by rw [← sl2U_add, neg_add_cancel, sl2U_zero]
    calc k = (sl2U x * sl2U (-x)) * k * (sl2U (-y) * sl2U y) := by rw [i1, i2, one_mul, mul_one]
      _ = sl2U x * (sl2U (-x) * k * sl2U (-y)) * sl2U y := by group
      _ = _ := by rw [h]
  conv_lhs => rw [hk]
  rw [← cj_cj, ← cj_cj, cj_sl2U_upper, cj_wc_upper]

theorem map_symm_eq {K : Type*} [Group K] (ψ : K ≃* SL2 F) {X : Subgroup K}
    {Y : Subgroup (SL2 F)} (h : X.map ψ.toMonoidHom = Y) : Y.map ψ.symm.toMonoidHom = X := by
  rw [← h, Subgroup.map_map]
  have : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id K := by ext x; simp
  rw [this, Subgroup.map_id]

theorem exists_equiv_of_sylow_pair [Finite F] {K : Type*} [Group K] {p f : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ f) (e : K ≃* SL2 F) {X X' : Subgroup K}
    (hX : Nat.card X = Nat.card F) (hX' : Nat.card X' = Nat.card F) (hne : X ≠ X') :
    ∃ φ : SL2 F ≃* K, (upperSub F).map φ.toMonoidHom = X ∧
      (lowerSub F).map φ.toMonoidHom = X' := by
  have hQc : Nat.card (X.map e.toMonoidHom) = Nat.card F := by
    rw [Subgroup.card_map_of_injective e.injective]; exact hX
  have hQ'c : Nat.card (X'.map e.toMonoidHom) = Nat.card F := by
    rw [Subgroup.card_map_of_injective e.injective]; exact hX'
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem hp hcard hQc
  obtain ⟨h, hh⟩ := exists_conj_unipotent_mem hp hcard hQ'c
  have hgQ : cj g (upperSub F) = X.map e.toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [card_cj, card_upperSub, hQc])
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := (mem_upperSub_iff y).1 hy
    exact hg t
  have hhQ : cj h (upperSub F) = X'.map e.toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [card_cj, card_upperSub, hQ'c])
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := (mem_upperSub_iff y).1 hy
    exact hh t
  obtain ⟨k, hk⟩ : ∃ k : SL2 F, k = g⁻¹ * h := ⟨_, rfl⟩
  have hkc : (k : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    intro hc
    have h1 : cj k (upperSub F) = upperSub F := cj_upper_of_c_zero hc
    apply hne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    have e2 : cj h (upperSub F) = cj g (cj k (upperSub F)) := by
      rw [cj_cj, hk]; simp
    rw [← hgQ, ← hhQ, e2, h1]
  have hbr := cj_bruhat k hkc
  obtain ⟨s, hs⟩ : ∃ s : F, s = (k : Matrix (Fin 2) (Fin 2) F) 0 0 / (k : Matrix (Fin 2) (Fin 2) F) 1 0 :=
    ⟨_, rfl⟩
  rw [← hs] at hbr
  obtain ⟨ψ, hψ⟩ : ∃ ψ : K ≃* SL2 F, ψ = e.trans (MulAut.conj (g * sl2U s)⁻¹) := ⟨_, rfl⟩
  have hψmap : ∀ Y : Subgroup K, Y.map ψ.toMonoidHom = cj (g * sl2U s)⁻¹ (Y.map e.toMonoidHom) := by
    intro Y
    rw [hψ, cj, Subgroup.map_map]
    rfl
  have hψX : X.map ψ.toMonoidHom = upperSub F := by
    rw [hψmap, ← hgQ, cj_cj]
    have : (g * sl2U s)⁻¹ * g = sl2U (-s) := by rw [_root_.mul_inv_rev, inv_mul_cancel_right, sl2U_inv]
    rw [this, cj_sl2U_upper]
  have hψX' : X'.map ψ.toMonoidHom = lowerSub F := by
    rw [hψmap, ← hhQ, cj_cj]
    have : (g * sl2U s)⁻¹ * h = sl2U (-s) * k := by
      rw [_root_.mul_inv_rev, sl2U_inv, hk]; group
    rw [this, ← cj_cj, hbr, cj_cj, ← sl2U_add, neg_add_cancel, sl2U_zero]
    ext x
    rw [mem_cj_iff]
    simp
  exact ⟨ψ.symm, map_symm_eq ψ hψX, map_symm_eq ψ hψX'⟩


theorem exists_rankOne [Finite F] {K : Type*} [Group K] {p f : ℕ}
    (hp : p.Prime) (hcard : Nat.card F = p ^ f) (e : K ≃* SL2 F) {X X' T : Subgroup K} {w : K}
    (hX : Nat.card X = Nat.card F) (hX' : Nat.card X' = Nat.card F) (hne : X ≠ X')
    (hT : T ≤ normalizer (X : Set K) ⊓ normalizer (X' : Set K)) (hTc : Nat.card T = Nat.card F - 1)
    (hw : w * w ∈ T) (hwX : ∀ x ∈ X, w * x * w⁻¹ ∈ X') :
    ∃ φ : SL2 F ≃* K, (upperSub F).map φ.toMonoidHom = X ∧ (lowerSub F).map φ.toMonoidHom = X' ∧
      (diagSub F).map φ.toMonoidHom = T ∧ ∃ t ∈ T, φ (sl2W F) = w * t := by
  have : Finite K := Finite.of_equiv (SL2 F) e.symm.toEquiv
  obtain ⟨φ, hφX, hφX'⟩ := exists_equiv_of_sylow_pair hp hcard e hX hX' hne
  have memX : ∀ y : SL2 F, y ∈ upperSub F ↔ φ y ∈ X := by
    intro y
    rw [← hφX]
    constructor
    · intro hy; exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have : z = y := φ.injective hzy
      rwa [this] at hz
  have memX' : ∀ y : SL2 F, y ∈ lowerSub F ↔ φ y ∈ X' := by
    intro y
    rw [← hφX']
    constructor
    · intro hy; exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have : z = y := φ.injective hzy
      rwa [this] at hz
  have hTD : ∀ x ∈ T, φ.symm x ∈ diagSub F := by
    intro x hx
    have hx1 : x ∈ normalizer (X : Set K) := (hT hx).1
    have hx2 : x ∈ normalizer (X' : Set K) := (hT hx).2
    rw [← normalizer_upper_inf_lower, Subgroup.mem_inf, mem_normalizer_iff, mem_normalizer_iff]
    constructor
    · intro y
      rw [memX y, memX (φ.symm x * y * (φ.symm x)⁻¹)]
      simpa using mem_normalizer_iff.1 hx1 (φ y)
    · intro y
      rw [memX' y, memX' (φ.symm x * y * (φ.symm x)⁻¹)]
      simpa using mem_normalizer_iff.1 hx2 (φ y)
  have hTle : T ≤ (diagSub F).map φ.toMonoidHom := by
    intro x hx
    exact ⟨φ.symm x, hTD x hx, by simp⟩
  have hTeq : (diagSub F).map φ.toMonoidHom = T := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hTle ?_
    rw [Subgroup.card_map_of_injective φ.injective, card_diagSub, hTc]
  refine ⟨φ, hφX, hφX', hTeq, ?_⟩
  set g : SL2 F := φ.symm w with hg
  have hgsq : g * g ∈ diagSub F := by
    have := hTD _ hw
    simpa [hg] using this
  have hswap : g * sl2U 1 * g⁻¹ ∈ lowerSub F := by
    have hu : sl2U (1 : F) ∈ upperSub F := (mem_upperSub_iff _).2 ⟨1, rfl⟩
    have h1 : w * φ (sl2U 1) * w⁻¹ ∈ X' := hwX _ ((memX _).1 hu)
    have h2 : φ (g * sl2U 1 * g⁻¹) ∈ X' := by simpa [hg] using h1
    exact (memX' _).2 h2
  have hgW := antidiag_of_swap_sq g hswap hgsq
  obtain ⟨t, ht⟩ := antidiag_eq g hgW.1 hgW.2
  have hwt : w = φ (sl2W F) * φ (sl2D t) := by
    have : φ g = w := by simp [hg]
    rw [← this, ht, map_mul]
  have hdt : φ (sl2D t)⁻¹ ∈ T := by
    rw [← hTeq]
    exact ⟨(sl2D t)⁻¹, Subgroup.inv_mem _ ((mem_diagSub_iff _).2 ⟨t, rfl⟩), by simp⟩
  refine ⟨φ (sl2D t)⁻¹, hdt, ?_⟩
  rw [hwt]
  simp

end CFSG.GH74.GLS.Stage4.SL2
