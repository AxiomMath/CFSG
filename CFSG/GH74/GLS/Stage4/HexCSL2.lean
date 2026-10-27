module

public import CFSG.GH74.GLS.Stage4.HexSL2Defs

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Hex

section Identities

variable {F : Type*} [Field F]

@[expose] def sl2Wc (c : F) : SL2 F := sl2U c * sl2L (-c⁻¹) * sl2U c

theorem coe_sl2Wc {c : F} (hc : c ≠ 0) :
    (sl2Wc c : Matrix (Fin 2) (Fin 2) F) = !![0, c; -c⁻¹, 0] := by
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have hcc' : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  have e : ((sl2Wc c : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, c; 0, 1] * !![1, 0; -c⁻¹, 1] * !![1, c; 0, 1] := by
    simp [sl2Wc, Matrix.SpecialLinearGroup.coe_mul]
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hcc, hcc']

theorem sl2U_one_mul_sl2Wc {c : F} (hc : c ≠ 0) :
    sl2U 1 * sl2Wc c = sl2Wc c * sl2L (-(c⁻¹ * c⁻¹)) := by
  apply sl2_ext
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Wc hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp

theorem sl2L_one_mul_sl2Wc {c : F} (hc : c ≠ 0) :
    sl2L 1 * sl2Wc c = sl2Wc c * sl2U (-(c * c)) := by
  apply sl2_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Wc hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp

theorem sl2D_eq_sl2Wc (t : Fˣ) : sl2D t = sl2Wc (t : F) * sl2Wc (-1) := by
  have h1 : (-1 : F) ≠ 0 := neg_ne_zero.2 one_ne_zero
  apply sl2_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Wc t.ne_zero, coe_sl2Wc h1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2W_mul_sl2U (d : F) : sl2W F * sl2U d = sl2L (-d) * sl2W F := by
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2W_mul_self : sl2W F * sl2W F = sl2D (-1) := by
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2W_eq_sl2Wc : sl2W F = sl2Wc (1 : F) := by
  apply sl2_ext
  rw [coe_sl2Wc one_ne_zero]
  simp

theorem sl2_mem_closure (A : SL2 F) :
    A ∈ Subgroup.closure (Set.range (sl2U (F := F)) ∪ Set.range (sl2L (F := F))) := by
  set S := Subgroup.closure (Set.range (sl2U (F := F)) ∪ Set.range (sl2L (F := F)))
  have hU : ∀ c, sl2U c ∈ S := fun c => Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
  have hL : ∀ c, sl2L c ∈ S := fun c => Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  have hdet : ∀ B : SL2 F,
      (B : Matrix (Fin 2) (Fin 2) F) 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := fun B => by
    have := B.2
    rwa [Matrix.det_fin_two] at this
  have key : ∀ B : SL2 F, (B : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → B ∈ S := by
    intro B hc
    have hB : B = sl2U ((B 0 0 - 1) / B 1 0) * sl2L (B 1 0) * sl2U ((B 1 1 - 1) / B 1 0) := by
      apply sl2_ext
      have h := hdet B
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2U,
        coe_sl2L, coe_sl2U]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
        first | ring1 | linear_combination h | linear_combination -h
    rw [hB]
    exact mul_mem (mul_mem (hU _) (hL _)) (hU _)
  by_cases hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have h00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h
      have := hdet A
      rw [h, hc] at this
      simp at this
    have hLA : ((sl2L 1 * A : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2L]
      simp [Matrix.mul_apply, Fin.sum_univ_two, hc, h00]
    have e : A = (sl2L 1)⁻¹ * (sl2L 1 * A) := by group
    rw [e]
    exact mul_mem (inv_mem (hL 1)) (key _ hLA)
  · exact key A hc

theorem sl2_hom_mem {G : Type*} [Group G] (φ : SL2 F →* G) (S : Subgroup G)
    (hU : ∀ c, φ (sl2U c) ∈ S) (hL : ∀ c, φ (sl2L c) ∈ S) (A : SL2 F) : φ A ∈ S := by
  have h := sl2_mem_closure A
  have hle : Subgroup.closure (Set.range (sl2U (F := F)) ∪ Set.range (sl2L (F := F))) ≤
      S.comap φ := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hU c
    · exact hL c
  exact hle h

end Identities

section NatMod

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M]

@[expose] def wmap (u l : F → M →+ M) (c : F) (x : M) : M := u c (l (-c⁻¹) (u c x))

structure NatModData (A B : AddSubgroup M) (u l : F → M →+ M) : Prop where
  u_zero : ∀ x, u 0 x = x
  u_add : ∀ c d x, u (c + d) x = u c (u d x)
  uw : ∀ c : F, c ≠ 0 → ∀ x, u 1 (wmap u l c x) = wmap u l c (l (-(c⁻¹ * c⁻¹)) x)
  lw : ∀ c : F, c ≠ 0 → ∀ x, l 1 (wmap u l c x) = wmap u l c (u (-(c * c)) x)
  uA : ∀ c, ∀ a ∈ A, u c a = a
  lB : ∀ c, ∀ b ∈ B, l c b = b
  uB : ∀ c, ∀ b ∈ B, u c b - b ∈ A
  lA : ∀ c, ∀ a ∈ A, l c a - a ∈ B
  ndU : ∀ b ∈ B, u 1 b = b → b = 0
  ndL : ∀ a ∈ A, l 1 a = a → a = 0

namespace NatModData

variable {A B : AddSubgroup M} {u l : F → M →+ M} (h : NatModData A B u l)

include h in
theorem g_add {b : M} (hb : b ∈ B) (c d : F) :
    u (c + d) b - b = (u c b - b) + (u d b - b) := by
  have hA : u d b - b ∈ A := h.uB d b hb
  have e : u d b = b + (u d b - b) := by abel
  rw [h.u_add c d b]
  conv_lhs => rw [e]
  rw [map_add, h.uA c _ hA]
  abel

include h in
theorem g_neg {b : M} (hb : b ∈ B) (c : F) : u (-c) b - b = -(u c b - b) := by
  have h1 := h.g_add hb c (-c)
  rw [add_neg_cancel, h.u_zero, sub_self] at h1
  exact eq_neg_of_add_eq_zero_right h1.symm

include h in
theorem weyl_B {c : F} (hc : c ≠ 0) {b : M} (hb : b ∈ B) :
    l (-c⁻¹) (u c b - b) - (u c b - b) = -b ∧ wmap u l c b = u c b - b := by
  set a₁ := u c b - b with ha₁
  have ha₁A : a₁ ∈ A := h.uB c b hb
  set β₁ := l (-c⁻¹) a₁ - a₁ with hβ₁
  have hβ₁B : β₁ ∈ B := h.lA _ a₁ ha₁A
  set g₁ := u c β₁ - β₁ with hg₁
  have hg₁A : g₁ ∈ A := h.uB c β₁ hβ₁B
  have hub : u c b = b + a₁ := by rw [ha₁]; abel
  have hlb : l (-c⁻¹) (b + a₁) = b + (a₁ + β₁) := by
    rw [map_add, h.lB _ b hb, hβ₁]; abel
  have huβ : u c β₁ = β₁ + g₁ := by rw [hg₁]; abel
  have hW : wmap u l c b = (b + β₁) + (a₁ + a₁ + g₁) := by
    unfold wmap
    rw [hub, hlb, map_add, map_add, hub, h.uA c a₁ ha₁A, huβ]
    abel
  have hfix : u 1 (wmap u l c b) = wmap u l c b := by
    rw [h.uw c hc b, h.lB _ b hb]
  have hAA : a₁ + a₁ + g₁ ∈ A := A.add_mem (A.add_mem ha₁A ha₁A) hg₁A
  have hbB : b + β₁ ∈ B := B.add_mem hb hβ₁B
  rw [hW, map_add, h.uA 1 _ hAA] at hfix
  have hfix' : u 1 (b + β₁) = b + β₁ := add_right_cancel hfix
  have h0 : b + β₁ = 0 := h.ndU _ hbB hfix'
  have hβ : β₁ = -b := eq_neg_of_add_eq_zero_right h0
  have hg : g₁ = -a₁ := by rw [hg₁, hβ, map_neg, ha₁]; abel
  refine ⟨hβ, ?_⟩
  rw [hW, h0, hg]; abel

include h in
theorem weyl_A {c : F} (hc : c ≠ 0) {a : M} (ha : a ∈ A) :
    u c (l (-c⁻¹) a - a) - (l (-c⁻¹) a - a) = -a ∧ wmap u l c a = l (-c⁻¹) a - a := by
  set β := l (-c⁻¹) a - a with hβ
  have hβB : β ∈ B := h.lA _ a ha
  set g := u c β - β with hg
  have hgA : g ∈ A := h.uB c β hβB
  have hla : l (-c⁻¹) a = a + β := by rw [hβ]; abel
  have huβ : u c β = β + g := by rw [hg]; abel
  have hW : wmap u l c a = (a + g) + β := by
    unfold wmap
    rw [h.uA c a ha, hla, map_add, h.uA c a ha, huβ]; abel
  have hfix : l 1 (wmap u l c a) = wmap u l c a := by
    rw [h.lw c hc a, h.uA _ a ha]
  have haa : a + g ∈ A := A.add_mem ha hgA
  rw [hW, map_add, h.lB 1 β hβB] at hfix
  have hfix' : l 1 (a + g) = a + g := add_right_cancel hfix
  have h0 : a + g = 0 := h.ndL _ haa hfix'
  have hg' : g = -a := eq_neg_of_add_eq_zero_right h0
  refine ⟨hg', ?_⟩
  rw [hW, h0, zero_add]

include h in
theorem key {t : F} (ht : t ≠ 0) (d : M →+ M)
    (hd : ∀ x, d x = wmap u l t (wmap u l (-1) x)) {b : M} (hb : b ∈ B) :
    d b ∈ B ∧ u t (d b) - d b = u 1 b - b := by
  have h1 : (-1 : F) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have hB := h.weyl_B h1 hb
  have hneg := h.g_neg hb 1
  have ha : u (-1) b - b ∈ A := h.uB (-1) b hb
  have hA := h.weyl_A ht ha
  have hAw := hA.2
  have hA1 := hA.1
  rw [hd, hB.2]
  refine ⟨?_, ?_⟩
  · rw [hAw]; exact h.lA _ _ ha
  · rw [hAw, hA1, hneg, neg_neg]

end NatModData

end NatMod

end CFSG.GH74.GLS.Stage4.Hex
