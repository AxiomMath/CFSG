module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFullAffine

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.Jhat

open Matrix CFSG.LocalAnalysis.ComponentInitial

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)
local notation "𝕊" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}

@[expose] def altS (c : Fin 3 → ZMod 2) : 𝕊 :=
  ⟨symThreeAlt c, symThreeAlt_mem c⟩

@[expose] def iotaY : Fin 3 → 𝕊 :=
  fun i => altS (Pi.single i 1)

@[expose] def lin3 (c : Fin 3 → ZMod 2) (y : Fin 3 → 𝕊) : 𝕊 :=
  c 0 • y 0 + c 1 • y 1 + c 2 • y 2

@[expose] def actY (g : GL (Fin 3) (ZMod 2)) (y : Fin 3 → 𝕊) : Fin 3 → 𝕊 :=
  fun i => symThreeCongr g (lin3 (fun j => (g : M₃) i j) y)

@[expose] def rows9 (a b c d e f g h i : ZMod 2) : Fin 3 → Fin 3 → ZMod 2 :=
  ![![a, b, c], ![d, e, f], ![g, h, i]]

@[expose] def actV (g : GL (Fin 3) (ZMod 2)) (u : Fin 3 → Fin 3 → ZMod 2) (i : Fin 3) :
    Fin 3 → ZMod 2 :=
  (g : M₃) *ᵥ ((g : M₃) i 0 • u 0 + (g : M₃) i 1 • u 1 + (g : M₃) i 2 • u 2)

@[expose] def glSwapOneTwo : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide, by decide⟩

@[expose] def glRot : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], !![1, 1, 0; 1, 0, 0; 0, 0, 1], by decide, by decide⟩

theorem glSwapTwoThree_e1 : (glSwapTwoThree : M₃) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  decide

theorem glTransTwoOne_e1 : (glTransTwoOne : M₃) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  decide

theorem glTransThreeTwo_e1 : (glTransThreeTwo : M₃) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  decide

theorem glTransThreeOne_e1 : (glTransThreeOne : M₃) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  decide

theorem glTransThreeOne_e2 : (glTransThreeOne : M₃) *ᵥ ![0, 1, 0] = ![0, 1, 0] := by
  decide

theorem glSwapOneTwo_e1 : (glSwapOneTwo : M₃) *ᵥ ![1, 0, 0] = ![0, 1, 0] := by
  decide

theorem glRot_e1 : (glRot : M₃) *ᵥ ![1, 0, 0] = ![0, 1, 0] := by
  decide

theorem glRot_e2 : (glRot : M₃) *ᵥ ![0, 1, 0] = ![1, 1, 0] := by
  decide

theorem glRot_inv_e1 : ((glRot⁻¹ : GL (Fin 3) (ZMod 2)) : M₃) *ᵥ ![1, 0, 0] = ![1, 1, 0] := by
  decide

theorem e1_add_e2 : (![1, 0, 0] : Fin 3 → ZMod 2) + ![0, 1, 0] = ![1, 1, 0] := by
  decide

theorem inv_alt_glSwapTwoThree : ∀ i : Fin 3,
    symThreeCongr glSwapTwoThree⁻¹ (altS (Pi.single i 1)) =
      altS (fun j => (glSwapTwoThree : M₃) i j) := by
  decide

theorem inv_alt_glTransTwoOne : ∀ i : Fin 3,
    symThreeCongr glTransTwoOne⁻¹ (altS (Pi.single i 1)) =
      altS (fun j => (glTransTwoOne : M₃) i j) := by
  decide

theorem inv_alt_glTransThreeTwo : ∀ i : Fin 3,
    symThreeCongr glTransThreeTwo⁻¹ (altS (Pi.single i 1)) =
      altS (fun j => (glTransThreeTwo : M₃) i j) := by
  decide

theorem inv_alt_glSwapOneTwo : ∀ i : Fin 3,
    symThreeCongr glSwapOneTwo⁻¹ (altS (Pi.single i 1)) =
      altS (fun j => (glSwapOneTwo : M₃) i j) := by
  decide

theorem inv_alt_glRot_inv : ∀ i : Fin 3,
    symThreeCongr glRot⁻¹⁻¹ (altS (Pi.single i 1)) =
      altS (fun j => ((glRot⁻¹ : GL (Fin 3) (ZMod 2)) : M₃) i j) := by
  decide

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
theorem diag_check : ∀ a b c d e f g h i : ZMod 2,
    (∀ r, actV glSwapTwoThree (rows9 a b c d e f g h i) r = rows9 a b c d e f g h i r) →
    (∀ r, actV glTransTwoOne (rows9 a b c d e f g h i) r = rows9 a b c d e f g h i r) →
    (∀ r, actV glTransThreeTwo (rows9 a b c d e f g h i) r = rows9 a b c d e f g h i r) →
    (∀ r, rows9 a b c d e f g h i r + actV glSwapOneTwo (rows9 a b c d e f g h i) r +
      actV glRot⁻¹ (rows9 a b c d e f g h i) r = 0) →
    rows9 a b c d e f g h i = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
theorem alt_check : ∀ a b c d e f g h i : ZMod 2,
    (actY glSwapTwoThree (fun r => altS (rows9 a b c d e f g h i r)) =
        (fun r => altS (rows9 a b c d e f g h i r)) ∨
      actY glSwapTwoThree (fun r => altS (rows9 a b c d e f g h i r)) =
        (fun r => altS (rows9 a b c d e f g h i r)) + iotaY) →
    (actY glTransTwoOne (fun r => altS (rows9 a b c d e f g h i r)) =
        (fun r => altS (rows9 a b c d e f g h i r)) ∨
      actY glTransTwoOne (fun r => altS (rows9 a b c d e f g h i r)) =
        (fun r => altS (rows9 a b c d e f g h i r)) + iotaY) →
    (actY glTransThreeTwo (fun r => altS (rows9 a b c d e f g h i r)) =
        (fun r => altS (rows9 a b c d e f g h i r)) ∨
      actY glTransThreeTwo (fun r => altS (rows9 a b c d e f g h i r)) =
        (fun r => altS (rows9 a b c d e f g h i r)) + iotaY) →
    rows9 a b c d e f g h i = 0 ∨ rows9 a b c d e f g h i = rows9 1 0 0 0 1 0 0 0 1 := by
  decide +kernel

theorem fix_pair_check : ∀ v : Fin 3 → ZMod 2, (glTransThreeOne : M₃) *ᵥ v = v →
    (glRot : M₃) *ᵥ v = v → v = 0 := by
  decide

theorem fix_one_check : ∀ v : Fin 3 → ZMod 2, (glTransTwoOne : M₃) *ᵥ v = v →
    (glTransThreeOne : M₃) *ᵥ v = v → v = 0 ∨ v = ![1, 0, 0] := by
  decide

set_option maxRecDepth 100000 in
theorem sym_check : ∀ a b c d e f : ZMod 2, a = 1 → b = 0 → c = 0 →
    (glSwapTwoThree : M₃) * !![a, d, e; d, b, f; e, f, c] * (glSwapTwoThree : M₃)ᵀ =
      !![a, d, e; d, b, f; e, f, c] →
    (glTransTwoOne : M₃) * !![a, d, e; d, b, f; e, f, c] * (glTransTwoOne : M₃)ᵀ =
      !![a, d, e; d, b, f; e, f, c] →
    (glTransThreeTwo : M₃) * !![a, d, e; d, b, f; e, f, c] * (glTransThreeTwo : M₃)ᵀ =
      !![a, d, e; d, b, f; e, f, c] →
    !![a, d, e; d, b, f; e, f, c] +
        (glSwapOneTwo : M₃) * !![a, d, e; d, b, f; e, f, c] * (glSwapOneTwo : M₃)ᵀ ≠
      ((glRot⁻¹ : GL (Fin 3) (ZMod 2)) : M₃) * !![a, d, e; d, b, f; e, f, c] *
        ((glRot⁻¹ : GL (Fin 3) (ZMod 2)) : M₃)ᵀ := by
  decide +kernel

theorem diag_actY (g : GL (Fin 3) (ZMod 2)) (y : Fin 3 → 𝕊) (i : Fin 3) :
    symThreeDiag (actY g y i : M₃) = actV g (fun j => symThreeDiag (y j : M₃)) i := by
  unfold actY actV
  rw [symThreeDiag_coe_congr]
  rfl

theorem diag_iotaY (i : Fin 3) : symThreeDiag (iotaY i : M₃) = 0 :=
  symThreeDiag_alt _

theorem rows9_eta (u : Fin 3 → Fin 3 → ZMod 2) :
    u = rows9 (u 0 0) (u 0 1) (u 0 2) (u 1 0) (u 1 1) (u 1 2) (u 2 0) (u 2 1) (u 2 2) := by
  funext r k
  fin_cases r <;> fin_cases k <;> rfl

theorem eq_zero_or_eq_iotaY (y : Fin 3 → 𝕊)
    (h1 : actY glSwapTwoThree y = y ∨ actY glSwapTwoThree y = y + iotaY)
    (h2 : actY glTransTwoOne y = y ∨ actY glTransTwoOne y = y + iotaY)
    (h3 : actY glTransThreeTwo y = y ∨ actY glTransThreeTwo y = y + iotaY)
    (h4 : y + actY glSwapOneTwo y + actY glRot⁻¹ y = 0 ∨
      y + actY glSwapOneTwo y + actY glRot⁻¹ y = iotaY) :
    y = 0 ∨ y = iotaY := by
  have hfix : ∀ g, (actY g y = y ∨ actY g y = y + iotaY) →
      ∀ r, actV g (fun j => symThreeDiag (y j : M₃)) r = symThreeDiag (y r : M₃) := by
    intro g hg r
    rw [← diag_actY]
    rcases hg with hg | hg <;> rw [hg]
    change symThreeDiag ((y r : M₃) + (iotaY r : M₃)) = _
    rw [symThreeDiag_add, diag_iotaY, add_zero]
  have hsum : ∀ r, symThreeDiag (y r : M₃) +
      actV glSwapOneTwo (fun j => symThreeDiag (y j : M₃)) r +
      actV glRot⁻¹ (fun j => symThreeDiag (y j : M₃)) r = 0 := by
    intro r
    rw [← diag_actY, ← diag_actY]
    have h : symThreeDiag ((y + actY glSwapOneTwo y + actY glRot⁻¹ y) r : M₃) = 0 := by
      rcases h4 with h4 | h4 <;> rw [h4]
      · rfl
      · exact diag_iotaY r
    exact h
  have hu0 : (fun j => symThreeDiag (y j : M₃)) = 0 := by
    obtain ⟨a, b, c, d, e, f, g, h, i, hu⟩ : ∃ a b c d e f g h i : ZMod 2,
        (fun j => symThreeDiag (y j : M₃)) = rows9 a b c d e f g h i :=
      ⟨_, _, _, _, _, _, _, _, _, rows9_eta _⟩
    have hu' : ∀ r, symThreeDiag (y r : M₃) = rows9 a b c d e f g h i r := fun r => congrFun hu r
    simp only [hu] at hfix hsum ⊢
    simp only [hu'] at hfix hsum
    exact diag_check _ _ _ _ _ _ _ _ _ (hfix _ h1) (hfix _ h2) (hfix _ h3) hsum
  have hyw : y = fun r => altS (symThreeOff (y r : M₃)) := by
    funext r
    exact Subtype.ext (eq_symThreeAlt (y r).2 (congrFun hu0 r))
  obtain ⟨a, b, c, d, e, f, g, h, i, hw⟩ : ∃ a b c d e f g h i : ZMod 2,
      (fun r => symThreeOff (y r : M₃)) = rows9 a b c d e f g h i :=
    ⟨_, _, _, _, _, _, _, _, _, rows9_eta _⟩
  have hyw' : y = fun r => altS (rows9 a b c d e f g h i r) := by
    rw [hyw, ← hw]
  rw [hyw'] at h1 h2 h3 ⊢
  rcases alt_check _ _ _ _ _ _ _ _ _ h1 h2 h3 with h | h
  · left
    rw [h]
    funext r
    exact Subtype.ext ((symThreeAlt_eq_zero_iff 0).2 rfl)
  · right
    rw [h]
    funext r
    exact congrArg altS (by revert r; decide)

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.Jhat
