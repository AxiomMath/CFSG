module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LocalAnalysis.ComponentInitial

theorem exists_retraction_of_sq_eq_one {Q : Type*} [CommGroup Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    (Y : Subgroup Q) : ∃ p : Q →* Q, (∀ q, p q ∈ Y) ∧ ∀ y ∈ Y, p y = y := by
  let _ : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule fun x =>
    Additive.toMul.injective (by rw [toMul_nsmul, toMul_zero]; exact hQ _)
  set Y' : Submodule (ZMod 2) (Additive Q) := AddSubgroup.toZModSubmodule 2 Y.toAddSubgroup
  obtain ⟨Z, hZ⟩ := Submodule.exists_isCompl Y'
  let p : Q →* Q :=
    { toFun := fun q => Additive.toMul (Y'.projection Z hZ (Additive.ofMul q))
      map_one' := by
        change Additive.toMul (Y'.projection Z hZ 0) = 1
        rw [map_zero]
        rfl
      map_mul' := fun q q' => by
        change Additive.toMul (Y'.projection Z hZ (Additive.ofMul q + Additive.ofMul q')) = _
        rw [map_add]
        rfl }
  refine ⟨p, fun q => ?_, fun y hy => ?_⟩
  · exact Submodule.projection_apply_mem hZ (Additive.ofMul q)
  · change Additive.toMul (Y'.projection Z hZ (Additive.ofMul y)) = y
    rw [Submodule.projection_apply_of_mem_left hZ (show Additive.ofMul y ∈ Y' from hy)]
    rfl

section Average

variable {T : Type*} [Group T] [Fintype T] {Q : Type*} [CommGroup Q] [MulDistribMulAction T Q]

@[expose] def averageHom (p : Q →* Q) : Q →* Q where
  toFun q := ∏ t : T, t • p (t⁻¹ • q)
  map_one' := by simp
  map_mul' q q' := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [smul_mul', map_mul, smul_mul']

theorem averageHom_apply (p : Q →* Q) (q : Q) :
    averageHom (T := T) p q = ∏ t : T, t • p (t⁻¹ • q) :=
  rfl

theorem averageHom_smul (p : Q →* Q) (s : T) (q : Q) :
    averageHom (T := T) p (s • q) = s • averageHom (T := T) p q := by
  rw [averageHom_apply, averageHom_apply, Finset.smul_prod']
  refine Fintype.prod_equiv (Equiv.mulLeft s⁻¹) _ _ fun t => ?_
  simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, mul_smul, smul_inv_smul]

theorem averageHom_mem {p : Q →* Q} {Y : Subgroup Q} (hp : ∀ q, p q ∈ Y)
    (hY : ∀ (t : T), ∀ y ∈ Y, t • y ∈ Y) (q : Q) : averageHom (T := T) p q ∈ Y :=
  Subgroup.prod_mem _ fun t _ => hY t _ (hp _)

theorem averageHom_eq_self (hT : Odd (Fintype.card T)) (hQ : ∀ q : Q, q ^ 2 = 1)
    {p : Q →* Q} {Y : Subgroup Q} (hp : ∀ y ∈ Y, p y = y) (hY : ∀ (t : T), ∀ y ∈ Y, t • y ∈ Y)
    {y : Q} (hy : y ∈ Y) : averageHom (T := T) p y = y := by
  rw [averageHom_apply]
  have h : ∀ t : T, t • p (t⁻¹ • y) = y := fun t => by
    rw [hp _ (hY _ _ hy), smul_inv_smul]
  simp only [h, Finset.prod_const, Finset.card_univ]
  obtain ⟨k, hk⟩ := hT
  rw [hk, pow_succ, pow_mul, hQ, one_pow, one_mul]

end Average

theorem form_eq_zero_of_image {T : Type*} [Group T] [Fintype T] (hT : Odd (Fintype.card T))
    {Q Q' : Type*} [CommGroup Q] [CommGroup Q'] [MulDistribMulAction T Q]
    [MulDistribMulAction T Q'] (hQ : ∀ q : Q, q ^ 2 = 1) (hQ' : ∀ q : Q', q ^ 2 = 1)
    (hB : ∀ B : Q → Q' → ZMod 2, (∀ q₁ q₂ q', B (q₁ * q₂) q' = B q₁ q' + B q₂ q') →
      (∀ q q₁' q₂', B q (q₁' * q₂') = B q q₁' + B q q₂') →
      (∀ (t : T) q q', B (t • q) (t • q') = B q q') → ∀ q q', B q q' = 0)
    {M : Type*} [Group M] (act : T → M → M) (W W' : Subgroup M)
    (hW : ∀ t, ∀ x ∈ W, act t x ∈ W) (hW' : ∀ t, ∀ y ∈ W', act t y ∈ W')
    (π : M → Q) (π' : M → Q') (hπ : ∀ x ∈ W, ∀ x' ∈ W, π (x * x') = π x * π x')
    (hπ' : ∀ y ∈ W', ∀ y' ∈ W', π' (y * y') = π' y * π' y')
    (hπT : ∀ t, ∀ x ∈ W, π (act t x) = t • π x) (hπT' : ∀ t, ∀ y ∈ W', π' (act t y) = t • π' y)
    (b : M → M → ZMod 2) (hb₁ : ∀ x ∈ W, ∀ x' ∈ W, ∀ y ∈ W', b (x * x') y = b x y + b x' y)
    (hb₂ : ∀ x ∈ W, ∀ y ∈ W', ∀ y' ∈ W', b x (y * y') = b x y + b x y')
    (hb₀ : ∀ x ∈ W, ∀ y ∈ W', π x = 1 → b x y = 0)
    (hb₀' : ∀ x ∈ W, ∀ y ∈ W', π' y = 1 → b x y = 0)
    (hbT : ∀ t, ∀ x ∈ W, ∀ y ∈ W', b (act t x) (act t y) = b x y) :
    ∀ x ∈ W, ∀ y ∈ W', b x y = 0 := by
  classical
  have hπ1 : π 1 = 1 := by
    have h := hπ 1 W.one_mem 1 W.one_mem
    rwa [mul_one, left_eq_mul] at h
  have hπ1' : π' 1 = 1 := by
    have h := hπ' 1 W'.one_mem 1 W'.one_mem
    rwa [mul_one, left_eq_mul] at h
  have hπinv : ∀ x ∈ W, π x⁻¹ = (π x)⁻¹ := fun x hx => by
    have h := hπ x hx x⁻¹ (W.inv_mem hx)
    rw [mul_inv_cancel, hπ1] at h
    exact (eq_inv_of_mul_eq_one_right h.symm)
  have hπinv' : ∀ y ∈ W', π' y⁻¹ = (π' y)⁻¹ := fun y hy => by
    have h := hπ' y hy y⁻¹ (W'.inv_mem hy)
    rw [mul_inv_cancel, hπ1'] at h
    exact (eq_inv_of_mul_eq_one_right h.symm)
  let Y : Subgroup Q :=
    { carrier := {q | ∃ x ∈ W, π x = q}
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
        exact ⟨x * x', W.mul_mem hx hx', hπ x hx x' hx'⟩
      one_mem' := ⟨1, W.one_mem, hπ1⟩
      inv_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x⁻¹, W.inv_mem hx, hπinv x hx⟩ }
  let Y' : Subgroup Q' :=
    { carrier := {q | ∃ y ∈ W', π' y = q}
      mul_mem' := by
        rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
        exact ⟨y * y', W'.mul_mem hy hy', hπ' y hy y' hy'⟩
      one_mem' := ⟨1, W'.one_mem, hπ1'⟩
      inv_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨y⁻¹, W'.inv_mem hy, hπinv' y hy⟩ }
  have hY : ∀ (t : T), ∀ q ∈ Y, t • q ∈ Y := by
    rintro t _ ⟨x, hx, rfl⟩
    exact ⟨act t x, hW t x hx, hπT t x hx⟩
  have hY' : ∀ (t : T), ∀ q ∈ Y', t • q ∈ Y' := by
    rintro t _ ⟨y, hy, rfl⟩
    exact ⟨act t y, hW' t y hy, hπT' t y hy⟩
  have hdep : ∀ x ∈ W, ∀ x₁ ∈ W, π x = π x₁ → ∀ y ∈ W', b x y = b x₁ y := by
    intro x hx x₁ hx₁ he y hy
    have hk : x⁻¹ * x₁ ∈ W := W.mul_mem (W.inv_mem hx) hx₁
    have hk1 : π (x⁻¹ * x₁) = 1 := by
      rw [hπ _ (W.inv_mem hx) _ hx₁, hπinv x hx, he, inv_mul_cancel]
    have h := hb₁ x hx (x⁻¹ * x₁) hk y hy
    rw [mul_inv_cancel_left, hb₀ _ hk y hy hk1, add_zero] at h
    exact h.symm
  have hdep' : ∀ x ∈ W, ∀ y ∈ W', ∀ y₁ ∈ W', π' y = π' y₁ → b x y = b x y₁ := by
    intro x hx y hy y₁ hy₁ he
    have hk : y⁻¹ * y₁ ∈ W' := W'.mul_mem (W'.inv_mem hy) hy₁
    have hk1 : π' (y⁻¹ * y₁) = 1 := by
      rw [hπ' _ (W'.inv_mem hy) _ hy₁, hπinv' y hy, he, inv_mul_cancel]
    have h := hb₂ x hx y hy (y⁻¹ * y₁) hk
    rw [mul_inv_cancel_left, hb₀' x hx _ hk hk1, add_zero] at h
    exact h.symm
  let L : Q → M := fun q => if h : ∃ x ∈ W, π x = q then h.choose else 1
  let L' : Q' → M := fun q => if h : ∃ y ∈ W', π' y = q then h.choose else 1
  have hL : ∀ q ∈ Y, L q ∈ W ∧ π (L q) = q := fun q hq => by
    have h : ∃ x ∈ W, π x = q := hq
    simp only [L, h, dite_true]
    exact h.choose_spec
  have hL' : ∀ q ∈ Y', L' q ∈ W' ∧ π' (L' q) = q := fun q hq => by
    have h : ∃ y ∈ W', π' y = q := hq
    simp only [L', h, dite_true]
    exact h.choose_spec
  obtain ⟨p, hpY, hpid⟩ := exists_retraction_of_sq_eq_one hQ Y
  obtain ⟨p', hpY', hpid'⟩ := exists_retraction_of_sq_eq_one hQ' Y'
  set P := averageHom (T := T) p
  set P' := averageHom (T := T) p'
  have hPY : ∀ q, P q ∈ Y := averageHom_mem hpY hY
  have hPY' : ∀ q, P' q ∈ Y' := averageHom_mem hpY' hY'
  let B : Q → Q' → ZMod 2 := fun q q' => b (L (P q)) (L' (P' q'))
  have hB0 := hB B ?_ ?_ ?_
  · intro x hx y hy
    have h1 : π x ∈ Y := ⟨x, hx, rfl⟩
    have h1' : π' y ∈ Y' := ⟨y, hy, rfl⟩
    have hPx : P (π x) = π x := averageHom_eq_self hT hQ hpid hY h1
    have hPy : P' (π' y) = π' y := averageHom_eq_self hT hQ' hpid' hY' h1'
    have h := hB0 (π x) (π' y)
    change b (L (P (π x))) (L' (P' (π' y))) = 0 at h
    rw [hPx, hPy] at h
    obtain ⟨hLx, hLx'⟩ := hL _ h1
    obtain ⟨hLy, hLy'⟩ := hL' _ h1'
    rw [hdep x hx _ hLx hLx'.symm y hy, hdep' _ hLx y hy _ hLy hLy'.symm]
    exact h
  · intro q₁ q₂ q'
    change b (L (P (q₁ * q₂))) _ = b (L (P q₁)) _ + b (L (P q₂)) _
    obtain ⟨h₁, h₁'⟩ := hL _ (hPY q₁)
    obtain ⟨h₂, h₂'⟩ := hL _ (hPY q₂)
    obtain ⟨h₁₂, h₁₂'⟩ := hL _ (hPY (q₁ * q₂))
    obtain ⟨hz, -⟩ := hL' _ (hPY' q')
    rw [hdep _ h₁₂ _ (W.mul_mem h₁ h₂) (by rw [h₁₂', hπ _ h₁ _ h₂, h₁', h₂', map_mul]) _ hz,
      hb₁ _ h₁ _ h₂ _ hz]
  · intro q q₁' q₂'
    change b _ (L' (P' (q₁' * q₂'))) = b _ (L' (P' q₁')) + b _ (L' (P' q₂'))
    obtain ⟨h₁, h₁'⟩ := hL' _ (hPY' q₁')
    obtain ⟨h₂, h₂'⟩ := hL' _ (hPY' q₂')
    obtain ⟨h₁₂, h₁₂'⟩ := hL' _ (hPY' (q₁' * q₂'))
    obtain ⟨hz, -⟩ := hL _ (hPY q)
    rw [hdep' _ hz _ h₁₂ _ (W'.mul_mem h₁ h₂) (by rw [h₁₂', hπ' _ h₁ _ h₂, h₁', h₂', map_mul]),
      hb₂ _ hz _ h₁ _ h₂]
  · intro t q q'
    change b (L (P (t • q))) (L' (P' (t • q'))) = b (L (P q)) (L' (P' q'))
    obtain ⟨h₁, h₁'⟩ := hL _ (hPY q)
    obtain ⟨h₂, h₂'⟩ := hL _ (hPY (t • q))
    obtain ⟨h₃, h₃'⟩ := hL' _ (hPY' q')
    obtain ⟨h₄, h₄'⟩ := hL' _ (hPY' (t • q'))
    rw [hdep _ h₂ _ (hW t _ h₁) (by rw [h₂', hπT t _ h₁, h₁', averageHom_smul]) _ h₄,
      hdep' _ (hW t _ h₁) _ h₄ _ (hW' t _ h₃) (by rw [h₄', hπT' t _ h₃, h₃', averageHom_smul]),
      hbT t _ h₁ _ h₃]

end CFSG.LocalAnalysis.ComponentInitial
