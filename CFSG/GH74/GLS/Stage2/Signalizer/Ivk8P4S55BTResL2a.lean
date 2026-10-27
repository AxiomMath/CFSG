module

public import CFSG.GH74.GLS.IVK.L2.BorelPGL
public import CFSG.GH74.GLS.IVK.L2.BorelSylow

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResL2

open CFSG.PSL2Table CFSG.GH74.GLS.IVK.L2Borel CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem bor_mul (a a' : Fˣ) (b b' : F) : bor a b * bor a' b' = bor (a * a') (a * b' + b) := by
  rw [bor, bor, bor, ← map_mul]
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem bor_eq_one_iff (a : Fˣ) (b : F) : bor a b = 1 ↔ a = 1 ∧ b = 0 := by
  constructor
  · intro h
    rw [bor, Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
    obtain ⟨u, hu⟩ := h
    have e00 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 0 0) hu
    have e01 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 0 1) hu
    have e11 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 1 1) hu
    simp at e00 e01 e11
    refine ⟨Units.ext ?_, e01.symm⟩
    rw [← e00, e11, Units.val_one]
  · rintro ⟨rfl, rfl⟩
    rw [bor, Matrix.ProjGenLinGroup.mk_eq_one]
    have : borGL (1 : Fˣ) (0 : F) = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [this]
    exact Subgroup.one_mem _

theorem bor_inv_zero (a : Fˣ) : (bor a 0)⁻¹ = bor a⁻¹ 0 := by
  rw [inv_eq_iff_mul_eq_one, bor_mul, (bor_eq_one_iff _ _).mpr]
  exact ⟨by group, by simp⟩

theorem exists_eq_bor_of_normalizes {W : Subgroup PSL(2, F)}
    (hWU : W ≤ unipotent F) (hW : W ≠ ⊥) {g : PGL(2, F)}
    (hg : ∀ w ∈ W, ∃ w' ∈ W, g * Matrix.ProjectiveSpecialLinearGroup.toPGL w * g⁻¹ =
      Matrix.ProjectiveSpecialLinearGroup.toPGL w') :
    ∃ (a : Fˣ) (b : F), g = bor a b := by
  obtain ⟨⟨w, hwW⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hW
  obtain ⟨t, ht⟩ := (mem_unipotent_iff_exists w).mp (hWU hwW)
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hw1
    apply Subtype.ext
    change w = 1
    rw [ht, unip_zero, map_one]
  obtain ⟨w', hw'W, hw'⟩ := hg w hwW
  obtain ⟨s, hs⟩ := (mem_unipotent_iff_exists w').mp (hWU hw'W)
  set τ : Fˣ := Units.mk0 t ht0 with hτ
  have hconj : bor τ 0 * Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip 1)) *
      (bor τ 0)⁻¹ = Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip t)) := by
    rw [bor_conj_unip, hτ, Units.val_mk0, mul_one]
  have key : (g * bor τ 0) * Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip 1)) *
      (g * bor τ 0)⁻¹ = Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip s)) := by
    rw [mul_inv_rev, show g * bor τ 0 * Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip 1)) *
      ((bor τ 0)⁻¹ * g⁻¹) = g * (bor τ 0 *
        Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip 1)) * (bor τ 0)⁻¹) * g⁻¹ by group,
      hconj, ← ht, hw', hs]
  obtain ⟨a, b, hab⟩ := exists_eq_bor key
  refine ⟨a * τ⁻¹, b, ?_⟩
  have : g = bor a b * (bor τ 0)⁻¹ := by rw [← hab]; group
  rw [this, bor_inv_zero, bor_mul, mul_zero, zero_add]

theorem units_eq_one_or_neg_one {a : Fˣ} (h : a * a = 1) : a = 1 ∨ a = -1 := by
  have h' : ((a : F) - 1) * ((a : F) + 1) = 0 := by
    have := congrArg Units.val h
    simp only [Units.val_mul, Units.val_one] at this
    linear_combination this
  rcases mul_eq_zero.mp h' with h1 | h1
  · left
    exact Units.ext (by simpa [sub_eq_zero] using h1)
  · right
    exact Units.ext (by simp [eq_neg_iff_add_eq_zero.mpr h1])

theorem bor_eq_of_involutions (h2 : (2 : F) ≠ 0) {a a' : Fˣ} {b b' : F}
    (h : bor a b * bor a b = 1) (h' : bor a' b' * bor a' b' = 1)
    (hp : bor a b * bor a' b' * (bor a b * bor a' b') = 1) (h1 : bor a b ≠ 1)
    (h1' : bor a' b' ≠ 1) : bor a b = bor a' b' := by
  have hneg : ∀ {c : Fˣ} {d : F}, bor c d * bor c d = 1 → bor c d ≠ 1 → c = -1 := by
    intro c d hc hc1
    rw [bor_mul, bor_eq_one_iff] at hc
    rcases units_eq_one_or_neg_one hc.1 with rfl | rfl
    · exfalso
      apply hc1
      rw [bor_eq_one_iff]
      refine ⟨rfl, ?_⟩
      have h0 : (2 : F) * d = 0 := by
        have := hc.2
        simp only [Units.val_one, one_mul] at this
        linear_combination this
      exact (mul_eq_zero.mp h0).resolve_left h2
    · rfl
  obtain rfl := hneg h h1
  obtain rfl := hneg h' h1'
  rw [bor_mul, bor_mul, bor_eq_one_iff] at hp
  have hbb : b = b' := by
    have h0 : (2 : F) * (b - b') = 0 := by
      have := hp.2
      simp only [Units.val_mul, Units.val_neg, Units.val_one] at this
      linear_combination this
    have := (mul_eq_zero.mp h0).resolve_left h2
    exact sub_eq_zero.mp this
  rw [hbb]

theorem eq_of_right_eq_one [Finite F] {p n : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ n)
    (h2 : (2 : F) ≠ 0) {W : Subgroup PSL(2, F)} (hW : W ≠ ⊥) (hWp : IsPGroup p ↥W)
    {x₁ x₂ : PGammaL2 F} (hn₁ : ∀ w ∈ W, semilinearAction F x₁ w ∈ W)
    (hn₂ : ∀ w ∈ W, semilinearAction F x₂ w ∈ W) (hr₁ : x₁.right = 1) (hr₂ : x₂.right = 1)
    (h₁ : x₁ * x₁ = 1) (h₂ : x₂ * x₂ = 1) (h₁₂ : x₁ * x₂ * (x₁ * x₂) = 1) (hne₁ : x₁ ≠ 1)
    (hne₂ : x₂ ≠ 1) : x₁ = x₂ := by
  have hx : ∀ {x : PGammaL2 F}, x.right = 1 → x = SemidirectProduct.inl x.left := fun {x} hr => by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x, hr, map_one, mul_one]
  obtain ⟨Q, hWQ⟩ := hWp.exists_le_sylow
  obtain ⟨c, hc⟩ := exists_conj_eq_unipotent hF Q
  set W₀ : Subgroup PSL(2, F) := W.map (MulAut.conj c⁻¹).toMonoidHom with hW₀
  have hW₀U : W₀ ≤ unipotent F := by
    rintro _ ⟨w, hw, rfl⟩
    have hwQ : w ∈ (unipotent F).map (MulAut.conj c).toMonoidHom := hc ▸ hWQ hw
    obtain ⟨u, hu, rfl⟩ := hwQ
    simpa [MulAut.conj_apply, mul_assoc] using hu
  have hW₀ : W₀ ≠ ⊥ := by
    intro hbot
    apply hW
    rw [hW₀, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj c⁻¹).injective] at hbot
    exact hbot
  set C : PGL(2, F) := Matrix.ProjectiveSpecialLinearGroup.toPGL c with hC
  have hbor : ∀ {x : PGammaL2 F}, x.right = 1 → (∀ w ∈ W, semilinearAction F x w ∈ W) →
      ∃ (a : Fˣ) (b : F), C⁻¹ * x.left * C = bor a b := by
    intro x hr hn
    refine exists_eq_bor_of_normalizes hW₀U hW₀ (fun w₀ hw₀ => ?_)
    obtain ⟨w, hw, rfl⟩ := hw₀
    have hxw := hn w hw
    have h1 : semilinearAction F x = pglAction F x.left := by
      rw [hx hr, semilinearAction_inl]
      rfl
    have e1 : (MulAut.conj c⁻¹).toMonoidHom w = c⁻¹ * w * c := by simp
    refine ⟨c⁻¹ * semilinearAction F x w * c, ⟨_, hxw, by simp⟩, ?_⟩
    rw [e1, map_mul, map_mul, map_mul, map_mul, map_inv, h1, toPGL_pglAction, ← hC]
    group
  obtain ⟨a₁, b₁, hb₁⟩ := hbor hr₁ hn₁
  obtain ⟨a₂, b₂, hb₂⟩ := hbor hr₂ hn₂
  have hinl : ∀ {x : PGammaL2 F}, x.right = 1 → ∀ {y : PGammaL2 F}, y.right = 1 →
      (x * y).left = x.left * y.left := fun {x} hx' {y} _ => by
    rw [SemidirectProduct.mul_left, hx', map_one, MulAut.one_apply]
  have hconj : ∀ g h : PGL(2, F), (C⁻¹ * g * C) * (C⁻¹ * h * C) = C⁻¹ * (g * h) * C :=
    fun g h => by group
  have hsq : ∀ {x : PGammaL2 F}, x.right = 1 → x * x = 1 → x.left * x.left = 1 := by
    intro x hr h
    rw [← hinl hr hr, h]
    rfl
  have hne : ∀ {x : PGammaL2 F}, x.right = 1 → x ≠ 1 → x.left ≠ 1 := by
    intro x hr h h1
    apply h
    rw [hx hr, h1, map_one]
  have hr₁₂ : (x₁ * x₂).right = 1 := by rw [SemidirectProduct.mul_right, hr₁, hr₂, mul_one]
  have key := bor_eq_of_involutions h2
    (by rw [← hb₁, hconj, hsq hr₁ h₁]; group) (by rw [← hb₂, hconj, hsq hr₂ h₂]; group)
    (by rw [← hb₁, ← hb₂, hconj, hconj, ← hinl hr₁ hr₂, hsq hr₁₂ h₁₂]; group)
    (by
      rw [← hb₁]
      intro h
      apply hne hr₁ hne₁
      calc x₁.left = C * (C⁻¹ * x₁.left * C) * C⁻¹ := by group
        _ = 1 := by rw [h]; group)
    (by
      rw [← hb₂]
      intro h
      apply hne hr₂ hne₂
      calc x₂.left = C * (C⁻¹ * x₂.left * C) * C⁻¹ := by group
        _ = 1 := by rw [h]; group)
  rw [← hb₁, ← hb₂] at key
  have hl : x₁.left = x₂.left := by
    calc x₁.left = C * (C⁻¹ * x₁.left * C) * C⁻¹ := by group
      _ = C * (C⁻¹ * x₂.left * C) * C⁻¹ := by rw [key]
      _ = x₂.left := by group
  rw [hx hr₁, hx hr₂, hl]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResL2
