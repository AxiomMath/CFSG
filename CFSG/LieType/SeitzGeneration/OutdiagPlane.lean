module

public import CFSG.LieType.SeitzGeneration.OutdiagHeis
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

section Scalars

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def NonScalarGL (g : GL (Fin n) F) : Prop :=
  ∀ c : Fˣ, g ≠ Matrix.GeneralLinearGroup.scalar (Fin n) c

theorem coe_scalarGL (c : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (c : F) • 1 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul,
    Matrix.mul_one]

theorem exists_scalarGL_of_coe_eq (hn : 0 < n) {g : GL (Fin n) F} {c : F}
    (h : (g : Matrix (Fin n) (Fin n) F) = c • 1) :
    ∃ u : Fˣ, g = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
  have hc : c ≠ 0 := by
    rintro rfl
    have h1 : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * g = 1 := Units.inv_mul g
    rw [h, zero_smul, Matrix.mul_zero] at h1
    exact zero_ne_one (congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩)
  refine ⟨Units.mk0 c hc, Units.ext ?_⟩
  rw [h, coe_scalarGL]
  rfl

theorem scalarGL_eq_one_iff (hn : 0 < n) {c : Fˣ} :
    Matrix.GeneralLinearGroup.scalar (Fin n) c = (1 : GL (Fin n) F) ↔ c = 1 := by
  constructor
  · intro h
    have h1 := congrArg Units.val h
    rw [coe_scalarGL, Units.val_one] at h1
    have := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
    simpa using this
  · rintro rfl; exact map_one _

theorem nonScalarGL_lines_of_quasi {x y : GL (Fin n) F} {w : Fˣ}
    (hyx : y * x = Matrix.GeneralLinearGroup.scalar (Fin n) w * (x * y)) (hn : 0 < n)
    (hw1 : w ≠ 1) :
    NonScalarGL x ∧ NonScalarGL y ∧ NonScalarGL (x * y) ∧ NonScalarGL (x * y ^ 2) := by
  have key : ¬ Commute x y := by
    intro hc
    apply hw1
    rw [← scalarGL_eq_one_iff hn]
    have h1 : y * x = x * y := hc.symm.eq
    rw [h1] at hyx
    exact mul_eq_right.1 hyx.symm
  have hs := fun (c : Fˣ) (g : GL (Fin n) F) => commute_scalarGL c g
  refine ⟨fun c hc => key ?_, fun c hc => key ?_, fun c hc => key ?_, fun c hc => key ?_⟩
  · rw [hc]; exact hs c y
  · rw [hc]; exact (hs c x).symm
  · have : x = Matrix.GeneralLinearGroup.scalar (Fin n) c * y⁻¹ := eq_mul_inv_of_mul_eq hc
    rw [this]
    exact Commute.mul_left (hs c y) (Commute.inv_left (Commute.refl y))
  · have : x = Matrix.GeneralLinearGroup.scalar (Fin n) c * (y ^ 2)⁻¹ := eq_mul_inv_of_mul_eq hc
    rw [this]
    exact Commute.mul_left (hs c y) (((Commute.refl y).pow_left 2).inv_left)

end Scalars

section Main

variable {F : Type} [Field F]

theorem det_scalarGL_three (c : Fˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) =
      c ^ 3 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_scalarGL, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_fin, Units.val_pow_eq_pow_val]

theorem cube_eq_one_of_quasi_commute {x y : GL (Fin 3) F} {w : Fˣ}
    (hyx : y * x = Matrix.GeneralLinearGroup.scalar (Fin 3) w * (x * y)) : w ^ 3 = 1 := by
  have h := congrArg Matrix.GeneralLinearGroup.det hyx
  rw [map_mul, map_mul, map_mul, det_scalarGL_three, mul_comm (Matrix.GeneralLinearGroup.det y)]
    at h
  exact mul_eq_right.1 h.symm

variable [Finite F]

theorem pair_of_normalized (hcore : OuterHeisCore) (hF3 : 3 ∣ Nat.card F - 1)
    (h4 : 4 < Nat.card F) (H : Subgroup (GL (Fin 3) F))
    (hH : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H)
    {x g : GL (Fin 3) F} (hx : x ∈ H) (hg : g ∈ H) {w α s : Fˣ}
    (hrel : g * x = Matrix.GeneralLinearGroup.scalar (Fin 3) w * (x * g)) (hw3 : w ^ 3 = 1)
    (hw1 : w ≠ 1) (hx3 : x ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) α)
    (hg3 : g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (s ^ 3)) :
    ∃ x' ∈ H, ∃ y' ∈ H, NonScalarGL x' ∧ NonScalarGL y' ∧ NonScalarGL (x' * y') ∧
      NonScalarGL (x' * y' ^ 2) ∧ Subgroup.closure (planeFix x' y') = ⊤ := by
  refine ⟨x, hx, Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * g, H.mul_mem (hH _) hg, ?_⟩
  have hrel' : (Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * g) * x =
      Matrix.GeneralLinearGroup.scalar (Fin 3) w *
        (x * (Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * g)) := by
    calc (Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * g) * x
        = Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * (g * x) := mul_assoc _ _ _
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) w * (x * g)) := by rw [hrel]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) w *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * (x * g)) := by
        rw [← mul_assoc, (commute_scalarGL s⁻¹
          (Matrix.GeneralLinearGroup.scalar (Fin 3) w)).eq, mul_assoc]
      _ = _ := by
        congr 1
        rw [← mul_assoc, ← mul_assoc, (commute_scalarGL s⁻¹ x).eq]
  have hy3 : (Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * g) ^ 3 = 1 := by
    rw [Commute.mul_pow (commute_scalarGL s⁻¹ g) 3, ← map_pow, hg3, ← map_mul, ← mul_pow,
      inv_mul_cancel, one_pow, map_one]
  have hyxM : ((Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * g : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) * x = (w : F) • ((x : Matrix (Fin 3) (Fin 3) F) *
        ((Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * g : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F)) := by
    have h := congrArg Units.val hrel'
    rw [Units.val_mul, Units.val_mul (Matrix.GeneralLinearGroup.scalar (Fin 3) w), coe_scalarGL,
      Matrix.smul_mul, Matrix.one_mul, ← Units.val_mul] at h
    exact h
  have hy3M : ((Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * g : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hy3, Units.val_one]
  have hx3M : (x : Matrix (Fin 3) (Fin 3) F) ^ 3 = (α : F) • 1 := by
    rw [← Units.val_pow_eq_pow_val, hx3, coe_scalarGL]
  have hw3F : (w : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hw3, Units.val_one]
  have hw1F : (w : F) ≠ 1 := fun h => hw1 (Units.val_eq_one.1 h)
  have hwF : (w : F) ^ 2 + w + 1 = 0 := by
    have h1 : ((w : F) - 1) * ((w : F) ^ 2 + w + 1) = 0 := by linear_combination hw3F
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hw1F)
  obtain ⟨hn1, hn2, hn3, hn4⟩ := nonScalarGL_lines_of_quasi hrel' (by norm_num) hw1
  exact ⟨hn1, hn2, hn3, hn4, closure_planeFix_heis_normal hcore hF3 h4 hwF hw1F α.ne_zero hyxM
    hy3M hx3M⟩

theorem exists_pair_closure_planeFix (hcore : OuterHeisCore) (hF3 : 3 ∣ Nat.card F - 1)
    (h4 : 4 < Nat.card F) (hζ : ∃ ζ : F, IsPrimitiveRoot ζ 3) (H : Subgroup (GL (Fin 3) F))
    (hH : ∀ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ H) {x y : GL (Fin 3) F}
    (hx : x ∈ H) (hy : y ∈ H) {ω α β : Fˣ}
    (hyx : y * x = Matrix.GeneralLinearGroup.scalar (Fin 3) ω * (x * y))
    (hx3 : x ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) α)
    (hy3 : y ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) β)
    (hind : ∀ a b : ℕ, (∃ c : Fˣ, x ^ a * y ^ b = Matrix.GeneralLinearGroup.scalar (Fin 3) c) →
      3 ∣ a ∧ 3 ∣ b) :
    ∃ x' ∈ H, ∃ y' ∈ H, NonScalarGL x' ∧ NonScalarGL y' ∧ NonScalarGL (x' * y') ∧
      NonScalarGL (x' * y' ^ 2) ∧ Subgroup.closure (planeFix x' y') = ⊤ := by
  have hω3 := cube_eq_one_of_quasi_commute hyx
  have hx3M : ((x ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (α : F) • 1 := by
    rw [hx3, coe_scalarGL]
  have hy3M : ((y ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (β : F) • 1 := by
    rw [hy3, coe_scalarGL]
  by_cases hω1 : ω = 1
  · subst hω1
    have hxy : x * y = y * x := by rw [map_one, one_mul] at hyx; exact hyx.symm
    have hind' : ∀ a b : ℕ,
        (∃ c : F, ((x ^ a * y ^ b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = c • 1) →
          3 ∣ a ∧ 3 ∣ b := fun a b ⟨c, hc⟩ => hind a b (exists_scalarGL_of_coe_eq (by norm_num) hc)
    refine ⟨x, hx, y, hy, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc; have := hind 1 0 ⟨c, by simpa using hc⟩; omega
    · intro c hc; have := hind 0 1 ⟨c, by simpa using hc⟩; omega
    · intro c hc; have := hind 1 1 ⟨c, by simpa using hc⟩; omega
    · intro c hc; have := hind 1 2 ⟨c, by simpa using hc⟩; omega
    · exact closure_planeFix_abelian hF3 hζ hxy α.ne_zero β.ne_zero hx3M hy3M hind'
  · have hw : ∀ g, Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) ω) g :=
      fun g => commute_scalarGL ω g
    have hw3 : (Matrix.GeneralLinearGroup.scalar (Fin 3) ω : GL (Fin 3) F) ^ 3 = 1 := by
      rw [← map_pow, hω3, map_one]
    obtain ⟨a, b, s, hs0, hab, hs3⟩ := exists_cube_line hF3 hw hw3 hyx α.ne_zero β.ne_zero hx3M
      hy3M
    obtain ⟨su, hsu⟩ : ∃ u : Fˣ, (u : F) = s := ⟨Units.mk0 s hs0, rfl⟩
    have hg3 : (x ^ a * y ^ b) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (su ^ 3) := by
      apply Units.ext
      rw [hs3, coe_scalarGL, Units.val_pow_eq_pow_val, hsu]
    have hxc := fun (c : Fˣ) => (commute_scalarGL (F := F) (n := 3) c x).eq
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [pow_one, pow_zero, mul_one] at hg3
      refine pair_of_normalized hcore hF3 h4 H hH hy hx (w := ω⁻¹) (α := β) (s := su) ?_ ?_ ?_
        hy3 hg3
      · rw [hyx, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      · rw [inv_pow, hω3, inv_one]
      · exact inv_ne_one.2 hω1
    · simp only [pow_zero, one_mul, pow_one] at hg3
      exact pair_of_normalized hcore hF3 h4 H hH hx hy (w := ω) (α := α) (s := su) hyx hω3 hω1
        hx3 hg3
    · simp only [pow_one] at hg3
      refine pair_of_normalized hcore hF3 h4 H hH hx (H.mul_mem hx hy) (w := ω) (α := α)
        (s := su) ?_ hω3 hω1 hx3 hg3
      calc x * y * x = x * (y * x) := mul_assoc _ _ _
        _ = x * (Matrix.GeneralLinearGroup.scalar (Fin 3) ω * (x * y)) := by rw [hyx]
        _ = _ := by rw [← mul_assoc, ← hxc ω, mul_assoc]
    · simp only [pow_one] at hg3
      have h2 : y ^ 2 * x = Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2) * (x * y ^ 2) := by
        rw [map_pow]; exact pow_mul_eq_of_quasi_commute hw hyx 2
      have hω2 : ω ^ 2 ≠ 1 := by
        intro h
        apply hω1
        calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
          _ = 1 := by rw [hω3, h, inv_one, one_mul]
      refine pair_of_normalized hcore hF3 h4 H hH hx (H.mul_mem hx (H.pow_mem hy 2)) (w := ω ^ 2)
        (α := α) (s := su) ?_ (by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]) hω2 hx3 hg3
      calc x * y ^ 2 * x = x * (y ^ 2 * x) := mul_assoc _ _ _
        _ = x * (Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2) * (x * y ^ 2)) := by rw [h2]
        _ = _ := by rw [← mul_assoc, ← hxc (ω ^ 2), mul_assoc]

end Main

end CFSG.LieType.SeitzGeneration
