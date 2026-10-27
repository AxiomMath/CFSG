module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.L364Lin
public import CFSG.Open.StatedDefs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34Mat

open Matrix CFSG.Open

variable {K : Type} [Field K]

theorem scalar_mul_eq_smul (u : K) (M : Matrix (Fin 3) (Fin 3) K) :
    Matrix.scalar (Fin 3) u * M = u • M := by
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem commute_transvection_of_conj (h3 : (3 : K) ≠ 0) {G Gi : Matrix (Fin 3) (Fin 3) K}
    (h1 : G * Gi = 1) (h2 : Gi * G = 1) {i j : Fin 3} (hij : i ≠ j) (c : K) {u : K}
    (h : G * transvection i j c * Gi = u • transvection i j c) :
    Commute (transvection i j c) G := by
  have htr : trace (transvection i j c) = 3 := by
    rw [transvection, trace_add, trace_one, trace_single_eq_of_ne i j c hij]
    simp
  have h4 : trace (G * transvection i j c * Gi) = trace (transvection i j c) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [h, trace_smul, htr, smul_eq_mul] at h4
  have hu : u = 1 := by
    apply mul_right_cancel₀ h3
    rw [h4, one_mul]
  rw [hu, one_smul] at h
  show transvection i j c * G = G * transvection i j c
  calc transvection i j c * G = G * transvection i j c * Gi * G := by rw [h]
    _ = G * transvection i j c := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem exists_unit_of_eq_scalar (g : GL (Fin 3) K) (a : K)
    (h : (g : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) a) :
    ∃ u : Kˣ, g = Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h0 : (g : Matrix (Fin 3) (Fin 3) K) = 0 := by rw [h]; simp
    have h1 : (g * g⁻¹ : GL (Fin 3) K) = 1 := mul_inv_cancel g
    have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [Units.val_mul, h0, Matrix.zero_mul, Units.val_one] at h2
    exact zero_ne_one h2
  refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, h]
  rfl

theorem exists_scalar_of_conj_scalar (h3 : (3 : K) ≠ 0) (γ : GL (Fin 3) K)
    (h : ∀ x : GL (Fin 3) K, (x : Matrix (Fin 3) (Fin 3) K).det = 1 →
      ∃ u : Kˣ, γ * x * γ⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) u * x) :
    ∃ c : Kˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  classical
  have hsc : (γ : Matrix (Fin 3) (Fin 3) K) ∈ Set.range (Matrix.scalar (Fin 3)) := by
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    have hdet : (t.toMatrix).det = 1 := det_transvection_of_ne t.i t.j t.hij t.c
    let x : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix
      (by rw [hdet]; exact one_ne_zero)
    have hx : (x : Matrix (Fin 3) (Fin 3) K) = t.toMatrix := rfl
    obtain ⟨u, hu⟩ := h x (by rw [hx]; exact hdet)
    have hu' := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hu
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hx,
      scalar_mul_eq_smul] at hu'
    exact commute_transvection_of_conj h3 (by rw [← Units.val_mul, mul_inv_cancel]; rfl)
      (by rw [← Units.val_mul, inv_mul_cancel]; rfl) t.hij t.c (u := (u : K)) hu'
  obtain ⟨a, ha⟩ := hsc
  exact exists_unit_of_eq_scalar γ a ha.symm

section Cyclic

open CFSG.HardMathSupport.Dickson.Sec6.Up34Lin

noncomputable abbrev glToEnd : GL (Fin 3) K ≃* (Module.End K (Fin 3 → K))ˣ :=
  Matrix.GeneralLinearGroup.toLin

theorem coe_glToEnd_scalar (u : Kˣ) :
    ((glToEnd (Matrix.GeneralLinearGroup.scalar (Fin 3) u) : (Module.End K (Fin 3 → K))ˣ) :
      Module.End K (Fin 3 → K)) = (u : K) • (1 : Module.End K (Fin 3 → K)) := by
  ext v i
  simp [glToEnd, Matrix.GeneralLinearGroup.coe_toLin, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem isCyclic_of_three_subgroup_gl [Finite K] (hK : Nat.card K % 3 = 1) (g : GL (Fin 3) K)
    (c : Kˣ) (hg3 : g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hg : ∀ a : Kˣ, g ≠ Matrix.GeneralLinearGroup.scalar (Fin 3) a)
    {D : Subgroup (GL (Fin 3) K)} (hD : ⁅D, D⁆ = D) (hDg : ∀ d ∈ D, d * g = g * d)
    {R : Type} [Group R] [Finite R] (ι : R →* GL (Fin 3) K) (hι : Function.Injective ι)
    (hR : ∀ r, ι r ∈ D) (hR3 : IsPGroup 3 R) : IsCyclic R := by
  classical
  have hV : Module.finrank K (Fin 3 → K) = 3 := by simp
  let ρ : GL (Fin 3) K ≃* (Module.End K (Fin 3 → K))ˣ := glToEnd
  let T : Module.End K (Fin 3 → K) := ((ρ g : (Module.End K (Fin 3 → K))ˣ) :
    Module.End K (Fin 3 → K))
  have hT3 : T * T * T = (c : K) • (1 : Module.End K (Fin 3 → K)) := by
    have h1 : ((ρ (g ^ 3) : (Module.End K (Fin 3 → K))ˣ) : Module.End K (Fin 3 → K)) = T * T * T := by
      rw [map_pow, pow_three', Units.val_mul, Units.val_mul]
    rw [← h1, hg3]
    exact coe_glToEnd_scalar c
  have hT : ∀ a : K, T ≠ a • (1 : Module.End K (Fin 3 → K)) := by
    intro a ha
    have hg' : (g : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) a := by
      ext i j
      have := congrArg (fun f : Module.End K (Fin 3 → K) => f (Pi.single j 1) i) ha
      simpa [T, ρ, glToEnd, Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVec,
        Matrix.scalar_apply, Matrix.diagonal_apply, Pi.single_apply, dotProduct,
        Matrix.mulVec_single] using this
    obtain ⟨u, hu⟩ := exists_unit_of_eq_scalar g a hg'
    exact hg u hu
  have hD' : ⁅D.map ρ.toMonoidHom, D.map ρ.toMonoidHom⁆ = D.map ρ.toMonoidHom := by
    rw [← Subgroup.map_commutator, hD]
  have hDT' : ∀ d ∈ D.map ρ.toMonoidHom,
      (d : Module.End K (Fin 3 → K)) * T = T * d := by
    rintro _ ⟨d₀, hd₀, rfl⟩
    have := hDg d₀ hd₀
    show ((ρ d₀ : (Module.End K (Fin 3 → K))ˣ) : Module.End K (Fin 3 → K)) *
      ((ρ g : (Module.End K (Fin 3 → K))ˣ) : Module.End K (Fin 3 → K)) =
        ((ρ g : (Module.End K (Fin 3 → K))ˣ) : Module.End K (Fin 3 → K)) *
          ((ρ d₀ : (Module.End K (Fin 3 → K))ˣ) : Module.End K (Fin 3 → K))
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, this]
  let f : R →* (Module.End K (Fin 3 → K))ˣ := ρ.toMonoidHom.comp ι
  have hf : Function.Injective f := ρ.injective.comp hι
  have hfS : IsPGroup 3 f.range := hR3.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  haveI : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hSD : f.range ≤ D.map ρ.toMonoidHom := by
    rintro _ ⟨r, rfl⟩
    exact ⟨ι r, hR r, rfl⟩
  have hcyc := three_subgroup_cyclic hK hV T (c : K) c.ne_zero hT3 hT hD' hDT' f.range hSD hfS
  exact isCyclic_of_injective f.rangeRestrict (by
    intro a b hab
    exact hf (congrArg Subtype.val hab))

end Cyclic

end CFSG.HardMathSupport.Dickson.Sec6.Up34Mat
