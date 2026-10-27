module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Structure

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure FormHyp (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (B : LinearMap.BilinForm (ZMod 2) V) : Prop where
  inv : ∀ (g : A5 × A5) (u u' : V), B (σ g u) (σ g u') = B u u'
  alt : ∀ u : V, B u u = 0
  nondeg : B.Nondegenerate

@[expose] def gramF (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (B : LinearMap.BilinForm (ZMod 2) V) (v : V)
    (x : A5) : ZMod 2 :=
  B v (σ (x, 1) v)

variable (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (B : LinearMap.BilinForm (ZMod 2) V) (v : V)

private lemma σ_mul_w (a b : A5) : σ (a, 1) (σ (b, 1) v) = σ (a * b, 1) v := by
  rw [← LinearEquiv.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

private lemma σ_comm_apply' (g h : A5 × A5) (hgh : g * h = h * g) (u : V) :
    σ g (σ h u) = σ h (σ g u) := by
  have h1 : σ g * σ h = σ h * σ g := by rw [← map_mul, ← map_mul, hgh]
  rw [← LinearEquiv.mul_apply, h1, LinearEquiv.mul_apply]

private lemma σ_one_apply : σ (1, 1) v = v := by
  change σ (1 : A5 × A5) v = v
  rw [map_one, LinearEquiv.one_eq_refl, LinearEquiv.refl_apply]

theorem gramF_one (hF : FormHyp σ B) : gramF σ B v 1 = 0 := by
  simp only [gramF]
  rw [σ_one_apply σ v, hF.alt v]

theorem B_w (hF : FormHyp σ B) (g h : A5) :
    B (σ (g, 1) v) (σ (h, 1) v) = gramF σ B v (g⁻¹ * h) := by
  calc B (σ (g, 1) v) (σ (h, 1) v)
      = B (σ (g⁻¹, 1) (σ (g, 1) v)) (σ (g⁻¹, 1) (σ (h, 1) v)) :=
        (hF.inv (g⁻¹, 1) (σ (g, 1) v) (σ (h, 1) v)).symm
    _ = B v (σ (g⁻¹ * h, 1) v) := by
        rw [σ_mul_w σ v g⁻¹ g, inv_mul_cancel, σ_mul_w σ v g⁻¹ h, σ_one_apply σ v]
    _ = gramF σ B v (g⁻¹ * h) := rfl

theorem σ_inl_w (x g : A5) : σ (x, 1) (σ (g, 1) v) = σ (x * g, 1) v :=
  σ_mul_w σ v x g

theorem σ_inr_w (hv : ∀ x : A5, σ (x, x) v = v) (y g : A5) :
    σ (1, y) (σ (g, 1) v) = σ (g * y⁻¹, 1) v := by
  have hcomm : σ (1, y) (σ (g, 1) v) = σ (g, 1) (σ (1, y) v) :=
    σ_comm_apply' σ (1, y) (g, 1) (by ext <;> simp [Prod.mk_mul_mk]) v
  rw [hcomm]
  have h1 : σ (1, y) v = σ (y⁻¹, 1) v := by
    have heq : ((1, y) : A5 × A5) = (y⁻¹, 1) * (y, y) := by
      ext <;> simp [Prod.mk_mul_mk]
    rw [heq, map_mul, LinearEquiv.mul_apply, hv y]
  rw [h1, σ_mul_w σ v g y⁻¹]

theorem σ_diag_w (hv : ∀ x : A5, σ (x, x) v = v) (x g : A5) :
    σ (x, x) (σ (g, 1) v) = σ (x * g * x⁻¹, 1) v := by
  have heq : ((x, x) : A5 × A5) = (x, 1) * (1, x) := by
    ext <;> simp [Prod.mk_mul_mk]
  rw [heq, map_mul, LinearEquiv.mul_apply, σ_inr_w σ v hv x g,
    σ_inl_w σ v x (g * x⁻¹), mul_assoc]

theorem gramF_conj (hF : FormHyp σ B) (hv : ∀ x : A5, σ (x, x) v = v) (x y : A5) :
    gramF σ B v (y * x * y⁻¹) = gramF σ B v x := by
  calc gramF σ B v (y * x * y⁻¹) = B v (σ (y * x * y⁻¹, 1) v) := rfl
    _ = B v (σ (y, y) (σ (x, 1) v)) := by rw [← σ_diag_w σ v hv y x]
    _ = B (σ (y, y) v) (σ (y, y) (σ (x, 1) v)) := by rw [hv y]
    _ = B v (σ (x, 1) v) := hF.inv (y, y) v (σ (x, 1) v)
    _ = gramF σ B v x := rfl

theorem span_w (hS : Swap.StdHyp σ) (hv : ∀ x : A5, σ (x, x) v = v) (hv0 : v ≠ 0) :
    Submodule.span (ZMod 2) (Set.range fun g : A5 => σ (g, 1) v) = ⊤ := by
  let U : Submodule (ZMod 2) V := Submodule.span (ZMod 2) (Set.range fun g : A5 => σ (g, 1) v)
  have hUinv : ∀ g : A5 × A5, ∀ u ∈ U, σ g u ∈ U := by
    intro g
    obtain ⟨x, y⟩ := g
    have hgen : ∀ h : A5, σ (x, y) (σ (h, 1) v) ∈ U := by
      intro h
      have heq : ((x, y) : A5 × A5) = (x, 1) * (1, y) := by
        ext <;> simp [Prod.mk_mul_mk]
      rw [heq, map_mul, LinearEquiv.mul_apply, σ_inr_w σ v hv y h,
        σ_inl_w σ v x (h * y⁻¹)]
      exact Submodule.subset_span ⟨x * (h * y⁻¹), rfl⟩
    intro u hu
    have hle : U ≤ U.comap (σ (x, y) : V →ₗ[ZMod 2] V) := by
      refine Submodule.span_le.mpr ?_
      rintro w ⟨h, rfl⟩
      exact hgen h
    exact hle hu
  rcases hS.irr U hUinv with hbot | htop
  · exfalso
    have hvU : v ∈ U := by
      rw [← σ_one_apply σ v]
      exact Submodule.subset_span ⟨1, rfl⟩
    rw [hbot] at hvU
    exact hv0 (by simpa using hvU)
  · exact htop

theorem gramF_ne_zero (hS : Swap.StdHyp σ) (hF : FormHyp σ B) (hv : ∀ x : A5, σ (x, x) v = v)
    (hv0 : v ≠ 0) : gramF σ B v ≠ 0 := by
  intro hgram
  have htop := span_w σ v hS hv hv0
  have hzero : ∀ u u' : V, B u u' = 0 := by
    intro u u'
    have hu : u ∈ Submodule.span (ZMod 2) (Set.range fun g : A5 => σ (g, 1) v) := by
      rw [htop]; trivial
    have hu' : u' ∈ Submodule.span (ZMod 2) (Set.range fun g : A5 => σ (g, 1) v) := by
      rw [htop]; trivial
    induction hu, hu' using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
        obtain ⟨g, rfl⟩ := hx
        obtain ⟨h, rfl⟩ := hy
        rw [B_w σ B v hF g h]
        exact congrFun hgram (g⁻¹ * h)
    | zero_left y hy => simp
    | zero_right x hx => simp
    | add_left x y z hx hy hz ihx ihy => simp [map_add, ihx, ihy]
    | add_right x y z hx hy hz ihx ihy => simp [map_add, ihx, ihy]
    | smul_left r x y hx hy ih => simp [map_smul, ih]
    | smul_right r x y hx hy ih => simp [map_smul, ih]
  exact hv0 (hF.nondeg.1 v fun u' => hzero v u')

theorem no_right_inverse (hS : Swap.StdHyp σ) (hF : FormHyp σ B) :
    ∀ (R C : Fin 9 → A5) (N : Matrix (Fin 9) (Fin 9) (ZMod 2)),
      (Matrix.of fun i j => gramF σ B v ((R i)⁻¹ * C j)) * N ≠ 1 := by
  intro R C N hGN
  haveI : Module.Finite (ZMod 2) V :=
    Module.finite_of_finrank_eq_succ (R := ZMod 2) (n := 7) (by rw [hS.finrank_eq])
  let u : Fin 9 → V := fun i => σ (R i, 1) v
  have hdep : ¬ LinearIndependent (ZMod 2) u := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, hS.finrank_eq] at hle
    omega
  obtain ⟨c, hcsum, hcne⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let G : Matrix (Fin 9) (Fin 9) (ZMod 2) :=
    Matrix.of fun i j => gramF σ B v ((R i)⁻¹ * C j)
  have hGN' : G * N = 1 := hGN
  have hGij : ∀ i j, G i j = B (u i) (σ (C j, 1) v) := by
    intro i j
    simp only [G, Matrix.of_apply, u]
    rw [B_w σ B v hF (R i) (C j)]
  have hcG : Matrix.vecMul c G = 0 := by
    funext j
    rw [Matrix.vecMul_apply_eq_sum]
    have h1 : (∑ i, c i * G i j) = ∑ i, (B (c i • u i)) (σ (C j, 1) v) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hGij i j, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hm : B (∑ i, c i • u i) = ∑ i, B (c i • u i) :=
      map_sum B (fun i => c i • u i) Finset.univ
    have hs : (∑ i, B (c i • u i)) (σ (C j, 1) v)
        = ∑ i, (B (c i • u i)) (σ (C j, 1) v) :=
      LinearMap.sum_apply Finset.univ (fun i => B (c i • u i)) (σ (C j, 1) v)
    rw [h1, ← hs, ← hm, hcsum]
    simp
  have hc0 : c = 0 := by
    calc c = Matrix.vecMul c 1 := (Matrix.vecMul_one c).symm
      _ = Matrix.vecMul c (G * N) := by rw [hGN']
      _ = Matrix.vecMul (Matrix.vecMul c G) N := (Matrix.vecMul_vecMul c G N).symm
      _ = Matrix.vecMul (0 : Fin 9 → ZMod 2) N := by rw [hcG]
      _ = 0 := Matrix.zero_vecMul N
  obtain ⟨i, hi⟩ := hcne
  exact hi (congrFun hc0 i)

end CFSG.EvenSporadicStandard.HNRecog.ML1
