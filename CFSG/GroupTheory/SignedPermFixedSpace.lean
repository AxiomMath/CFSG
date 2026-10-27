module

public import CFSG.GroupTheory.SignedPermFThree
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.GroupTheory

open Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] def fixedVectors (x : GL ι K) : Set (ι → K) :=
  {w | (x : Matrix ι ι K) *ᵥ w = w}

@[expose] def commonFixedVectors {Y : Type*} [Group Y] (ρ : Y →* GL ι K)
    (c : Multiplicative (Fin 3 → ZMod 3) →* Y) : Set (ι → K) :=
  ⋂ v, fixedVectors (ρ (c v))

private lemma fixedVectors_conj_aux_inv (g : GL ι K) (w : ι → K) :
    ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]

private lemma fixedVectors_conj_aux_mul (g : GL ι K) (w : ι → K) :
    (g : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec]

theorem fixedVectors_conj (g x : GL ι K) :
    fixedVectors (g * x * g⁻¹) = (fun w => (g : Matrix ι ι K) *ᵥ w) '' fixedVectors x := by
  ext w
  constructor
  · intro hw
    have hw₀ : ((g * x * g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w = w := hw
    refine ⟨((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w, ?_, ?_⟩
    · show (x : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) =
        ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w
      have hw' : (g : Matrix ι ι K) *ᵥ
          ((x : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w)) = w := by
        simpa only [Units.val_mul, ← Matrix.mulVec_mulVec] using hw₀
      have h := congrArg (fun z => ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ z) hw'
      simpa only [fixedVectors_conj_aux_inv] using h
    · exact fixedVectors_conj_aux_mul g w
  · rintro ⟨y, hy, rfl⟩
    have hy' : (x : Matrix ι ι K) *ᵥ y = y := hy
    show ((g * x * g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ y) =
      (g : Matrix ι ι K) *ᵥ y
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec, fixedVectors_conj_aux_inv, hy']

theorem exists_mulEquiv_conj_of_mem_range {Y : Type*} [Group Y]
    (c : Multiplicative (Fin 3 → ZMod 3) →* Y) (hc : Function.Injective c) (g : Y)
    (hg : ∀ v, ∃ w, g * c v * g⁻¹ = c w) :
    ∃ α : Multiplicative (Fin 3 → ZMod 3) ≃* Multiplicative (Fin 3 → ZMod 3),
      ∀ v, g * c v * g⁻¹ = c (α v) := by
  classical
  let α₀ : Multiplicative (Fin 3 → ZMod 3) → Multiplicative (Fin 3 → ZMod 3) :=
    fun v => Classical.choose (hg v)
  have hα₀ : ∀ v, g * c v * g⁻¹ = c (α₀ v) := fun v => Classical.choose_spec (hg v)
  have hinj : Function.Injective α₀ := by
    intro v w hvw
    apply hc
    have h : g * c v * g⁻¹ = g * c w * g⁻¹ := by rw [hα₀ v, hα₀ w, hvw]
    exact mul_left_cancel (mul_right_cancel h)
  have hmul : ∀ v w, α₀ (v * w) = α₀ v * α₀ w := by
    intro v w
    apply hc
    rw [← hα₀ (v * w)]
    simp only [map_mul]
    rw [← hα₀ v, ← hα₀ w]
    exact (conj_mul (a := c v) (b := g) (c := c w)).symm
  have hbij : Function.Bijective α₀ := hinj.bijective_of_finite
  refine ⟨{ Equiv.ofBijective α₀ hbij with map_mul' := ?_ }, ?_⟩
  · intro v w
    exact hmul v w
  · intro v
    exact hα₀ v

theorem image_commonFixedVectors_eq {Y : Type*} [Group Y] (ρ : Y →* GL ι K)
    (c : Multiplicative (Fin 3 → ZMod 3) →* Y) (hc : Function.Injective c) (g : Y)
    (hg : ∀ v, ∃ w, g * c v * g⁻¹ = c w) :
    (fun w => ((ρ g : GL ι K) : Matrix ι ι K) *ᵥ w) '' commonFixedVectors ρ c =
      commonFixedVectors ρ c := by
  obtain ⟨α, hα⟩ := exists_mulEquiv_conj_of_mem_range c hc g hg
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [commonFixedVectors, Set.mem_iInter] at hy ⊢
    intro v
    set u := α.symm v with hu
    have hau : α u = v := by rw [hu]; exact MulEquiv.apply_symm_apply α v
    have hcv : ρ (c v) = ρ g * ρ (c u) * (ρ g)⁻¹ := by
      rw [← hau, ← hα u]
      simp only [map_mul, map_inv]
    rw [hcv, fixedVectors_conj]
    exact ⟨y, hy u, rfl⟩
  · intro hw
    rw [commonFixedVectors, Set.mem_iInter] at hw
    refine ⟨((ρ g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w, ?_, ?_⟩
    · rw [commonFixedVectors, Set.mem_iInter]
      intro v
      have hcv : ρ (c (α v)) = ρ g * ρ (c v) * (ρ g)⁻¹ := by
        rw [← hα v]
        simp only [map_mul, map_inv]
      have hwv : w ∈ fixedVectors (ρ g * ρ (c v) * (ρ g)⁻¹) := by
        rw [← hcv]
        exact hw (α v)
      rw [fixedVectors_conj] at hwv
      obtain ⟨z, hz, hzg⟩ := hwv
      have hyz : ((ρ g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w = z := by
        rw [← hzg, map_inv]
        exact fixedVectors_conj_aux_inv (ρ g) z
      show (↑(ρ (c v)) : Matrix ι ι K) *ᵥ
          (((ρ g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) =
        ((ρ g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w
      rw [hyz]
      exact hz
    · rw [map_inv]
      exact fixedVectors_conj_aux_mul (ρ g) w

theorem exists_signedPerm_of_conj_mem_range {Y : Type*} [Group Y] (ρ : Y →* GL ι K)
    (c : Multiplicative (Fin 3 → ZMod 3) →* Y) (hc : Function.Injective c)
    (hfix : ∀ v : Multiplicative (Fin 3 → ZMod 3),
      fixedVectors (ρ (c v)) = commonFixedVectors ρ c ↔ ∀ i, Multiplicative.toAdd v i ≠ 0)
    (g : Y) (hg : ∀ v, ∃ w, g * c v * g⁻¹ = c w) :
    ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧ ∀ v,
      g * c v * g⁻¹ =
        c (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i)) := by
  obtain ⟨α, hα⟩ := exists_mulEquiv_conj_of_mem_range c hc g hg
  let α' : (Fin 3 → ZMod 3) ≃+ (Fin 3 → ZMod 3) :=
    { toFun := fun v => Multiplicative.toAdd (α (Multiplicative.ofAdd v))
      invFun := fun v => Multiplicative.toAdd (α.symm (Multiplicative.ofAdd v))
      left_inv := by
        intro v
        simp
      right_inv := by
        intro v
        simp
      map_add' := by
        intro v w
        simp only [ofAdd_add, map_mul, toAdd_mul] }
  have hαα' : ∀ v : Fin 3 → ZMod 3,
      α (Multiplicative.ofAdd v) = Multiplicative.ofAdd (α' v) :=
    fun v => (ofAdd_toAdd (α (Multiplicative.ofAdd v))).symm
  have hpres : ∀ v : Fin 3 → ZMod 3, (∀ i, v i ≠ 0) → ∀ i, α' v i ≠ 0 := by
    intro v hv
    have hu : ∀ i, Multiplicative.toAdd (Multiplicative.ofAdd v) i ≠ 0 := by simpa using hv
    have hbase : fixedVectors (ρ (c (α (Multiplicative.ofAdd v)))) =
        commonFixedVectors ρ c := by
      have hcα : c (α (Multiplicative.ofAdd v)) =
          g * c (Multiplicative.ofAdd v) * g⁻¹ := (hα (Multiplicative.ofAdd v)).symm
      have hρ : ρ (c (α (Multiplicative.ofAdd v))) =
          ρ g * ρ (c (Multiplicative.ofAdd v)) * (ρ g)⁻¹ := by
        rw [hcα]
        simp only [map_mul, map_inv]
      rw [hρ, fixedVectors_conj, (hfix (Multiplicative.ofAdd v)).mpr hu]
      exact image_commonFixedVectors_eq ρ c hc g hg
    have h' : fixedVectors (ρ (c (Multiplicative.ofAdd (α' v)))) =
        commonFixedVectors ρ c := by
      simpa only [hαα' v] using hbase
    have hfin := (hfix (Multiplicative.ofAdd (α' v))).mp h'
    simpa using hfin
  obtain ⟨σ, ε, hε, hform⟩ := exists_signedPerm_of_preserves α' hpres
  refine ⟨σ, ε, hε, fun v => ?_⟩
  calc g * c v * g⁻¹ = c (α v) := hα v
    _ = c (Multiplicative.ofAdd (α' (Multiplicative.toAdd v))) := by
          rw [← hαα' (Multiplicative.toAdd v)]
          simp
    _ = c (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i)) := by
          rw [hform (Multiplicative.toAdd v)]

end CFSG.GroupTheory
