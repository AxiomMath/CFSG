module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage3FinInputs

public section

namespace CFSG.QuasithinUnique.A5

variable {G : Type*} [Group G] {P Z M₁ : Subgroup G}

theorem exists_rho (θ : ↥P →* Multiplicative V4) (hθ : Function.Surjective θ)
    (hker : θ.ker = Z.subgroupOf P)
    (hnorm : ∀ m ∈ M₁, ∀ p ∈ P, m * p * m⁻¹ ∈ P)
    (hZ : ∀ m ∈ M₁, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z) :
    ∃ ρ : ↥M₁ →* GL (Fin 4) (ZMod 2), ∀ (m : ↥M₁) (x y : ↥P), (y : G) = m * x * m⁻¹ →
      Multiplicative.toAdd (θ y) =
        (ρ m : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (θ x)) := by
  classical
  choose sec hsec using hθ
  let cj : ↥M₁ → ↥P → ↥P := fun m p => ⟨(m : G) * p * (m : G)⁻¹, hnorm m m.2 p p.2⟩
  have cj_val : ∀ m p, ((cj m p : ↥P) : G) = (m : G) * p * (m : G)⁻¹ := fun _ _ => rfl
  have cj_mul : ∀ m p q, cj m (p * q) = cj m p * cj m q := by
    intro m p q
    apply Subtype.ext
    simp only [cj_val, Subgroup.coe_mul]
    group
  have cj_comp : ∀ m m' p, cj (m * m') p = cj m (cj m' p) := by
    intro m m' p
    apply Subtype.ext
    simp only [cj_val, Subgroup.coe_mul]
    group
  have cj_one : ∀ p, cj 1 p = p := by
    intro p
    apply Subtype.ext
    simp [cj_val]
  have cj_ker : ∀ m p, θ p = 1 → θ (cj m p) = 1 := by
    intro m p hp
    have h1 : p ∈ θ.ker := hp
    rw [hker] at h1
    have h2 : cj m p ∈ θ.ker := by
      rw [hker]
      exact hZ m m.2 p h1
    exact h2
  let La : ↥M₁ → V4 → V4 := fun m v =>
    Multiplicative.toAdd (θ (cj m (sec (Multiplicative.ofAdd v))))
  have La_spec : ∀ m (p : ↥P),
      La m (Multiplicative.toAdd (θ p)) = Multiplicative.toAdd (θ (cj m p)) := by
    intro m p
    show Multiplicative.toAdd (θ (cj m (sec (Multiplicative.ofAdd (Multiplicative.toAdd (θ p))))))
      = _
    rw [ofAdd_toAdd]
    have h2 : θ ((sec (θ p))⁻¹ * p) = 1 := by
      rw [map_mul, map_inv, hsec]
      exact inv_mul_cancel _
    have h3 : cj m p = cj m (sec (θ p)) * cj m ((sec (θ p))⁻¹ * p) := by
      rw [← cj_mul]
      congr 1
      group
    conv_rhs => rw [h3, map_mul, cj_ker m _ h2, mul_one]
  have La_add : ∀ m u v, La m (u + v) = La m u + La m v := by
    intro m u v
    have huv : u + v = Multiplicative.toAdd (θ (sec (Multiplicative.ofAdd u) *
        sec (Multiplicative.ofAdd v))) := by
      rw [map_mul, hsec, hsec]
      rfl
    rw [huv, La_spec, cj_mul, map_mul, toAdd_mul]
  have La_zero : ∀ m, La m 0 = 0 := by
    intro m
    have h := La_add m 0 0
    rw [add_zero] at h
    have h2 : La m 0 + La m 0 = La m 0 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h2
  let Llin : ↥M₁ → (V4 →ₗ[ZMod 2] V4) := fun m =>
    { toFun := La m
      map_add' := La_add m
      map_smul' := by
        intro c v
        rcases zmod2_cases c with rfl | rfl
        · simp [La_zero]
        · simp }
  have Llin_apply : ∀ m v, Llin m v = La m v := fun _ _ => rfl
  have Llin_mul : ∀ m m', Llin (m * m') = (Llin m).comp (Llin m') := by
    intro m m'
    apply LinearMap.ext
    intro v
    rw [Llin_apply, LinearMap.comp_apply, Llin_apply, Llin_apply]
    show Multiplicative.toAdd (θ (cj (m * m') (sec (Multiplicative.ofAdd v)))) = La m (La m' v)
    rw [show La m' v = Multiplicative.toAdd (θ (cj m' (sec (Multiplicative.ofAdd v)))) from rfl,
      La_spec, cj_comp]
  have Llin_one : Llin 1 = LinearMap.id := by
    apply LinearMap.ext
    intro v
    show Multiplicative.toAdd (θ (cj 1 (sec (Multiplicative.ofAdd v)))) = v
    rw [cj_one, hsec]
    rfl
  let matHom : ↥M₁ →* Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    { toFun := fun m => LinearMap.toMatrix' (Llin m)
      map_one' := by
        show LinearMap.toMatrix' (Llin 1) = 1
        rw [Llin_one, LinearMap.toMatrix'_id]
      map_mul' := by
        intro m m'
        show LinearMap.toMatrix' (Llin (m * m')) =
          LinearMap.toMatrix' (Llin m) * LinearMap.toMatrix' (Llin m')
        rw [Llin_mul, LinearMap.toMatrix'_comp] }
  refine ⟨matHom.toHomUnits, ?_⟩
  intro m x y hxy
  have hy : y = cj m x := Subtype.ext hxy
  have hmat : ((matHom.toHomUnits m : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      LinearMap.toMatrix' (Llin m) := rfl
  rw [hmat, LinearMap.toMatrix'_mulVec, Llin_apply, La_spec, hy]

end CFSG.QuasithinUnique.A5
