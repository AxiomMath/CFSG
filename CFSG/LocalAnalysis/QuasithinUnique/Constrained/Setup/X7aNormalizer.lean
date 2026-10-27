module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aComm
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Central

variable {F : Type} [Field F] {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem mem_scalars_of_commutes (ρ : Representation (ZMod 2) SL(3, F) U)
    (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F) {y : SL(3, F)}
    (hy : ∀ w : SL(3, F), ρ y * ρ w = ρ w * ρ y) : y ∈ scalars 3 F := by
  have : Group.IsPerfect SL(3, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) (n := 3) le_rfl
  have hcen : ∀ w : SL(3, F), y * w * y⁻¹ * w⁻¹ ∈ Subgroup.center SL(3, F) := by
    intro w
    refine scalars_le_center 3 F (hker _ ?_)
    have h1 : ρ y * ρ w * ρ y⁻¹ = ρ w := by
      calc ρ y * ρ w * ρ y⁻¹ = ρ w * ρ y * ρ y⁻¹ := by rw [hy w]
        _ = ρ w := by rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    rw [map_mul, map_mul, map_mul, h1, ← map_mul, mul_inv_cancel, map_one]
  let κ : SL(3, F) →* Subgroup.center SL(3, F) :=
    { toFun := fun w => ⟨y * w * y⁻¹ * w⁻¹, hcen w⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun w w' => by
        apply Subtype.ext
        have hc' := Subgroup.mem_center_iff.mp (hcen w')
        change y * (w * w') * y⁻¹ * (w * w')⁻¹ =
          (y * w * y⁻¹ * w⁻¹) * (y * w' * y⁻¹ * w'⁻¹)
        calc y * (w * w') * y⁻¹ * (w * w')⁻¹
            = (y * w * y⁻¹) * (y * w' * y⁻¹ * w'⁻¹) * w⁻¹ := by group
          _ = (y * w * y⁻¹) * w⁻¹ * (y * w' * y⁻¹ * w'⁻¹) := by rw [mul_assoc _ _ w⁻¹, ← hc' w⁻¹, ← mul_assoc]
          _ = (y * w * y⁻¹ * w⁻¹) * (y * w' * y⁻¹ * w'⁻¹) := by group }
  have hκ := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative κ
  have hyc : ∀ w : SL(3, F), y * w * y⁻¹ * w⁻¹ = 1 := fun w => by
    have := congrArg (fun φ : SL(3, F) →* Subgroup.center SL(3, F) => (φ w : SL(3, F))) hκ
    simpa [κ] using this
  rw [scalars_eq_center]
  exact Subgroup.mem_center_iff.mpr fun w => by
    have := hyc w
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this.symm

variable (ρ : Representation (ZMod 2) SL(3, F) U)

theorem intertwines_one_scalars (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
    {a : U ≃ₗ[ZMod 2] U} {y : SL(3, F)}
    (h : Intertwines ρ a 1 y) : y ∈ scalars 3 F := by
  apply hker
  refine LinearMap.ext fun v => ?_
  obtain ⟨u, rfl⟩ := a.surjective v
  have := h u
  rw [map_one, Module.End.one_apply] at this
  exact this.symm

theorem intertwines_unique (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
    {a : U ≃ₗ[ZMod 2] U} {x y y' : SL(3, F)} (h : Intertwines ρ a x y)
    (h' : Intertwines ρ a x y') : y⁻¹ * y' ∈ scalars 3 F := by
  have := (h.inv).mul h'
  rw [inv_mul_cancel] at this
  exact intertwines_one_scalars ρ hker this

theorem Intertwines.of_inv {a : U ≃ₗ[ZMod 2] U} {x y : SL(3, F)}
    (h : Intertwines ρ a⁻¹ x y) : Intertwines ρ a y x := by
  intro u
  have h1 := h (a u)
  have h2 : (a⁻¹) (a u) = u := by simp
  rw [h2] at h1
  have h3 : a (a⁻¹ (ρ x (a u))) = ρ x (a u) := by simp
  rw [← h3, h1]

theorem intertwines_scalar_scalar (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
    {a : U ≃ₗ[ZMod 2] U}
    (ha' : ∀ x : SL(3, F), ∃ y, Intertwines ρ a⁻¹ x y) {z w : SL(3, F)} (hz : z ∈ scalars 3 F)
    (h : Intertwines ρ a z w) : w ∈ scalars 3 F := by
  apply mem_scalars_of_commutes ρ hker
  intro x'
  obtain ⟨x'', hx''⟩ := ha' x'
  have hx''' := Intertwines.of_inv ρ hx''
  have hcz : ρ z * ρ x'' = ρ x'' * ρ z := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp (scalars_le_center 3 F hz) x'').symm
  refine LinearMap.ext fun u => ?_
  obtain ⟨v, rfl⟩ := a.surjective u
  calc (ρ w * ρ x') (a v) = ρ w (ρ x' (a v)) := rfl
    _ = ρ w (a (ρ x'' v)) := by rw [← hx''' v]
    _ = a (ρ z (ρ x'' v)) := (h _).symm
    _ = a (ρ x'' (ρ z v)) := by
        have := LinearMap.congr_fun hcz v
        simpa using congrArg a this
    _ = ρ x' (a (ρ z v)) := hx''' _
    _ = ρ x' (ρ w (a v)) := by rw [h]
    _ = (ρ x' * ρ w) (a v) := rfl

theorem proj_eq_of_intertwines (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
    {a : U ≃ₗ[ZMod 2] U}
    (ha' : ∀ x : SL(3, F), ∃ y, Intertwines ρ a⁻¹ x y) {x x' y y' : SL(3, F)}
    (hx : proj 3 F x = proj 3 F x') (h : Intertwines ρ a x y) (h' : Intertwines ρ a x' y') :
    proj 3 F y = proj 3 F y' := by
  have hz : x⁻¹ * x' ∈ scalars 3 F := proj_eq_proj_iff.mp hx
  have hw : Intertwines ρ a (x⁻¹ * x') (y⁻¹ * y') := h.inv.mul h'
  exact proj_eq_proj_iff.mpr (intertwines_scalar_scalar ρ hker ha' hz hw)

end Central

section Induced

variable {F : Type} [Field F] {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) SL(3, F) U) (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)

theorem Intertwines.to_inv {a : U ≃ₗ[ZMod 2] U} {x y : SL(3, F)} (h : Intertwines ρ a x y) :
    Intertwines ρ a⁻¹ y x := by
  intro u
  have h1 := h (a⁻¹ u)
  have h2 : a (a⁻¹ u) = u := by simp
  rw [h2] at h1
  have h3 : (a⁻¹) (a (ρ x (a⁻¹ u))) = ρ x (a⁻¹ u) := by simp
  rw [← h3, h1]

theorem Intertwines.comp {a a' : U ≃ₗ[ZMod 2] U} {x z w : SL(3, F)} (h' : Intertwines ρ a' x z)
    (h : Intertwines ρ a z w) : Intertwines ρ (a * a') x w := by
  intro u
  show a (a' (ρ x u)) = ρ w (a (a' u))
  rw [h' u, h]

variable {a : U ≃ₗ[ZMod 2] U} (ha : ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)
  (ha' : ∀ x : SL(3, F), ∃ y, Intertwines ρ a⁻¹ x y)

noncomputable def indSL (x : SL(3, F)) : SL(3, F) := Classical.choose (ha x)

theorem indSL_spec (x : SL(3, F)) : Intertwines ρ a x (indSL ρ ha x) := Classical.choose_spec (ha x)

noncomputable def inducedHom : SL(3, F) →* projectiveSL 3 F where
  toFun x := proj 3 F (indSL ρ ha x)
  map_one' := by
    apply proj_eq_one_iff.mpr
    refine intertwines_one_scalars ρ hker (a := a) ?_
    exact indSL_spec ρ ha 1
  map_mul' x x' := by
    have h := proj_eq_of_intertwines ρ hker ha' (x := x * x') (x' := x * x') rfl
      (indSL_spec ρ ha (x * x')) ((indSL_spec ρ ha x).mul (indSL_spec ρ ha x'))
    show proj 3 F (indSL ρ ha (x * x')) = proj 3 F (indSL ρ ha x) * proj 3 F (indSL ρ ha x')
    rw [h, map_mul]

noncomputable def inducedPSL : projectiveSL 3 F →* projectiveSL 3 F :=
  QuotientGroup.lift (scalars 3 F) (inducedHom ρ hker ha ha') (fun z hz => by
    rw [MonoidHom.mem_ker]
    exact proj_eq_one_iff.mpr (intertwines_scalar_scalar ρ hker ha' hz (indSL_spec ρ ha z)))

theorem inducedPSL_proj (x : SL(3, F)) :
    inducedPSL ρ hker ha ha' (proj 3 F x) = proj 3 F (indSL ρ ha x) :=
  QuotientGroup.lift_mk _ _ x

theorem inducedPSL_bijective : Function.Bijective (inducedPSL ρ hker ha ha') := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    obtain ⟨x, rfl⟩ := proj_surjective 3 F p
    rw [MonoidHom.mem_ker, inducedPSL_proj] at hp
    have h1 : indSL ρ ha x ∈ scalars 3 F := proj_eq_one_iff.mp hp
    have h2 : Intertwines ρ a⁻¹ (indSL ρ ha x) x := (indSL_spec ρ ha x).to_inv ρ
    have h3 : ∀ y : SL(3, F), ∃ z, Intertwines ρ a⁻¹⁻¹ y z := fun y => by
      simpa using ha y
    exact Subgroup.mem_bot.mpr (proj_eq_one_iff.mpr (intertwines_scalar_scalar ρ hker h3 h1 h2))
  · intro q
    obtain ⟨y, rfl⟩ := proj_surjective 3 F q
    obtain ⟨x', hx'⟩ := ha' y
    have hint : Intertwines ρ a x' y := Intertwines.of_inv ρ hx'
    refine ⟨proj 3 F x', ?_⟩
    rw [inducedPSL_proj]
    exact proj_eq_of_intertwines ρ hker ha' rfl (indSL_spec ρ ha x') hint

noncomputable def inducedAut : MulAut (projectiveSL 3 F) :=
  MulEquiv.ofBijective (inducedPSL ρ hker ha ha') (inducedPSL_bijective ρ hker ha ha')

theorem inducedAut_apply {x y : SL(3, F)} (h : Intertwines ρ a x y) :
    inducedAut ρ hker ha ha' (proj 3 F x) = proj 3 F y := by
  show inducedPSL ρ hker ha ha' (proj 3 F x) = _
  rw [inducedPSL_proj]
  exact proj_eq_of_intertwines ρ hker ha' rfl (indSL_spec ρ ha x) h

end Induced

section NormalizerHom

variable {F : Type} [Field F] {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) SL(3, F) U) (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
  (A : Subgroup (U ≃ₗ[ZMod 2] U)) (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)

theorem normalizer_inv (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)
    (a : U ≃ₗ[ZMod 2] U) (ha : a ∈ A) :
    ∀ x : SL(3, F), ∃ y, Intertwines ρ a⁻¹ x y := fun x => hA a⁻¹ (A.inv_mem ha) x

noncomputable def normalizerHom : A →* MulAut (projectiveSL 3 F) where
  toFun a := inducedAut ρ hker (hA a a.2) (normalizer_inv ρ A hA a a.2)
  map_one' := by
    ext p
    obtain ⟨x, rfl⟩ := proj_surjective 3 F p
    rw [MulAut.one_apply]
    exact inducedAut_apply ρ hker _ _ (by intro u; rfl)
  map_mul' a a' := by
    ext p
    obtain ⟨x, rfl⟩ := proj_surjective 3 F p
    obtain ⟨z, hz⟩ := hA a' a'.2 x
    obtain ⟨w, hw⟩ := hA a a.2 z
    have h1 : inducedAut ρ hker (hA a' a'.2) (normalizer_inv ρ A hA a' a'.2) (proj 3 F x) =
        proj 3 F z := inducedAut_apply ρ hker _ _ hz
    rw [MulAut.mul_apply, h1]
    have h2 : inducedAut ρ hker (hA a a.2) (normalizer_inv ρ A hA a a.2) (proj 3 F z) =
        proj 3 F w := inducedAut_apply ρ hker _ _ hw
    rw [h2]
    exact inducedAut_apply ρ hker _ _ (hz.comp ρ hw)

theorem normalizerHom_apply (a : A) {x y : SL(3, F)} (h : Intertwines ρ (a : U ≃ₗ[ZMod 2] U) x y) :
    normalizerHom ρ hker A hA a (proj 3 F x) = proj 3 F y :=
  inducedAut_apply ρ hker _ _ h

theorem exists_induced (a : A) (x : SL(3, F)) :
    ∃ y, Intertwines ρ (a : U ≃ₗ[ZMod 2] U) x y ∧
      proj 3 F y = normalizerHom ρ hker A hA a (proj 3 F x) := by
  obtain ⟨y, hy⟩ := hA a a.2 x
  exact ⟨y, hy, (normalizerHom_apply ρ hker A hA a hy).symm⟩

end NormalizerHom

end CFSG.QuasithinUnique.Setup.X7a
