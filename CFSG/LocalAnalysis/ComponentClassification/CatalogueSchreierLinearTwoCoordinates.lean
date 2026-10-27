module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Triple

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter

universe u

abbrev Omega (K : Type u) := Option K

@[expose] def coordinatePoint (K : Type u) [Field K] : Omega K → PSL2ProjectiveLine K
  | none => psl2ProjectiveInfinity K
  | some x => psl2AffinePoint K x

theorem coordinatePoint_bijective (K : Type u) [Field K] :
    Function.Bijective (coordinatePoint K) := by
  constructor
  · intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact ((psl2AffinePoint_ne_infinity y) h.symm).elim
    | some x =>
      cases y with
      | none => exact ((psl2AffinePoint_ne_infinity x) h).elim
      | some y => exact congrArg some (psl2AffinePoint_injective h)
  · intro x
    by_cases hx : x = psl2ProjectiveInfinity K
    · exact ⟨none, hx.symm⟩
    · obtain ⟨a, ha, _⟩ := existsUnique_psl2AffinePoint_eq x hx
      exact ⟨some a, ha⟩

@[expose] def coordinateEquiv (K : Type u) [Field K] : Omega K ≃ PSL2ProjectiveLine K :=
  Equiv.ofBijective (coordinatePoint K) (coordinatePoint_bijective K)

@[simp]
theorem coordinateEquiv_none (K : Type u) [Field K] :
    coordinateEquiv K none = psl2ProjectiveInfinity K := rfl

@[simp]
theorem coordinateEquiv_some (K : Type u) [Field K] (x : K) :
    coordinateEquiv K (some x) = psl2AffinePoint K x := rfl

@[expose] def translation (K : Type u) [Field K] (b : K) : Equiv.Perm (Omega K) :=
  Equiv.optionCongr {
    toFun := fun x => x + b
    invFun := fun x => x - b
    left_inv := by intro x; simp
    right_inv := by intro x; simp }

@[simp]
theorem translation_none (K : Type u) [Field K] (b : K) : translation K b none = none := rfl

@[simp]
theorem translation_some (K : Type u) [Field K] (b x : K) :
    translation K b (some x) = some (x + b) := rfl

@[expose] def inversion (K : Type u) [Field K] : Equiv.Perm (Omega K) := by
  classical
  let f : Omega K → Omega K
    | none => some 0
    | some x => if x = 0 then none else some (-x⁻¹)
  have hf : Function.Involutive f := by
    intro x
    cases x with
    | none => simp [f]
    | some x =>
      by_cases hx : x = 0
      · simp [f, hx]
      · simp [f, hx]
  exact ⟨f, f, hf, hf⟩

@[simp]
theorem inversion_none (K : Type u) [Field K] : inversion K none = some 0 := rfl

@[simp]
theorem inversion_zero (K : Type u) [Field K] : inversion K (some 0) = none := by
  classical
  simp [inversion]

theorem inversion_nonzero (K : Type u) [Field K] (x : K) (hx : x ≠ 0) :
    inversion K (some x) = some (-x⁻¹) := by
  classical
  simp [inversion, hx]

@[expose] def multiplier (K : Type u) [Field K] (s : Kˣ) : Equiv.Perm (Omega K) :=
  Equiv.optionCongr {
    toFun := fun x => (s : K) * x
    invFun := fun x => (s⁻¹ : Kˣ) * x
    left_inv := by intro x; simp
    right_inv := by intro x; simp }

@[simp]
theorem multiplier_none (K : Type u) [Field K] (s : Kˣ) : multiplier K s none = none := rfl

@[simp]
theorem multiplier_some (K : Type u) [Field K] (s : Kˣ) (x : K) :
    multiplier K s (some x) = some ((s : K) * x) := rfl

@[expose] def fieldExtension (K : Type u) [Field K] (sigma : K ≃+* K) :
    Equiv.Perm (Omega K) := Equiv.optionCongr sigma.toEquiv

@[simp]
theorem fieldExtension_none (K : Type u) [Field K] (sigma : K ≃+* K) :
    fieldExtension K sigma none = none := rfl

@[simp]
theorem fieldExtension_some (K : Type u) [Field K] (sigma : K ≃+* K) (x : K) :
    fieldExtension K sigma (some x) = some (sigma x) := rfl

@[expose] def coordinateU (K : Type u) [Field K] : Subgroup (Equiv.Perm (Omega K)) :=
  Subgroup.closure (Set.range (translation K))

@[expose] def coordinateG (K : Type u) [Field K] : Subgroup (Equiv.Perm (Omega K)) :=
  Subgroup.closure (Set.range (translation K) ∪ {inversion K})

@[expose] def coordinateD (K : Type u) [Field K] : Subgroup (Equiv.Perm (Omega K)) :=
  Subgroup.closure ((coordinateG K : Set (Equiv.Perm (Omega K))) ∪ Set.range (multiplier K))

@[expose] def coordinateE (K : Type u) [Field K] : Subgroup (Equiv.Perm (Omega K)) :=
  Subgroup.closure ((coordinateD K : Set (Equiv.Perm (Omega K))) ∪
    Set.range (fieldExtension K))

@[expose] def coordinatePSLAction (K : Type u) [Field K] :
    PSL2 K →* Equiv.Perm (Omega K) :=
  (coordinateEquiv K).symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (PSL2 K) (PSL2ProjectiveLine K))

@[expose] def coordinatePGLAction (K : Type u) [Field K] :
    PGL2 K →* Equiv.Perm (Omega K) :=
  (coordinateEquiv K).symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (PGL2 K) (PSL2ProjectiveLine K))

theorem coordinatePSLAction_point (K : Type u) [Field K] (g : PSL2 K) (x : Omega K) :
    coordinateEquiv K (coordinatePSLAction K g x) = g • coordinateEquiv K x := by
  exact (coordinateEquiv K).apply_symm_apply _

theorem coordinatePGLAction_point (K : Type u) [Field K] (g : PGL2 K) (x : Omega K) :
    coordinateEquiv K (coordinatePGLAction K g x) = g • coordinateEquiv K x := by
  exact (coordinateEquiv K).apply_symm_apply _

theorem coordinatePSLAction_injective (K : Type u) [Field K] :
    Function.Injective (coordinatePSLAction K) :=
  (coordinateEquiv K).symm.permCongrHom.injective.comp
    (MulAction.toPerm_injective (α := PSL2 K) (β := PSL2ProjectiveLine K))

theorem coordinatePGLAction_toPGL (K : Type u) [Field K] (g : PSL2 K) :
    coordinatePGLAction K (Matrix.ProjectiveSpecialLinearGroup.toPGL g) =
      coordinatePSLAction K g := by
  apply Equiv.ext
  intro x
  apply (coordinateEquiv K).injective
  rw [coordinatePGLAction_point, coordinatePSLAction_point, psl2ToPGL_smul]

end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
