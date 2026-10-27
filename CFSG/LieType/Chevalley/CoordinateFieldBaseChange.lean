module

public import CFSG.LieType.Chevalley.D4TripleA2Lemmas
public import CFSG.Blueprint.ChevalleyRootGroups

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {R S : Type} [Field R] [Field S] (f : R →+* S)

@[expose] def baseChangeEnd (A : Module.End R (RootModule τ R)) : Module.End S (RootModule τ S) :=
  Finsupp.linearCombination S fun b => Finsupp.mapRange f f.map_zero (A (Finsupp.single b 1))

theorem baseChangeEnd_single (A : Module.End R (RootModule τ R)) (b : Label τ) :
    baseChangeEnd f A (Finsupp.single b 1) =
      Finsupp.mapRange f f.map_zero (A (Finsupp.single b 1)) := by
  simp [baseChangeEnd]

theorem baseChange_baseChangeEnd (A : Module.End R (RootModule τ R)) :
    BaseChange f A (baseChangeEnd f A) := fun b => (baseChangeEnd_single f A b).symm

private theorem baseChangeEnd_apply (A : Module.End R (RootModule τ R)) (x : RootModule τ R) :
    Finsupp.mapRange f f.map_zero (A x) =
      baseChangeEnd f A (Finsupp.mapRange f f.map_zero x) := by
  have hsmul (r : R) (y : RootModule τ R) :
      Finsupp.mapRange f f.map_zero (r • y) = f r • Finsupp.mapRange f f.map_zero y := by
    ext a
    simp
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, Finsupp.mapRange_add (map_add f), hx, hy,
      Finsupp.mapRange_add (map_add f), map_add]
  | single b r =>
    rw [← Finsupp.smul_single_one, map_smul, hsmul, hsmul, map_smul]
    rw [Finsupp.mapRange_single, map_one, baseChangeEnd_single]

@[expose] def baseChangeEndHom : Module.End R (RootModule τ R) →* Module.End S (RootModule τ S) where
  toFun := baseChangeEnd f
  map_one' := Finsupp.lhom_ext' fun b => LinearMap.ext_ring (by
    simp [LinearMap.comp_apply, Finsupp.lsingle_apply, baseChangeEnd_single])
  map_mul' A B := Finsupp.lhom_ext' fun b => LinearMap.ext_ring (by
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, baseChangeEnd_single, Module.End.mul_apply]
    exact baseChangeEnd_apply f A (B (Finsupp.single b 1)))

@[expose] def baseChangeGL : ModGL τ R →* ModGL τ S :=
  Units.map (baseChangeEndHom f)

theorem coe_baseChangeGL
    (g : ModGL τ R) :
    ((baseChangeGL f g : ModGL τ S) : Module.End S (RootModule τ S)) =
      baseChangeEnd f (g : Module.End R (RootModule τ R)) :=
  rfl

theorem baseChangeGL_apply_single
    (g : ModGL τ R) (b : Label τ) :
    ((baseChangeGL f g : ModGL τ S) : Module.End S (RootModule τ S)) (Finsupp.single b 1) =
      Finsupp.mapRange f f.map_zero
        ((g : Module.End R (RootModule τ R)) (Finsupp.single b 1)) :=
  baseChangeEnd_single f _ b

theorem baseChangeGL_injective :
    Function.Injective (baseChangeGL (τ := τ) f) := by
  intro g g' h
  refine Units.ext ?_
  have h' : baseChangeEnd f (g : Module.End R (RootModule τ R)) =
      baseChangeEnd f (g' : Module.End R (RootModule τ R)) := congrArg Units.val h
  refine (baseChange_baseChangeEnd f _).eq_of_injective f.injective ?_
  rw [h']
  exact baseChange_baseChangeEnd f _

theorem baseChangeGL_xUnit
    (i : Fin τ.rank) (c : R) :
    baseChangeGL f (xUnit τ R i c) = xUnit τ S i (f c) :=
  Units.ext ((baseChange_baseChangeEnd f _).unique (BaseChange.xOp i c))

theorem baseChangeGL_yUnit
    (i : Fin τ.rank) (c : R) :
    baseChangeGL f (yUnit τ R i c) = yUnit τ S i (f c) :=
  Units.ext ((baseChange_baseChangeEnd f _).unique (BaseChange.yOp i c))

theorem baseChangeGL_pinnedX
    (α : Fin τ.rank → ℤ) (c : R) :
    baseChangeGL f (pinnedX τ R α c) = pinnedX τ S α (f c) :=
  Units.ext ((baseChange_baseChangeEnd f _).unique (baseChange_pinnedX f α c))

theorem map_baseChangeGL_adjointGroup :
    (adjointGroup τ R).map (baseChangeGL f) = Subgroup.closure
      {g | ∃ (i : Fin τ.rank) (c : R), g = xUnit τ S i (f c) ∨ g = yUnit τ S i (f c)} := by
  rw [adjointGroup, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨h, ⟨i, c, hh | hh⟩, rfl⟩
    · refine ⟨i, c, Or.inl ?_⟩
      rw [show h = xUnit τ R i c from Units.ext hh, baseChangeGL_xUnit]
    · refine ⟨i, c, Or.inr ?_⟩
      rw [show h = yUnit τ R i c from Units.ext hh, baseChangeGL_yUnit]
  · rintro ⟨i, c, rfl | rfl⟩
    · exact ⟨xUnit τ R i c, ⟨i, c, Or.inl rfl⟩, baseChangeGL_xUnit f i c⟩
    · exact ⟨yUnit τ R i c, ⟨i, c, Or.inr rfl⟩, baseChangeGL_yUnit f i c⟩

end CFSG.LieType.Chevalley
