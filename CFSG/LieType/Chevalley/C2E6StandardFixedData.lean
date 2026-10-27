module

public import CFSG.LieType.Chevalley.C2E6UnitaryFourCompound
public import CFSG.LieType.Chevalley.GraphFixedStandardParabolic
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap

abbrev stdFixedGroup : Subgroup (ModGL Tag.E6 K) := twistedFixedGroup TwistTag.E6 K barHom

abbrev stdGroup
    : Subgroup (ModGL Tag.E6 K) := graphFixedRootGroup TwistTag.E6 K barHom

abbrev stdBorel
    : Subgroup (ModGL Tag.E6 K) := graphFixedRootBorel TwistTag.E6 K barHom

abbrev stdTorus
    : Subgroup (ModGL Tag.E6 K) := graphFixedRootTorus TwistTag.E6 K barHom

theorem barHom_comp_barHom : barHom.comp barHom = RingHom.id K := by
  ext a
  exact bar_bar a

@[expose] def nativeOrbit : Fin 4 → Finset (Fin 6) := ![{1}, {3}, {2, 4}, {0, 5}]

@[expose] def foldedIndex (i : Fin 4) : Fin TwistTag.E6.foldedTag.rank := Fin.rev i

theorem nativeOrbit_eq_orbit (i : Fin 4) : nativeOrbit i = TwistTag.E6.orbit (foldedIndex i) := by
  fin_cases i <;> rfl

@[expose] def nativeRefl
    (i : Fin 4) : WeylGroup Tag.E6 :=
  (coxeterSystem Tag.E6).wordProd ((nativeOrbit i).sort (· ≤ ·))

theorem nativeRefl_eq
    (i : Fin 4) : nativeRefl i = TwistTag.E6.orbitReflection (foldedIndex i) := by
  rw [nativeRefl, TwistTag.orbitReflection, TwistTag.orbitWord_eq_sort, nativeOrbit_eq_orbit]
  rfl

@[expose] def nativeRep
    (i : Fin 4) : ModGL Tag.E6 K :=
  canonicalRep (coxeterSystem Tag.E6) K (nativeRefl i)

@[expose] def nativeParabolic
    (J : Set (Fin 4)) : Subgroup (ModGL Tag.E6 K) :=
  Subgroup.closure ((stdBorel : Set (ModGL Tag.E6 K)) ∪ nativeRep '' J)

@[expose] def nativeWeyl
    (J : Set (Fin 4)) : Subgroup (WeylGroup Tag.E6) :=
  Subgroup.closure (nativeRefl '' J)

theorem image_nativeRep
    (J : Set (Fin 4)) :
    nativeRep '' J = (fun a => canonicalRep (coxeterSystem TwistTag.E6.tag) K
      (TwistTag.E6.orbitReflection a)) '' (foldedIndex '' J) := by
  rw [Set.image_image]
  refine Set.image_congr fun i _ => ?_
  rw [nativeRep, nativeRefl_eq]
  rfl

theorem nativeParabolic_eq
    (J : Set (Fin 4)) :
    nativeParabolic J = graphFixedParabolic TwistTag.E6 K barHom (foldedIndex '' J) := by
  rw [nativeParabolic, graphFixedParabolic, Subgroup.closure_union, Subgroup.closure_eq,
    image_nativeRep]
  rfl

theorem nativeWeyl_eq
    (J : Set (Fin 4)) :
    nativeWeyl J = foldedParabolicWeylGroup TwistTag.E6 (foldedIndex '' J) := by
  rw [nativeWeyl, foldedParabolicWeylGroup, Set.image_image]
  congr 1
  exact Set.image_congr fun i _ => nativeRefl_eq i

@[expose] def setA : Set (Fin 6) := {0, 2, 3, 4, 5}

@[expose] def setD : Set (Fin 6) := {1, 2, 3, 4}

abbrev groupA
    : Subgroup (ModGL Tag.E6 K) := subsystemGroup Tag.E6 K setA

abbrev torusA
    : Subgroup (ModGL Tag.E6 K) := subsystemTorus Tag.E6 K setA

abbrev unipotentA
    : Subgroup (ModGL Tag.E6 K) := parabolicLeviUnipotent Tag.E6 K setA

abbrev groupD
    : Subgroup (ModGL Tag.E6 K) := subsystemGroup Tag.E6 K setD

abbrev torusD
    : Subgroup (ModGL Tag.E6 K) := subsystemTorus Tag.E6 K setD

abbrev unipotentD
    : Subgroup (ModGL Tag.E6 K) := parabolicLeviUnipotent Tag.E6 K setD

@[expose] def moduleA : Submodule K (RootModule Tag.E6 K) :=
  Submodule.span K {v | ∃ α, IsRoot Tag.E6 α ∧ α (1 : Fin 6) = 1 ∧ v = rootVec Tag.E6 K α}

@[expose] def moduleD : Submodule K (RootModule Tag.E6 K) :=
  Submodule.span K {v | ∃ α, IsRoot Tag.E6 α ∧ α (0 : Fin 6) = 1 ∧ α (5 : Fin 6) = 1 ∧
    v = rootVec Tag.E6 K α}

abbrev betaStar : Module.End K (RootModule Tag.E6 K) →* Module.End K (RootModule Tag.E6 K) :=
  entrywiseHom barHom

abbrev betaGL : ModGL Tag.E6 K →* ModGL Tag.E6 K := Units.map betaStar

theorem betaStar_apply (A : Module.End K (RootModule Tag.E6 K)) :
    betaStar A = entrywise barHom A := rfl

end CFSG.LieType.Chevalley.C2E6Std
