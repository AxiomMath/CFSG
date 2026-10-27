module

public import CFSG.Quasithin.Background.SmithCurtisBasic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Algebra.Algebra.ZMod
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.Quasithin
open scoped MonoidAlgebra

variable {E X M D : Type*}
  [Field E] [Fintype E] [CharP E 2] [Algebra (ZMod 2) E]
  [AddCommGroup X] [Module E X] [Module (ZMod 2) X]
  [Group M] [Group D]

section GroupAlgebra

variable [Module (MonoidAlgebra (ZMod 2) M) X]
variable [IsScalarTower (ZMod 2) (MonoidAlgebra (ZMod 2) M) X]

omit [IsScalarTower (ZMod 2) (MonoidAlgebra (ZMod 2) M) X] in
theorem isInvariant_of_submodule (σ : Representation (ZMod 2) M X)
    (hsmul : ∀ (g : M) (x : X),
      (MonoidAlgebra.single g (1 : ZMod 2)) • x = σ g x)
    (W : Submodule (MonoidAlgebra (ZMod 2) M) X) :
    ∀ g, ∀ w ∈ W, σ g w ∈ W := by
  intro g w hw
  rw [← hsmul g w]
  exact W.smul_mem (MonoidAlgebra.single g (1 : ZMod 2)) hw

@[expose] noncomputable def submoduleOfIsInvariant (σ : Representation (ZMod 2) M X)
    (hsmul : ∀ (g : M) (x : X),
      (MonoidAlgebra.single g (1 : ZMod 2)) • x = σ g x)
    (W : Submodule (ZMod 2) X)
    (hW : ∀ g, ∀ w ∈ W, σ g w ∈ W) : Submodule (MonoidAlgebra (ZMod 2) M) X where
  carrier := W
  add_mem' := W.add_mem
  zero_mem' := W.zero_mem
  smul_mem' := by
    intro r x hx
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r s hr hs => simpa [add_smul] using W.add_mem hr hs
    | single g a =>
        have hsingle : MonoidAlgebra.single g a =
            a • MonoidAlgebra.single g (1 : ZMod 2) := by
          rw [MonoidAlgebra.smul_single]
          simp
        rw [hsingle, smul_assoc, hsmul g x]
        exact W.smul_mem a (hW g x hx)

@[simp]
theorem mem_submoduleOfIsInvariant (σ : Representation (ZMod 2) M X)
    (hsmul : ∀ (g : M) (x : X),
      (MonoidAlgebra.single g (1 : ZMod 2)) • x = σ g x)
    {W : Submodule (ZMod 2) X}
    {hW : ∀ g, ∀ w ∈ W, σ g w ∈ W} {x : X} :
    x ∈ submoduleOfIsInvariant σ hsmul W hW ↔ x ∈ W := Iff.rfl

theorem single_smul_eq (σ : Representation (ZMod 2) M X)
    (hsmul : ∀ (g : M) (x : X),
      (MonoidAlgebra.single g (1 : ZMod 2)) • x = σ g x)
    (g : M) (a : ZMod 2) (x : X) :
    (MonoidAlgebra.single g a) • x = a • σ g x := by
  have hsingle : MonoidAlgebra.single g a =
      a • MonoidAlgebra.single g (1 : ZMod 2) := by
    rw [MonoidAlgebra.smul_single]
    simp
  rw [hsingle, smul_assoc, hsmul]

omit [Fintype E] [CharP E 2] in
theorem smul_comm_groupAlgebra (σ : Representation (ZMod 2) M X)
    (hsmul : ∀ (g : M) (x : X),
      (MonoidAlgebra.single g (1 : ZMod 2)) • x = σ g x)
    (hσE : ∀ g, ∀ (c : E) (x : X), σ g (c • x) = c • σ g x)
    (c : E) (r : MonoidAlgebra (ZMod 2) M) (x : X) :
    c • (r • x) = r • (c • x) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r s hr hs => simp [add_smul, hr, hs]
  | single g a =>
      rw [single_smul_eq σ hsmul g a x,
        single_smul_eq σ hsmul g a (c • x), hσE g c x, smul_comm]

omit [Fintype E] [CharP E 2] in
@[expose] noncomputable def smulLinear (σ : Representation (ZMod 2) M X)
    (hsmul : ∀ (g : M) (x : X),
      (MonoidAlgebra.single g (1 : ZMod 2)) • x = σ g x)
    (hσE : ∀ g, ∀ (c : E) (x : X), σ g (c • x) = c • σ g x) (c : E) :
    X →ₗ[MonoidAlgebra (ZMod 2) M] X where
  toFun x := c • x
  map_add' x y := smul_add c x y
  map_smul' r x := smul_comm_groupAlgebra σ hsmul hσE c r x

omit [Fintype E] [CharP E 2] in
@[simp]
theorem smulLinear_apply (σ : Representation (ZMod 2) M X)
    (hsmul : ∀ (g : M) (x : X),
      (MonoidAlgebra.single g (1 : ZMod 2)) • x = σ g x)
    (hσE : ∀ g, ∀ (c : E) (x : X), σ g (c • x) = c • σ g x)
    (c : E) (x : X) : smulLinear σ hsmul hσE c x = c • x := rfl

@[expose] noncomputable def smulSubmodule (σ : Representation (ZMod 2) M X)
    (hsmul : ∀ (g : M) (x : X),
      (MonoidAlgebra.single g (1 : ZMod 2)) • x = σ g x)
    (hσE : ∀ g, ∀ (c : E) (x : X), σ g (c • x) = c • σ g x)
    (c : E) (W : Submodule (MonoidAlgebra (ZMod 2) M) X) :
    Submodule (MonoidAlgebra (ZMod 2) M) X :=
  W.map (smulLinear σ hsmul hσE c)

omit [Fintype E] [CharP E 2] in
@[simp]
theorem smulSubmodule_one (σ : Representation (ZMod 2) M X)
    (hsmul : ∀ (g : M) (x : X),
      (MonoidAlgebra.single g (1 : ZMod 2)) • x = σ g x)
    (hσE : ∀ g, ∀ (c : E) (x : X), σ g (c • x) = c • σ g x)
    (W : Submodule (MonoidAlgebra (ZMod 2) M) X) :
    smulSubmodule σ hsmul hσE 1 W = W := by
  ext x
  simp only [smulSubmodule, Submodule.mem_map, smulLinear, LinearMap.coe_mk,
    AddHom.coe_mk]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x, hx, by simp⟩

section Normalizer

variable (σ : Representation (ZMod 2) M X) (δ : Representation (ZMod 2) D X)
variable (hsmul : ∀ (g : M) (x : X),
  (MonoidAlgebra.single g (1 : ZMod 2)) • x = σ g x)
variable (hnorm : ∀ d g, ∃ g', ∀ x, δ d (σ g x) = σ g' (δ d x))

@[expose] noncomputable def mapSubmodule (d : D)
    (W : Submodule (MonoidAlgebra (ZMod 2) M) X) :
    Submodule (MonoidAlgebra (ZMod 2) M) X :=
  submoduleOfIsInvariant σ hsmul ((W.restrictScalars (ZMod 2)).map (δ d)) (by
    intro g y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨g', hg'⟩ := hnorm d⁻¹ g
    have h2 : σ g (δ d x) = δ d (σ g' x) := by
      have h := congrArg (δ d) (hg' (δ d x))
      simpa using h
    exact ⟨σ g' x, isInvariant_of_submodule σ hsmul W g' x hx, h2.symm⟩)

@[simp]
theorem mem_mapSubmodule {d : D} {W : Submodule (MonoidAlgebra (ZMod 2) M) X}
    {y : X} :
    y ∈ mapSubmodule σ δ hsmul hnorm d W ↔ ∃ x ∈ W, δ d x = y := by
  change y ∈ (W.restrictScalars (ZMod 2)).map (δ d) ↔ ∃ x ∈ W, δ d x = y
  exact Submodule.mem_map

theorem delta_injective (d : D) : Function.Injective (δ d) := by
  intro x y hxy
  have h := congrArg (δ d⁻¹) hxy
  simpa using h

@[simp]
theorem mapSubmodule_one (W : Submodule (MonoidAlgebra (ZMod 2) M) X) :
    mapSubmodule σ δ hsmul hnorm 1 W = W := by
  ext y
  rw [mem_mapSubmodule]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨y, hy, by simp⟩

@[simp]
theorem mapSubmodule_mul (d₁ d₂ : D)
    (W : Submodule (MonoidAlgebra (ZMod 2) M) X) :
    mapSubmodule σ δ hsmul hnorm (d₁ * d₂) W =
      mapSubmodule σ δ hsmul hnorm d₁
        (mapSubmodule σ δ hsmul hnorm d₂ W) := by
  ext y
  simp only [mem_mapSubmodule]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨δ d₂ x, ⟨x, hx, rfl⟩, by rw [map_mul]; rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by rw [map_mul]; rfl⟩

@[expose] noncomputable def preimageSubmodule (d : D)
    (V : Submodule (MonoidAlgebra (ZMod 2) M) X) :
    Submodule (MonoidAlgebra (ZMod 2) M) X :=
  submoduleOfIsInvariant σ hsmul ((V.restrictScalars (ZMod 2)).comap (δ d)) (by
    intro g y hy
    obtain ⟨g', hg'⟩ := hnorm d g
    change δ d (σ g y) ∈ V
    rw [hg' y]
    exact isInvariant_of_submodule σ hsmul V g' (δ d y) hy)

@[simp]
theorem mem_preimageSubmodule {d : D} {V : Submodule (MonoidAlgebra (ZMod 2) M) X}
    {y : X} :
    y ∈ preimageSubmodule σ δ hsmul hnorm d V ↔ δ d y ∈ V := Iff.rfl

theorem mapSubmodule_isSimple (d : D)
    {W : Submodule (MonoidAlgebra (ZMod 2) M) X} [IsSimpleModule
      (MonoidAlgebra (ZMod 2) M) W] :
    IsSimpleModule (MonoidAlgebra (ZMod 2) M)
      (mapSubmodule σ δ hsmul hnorm d W) := by
  rw [isSimpleModule_iff_isAtom]
  refine (isAtom_iff_le_of_ge).2 ⟨?_, ?_⟩
  · intro hbot
    have hWbot : W = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hx' : δ d x ∈ mapSubmodule σ δ hsmul hnorm d W := by
        rw [mem_mapSubmodule]
        exact ⟨x, hx, rfl⟩
      rw [hbot] at hx'
      have hx0 : δ d x = 0 := by simpa using hx'
      exact delta_injective δ d (by simpa using hx0)
    exact (Submodule.nontrivial_iff_ne_bot.mp
      (IsSimpleModule.nontrivial (MonoidAlgebra (ZMod 2) M) W)) hWbot
  · intro V hVne hVle
    have hpre_ne : preimageSubmodule σ δ hsmul hnorm d V ≠ ⊥ := by
      intro hbot
      apply hVne
      rw [Submodule.eq_bot_iff]
      intro y hy
      have hy' : y ∈ mapSubmodule σ δ hsmul hnorm d W := hVle hy
      rw [mem_mapSubmodule] at hy'
      obtain ⟨x, hx, rfl⟩ := hy'
      have hxpre : x ∈ preimageSubmodule σ δ hsmul hnorm d V := by
        rwa [mem_preimageSubmodule]
      rw [hbot] at hxpre
      have hxzero : x = 0 := by simpa using hxpre
      rw [hxzero, map_zero]
    have hpre_le : preimageSubmodule σ δ hsmul hnorm d V ≤ W := by
      intro x hx
      rw [mem_preimageSubmodule] at hx
      have hmap : δ d x ∈ mapSubmodule σ δ hsmul hnorm d W := hVle hx
      rw [mem_mapSubmodule] at hmap
      obtain ⟨y, hy, hxy⟩ := hmap
      have hyx : y = x := delta_injective δ d hxy
      simpa [hyx] using hy
    have hWatom : IsAtom W :=
      (isSimpleModule_iff_isAtom).1 (inferInstance : IsSimpleModule
        (MonoidAlgebra (ZMod 2) M) W)
    rcases hWatom.le_iff.1 hpre_le with h | h
    · exact (hpre_ne h).elim
    · intro y hy
      rw [mem_mapSubmodule] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hxpre : x ∈ preimageSubmodule σ δ hsmul hnorm d V := by
        rw [h]
        exact hx
      rwa [mem_preimageSubmodule] at hxpre

end Normalizer

end GroupAlgebra

@[expose] def representationHom (δ : Representation (ZMod 2) D X) :
    D →* Module.End (ZMod 2) X :=
  δ

@[expose] noncomputable def unitRep (δ : Representation (ZMod 2) D X) :
    D →* (Module.End (ZMod 2) X)ˣ where
  toFun d :=
    { val := δ d
      inv := δ d⁻¹
      val_inv := by rw [← map_mul, mul_inv_cancel, map_one]
      inv_val := by rw [← map_mul, inv_mul_cancel, map_one] }
  map_one' := Units.ext (map_one δ)
  map_mul' d e := Units.ext (map_mul δ d e)

@[simp]
theorem unitRep_apply (δ : Representation (ZMod 2) D X) (d : D) :
    ((unitRep δ d : (Module.End (ZMod 2) X)ˣ) : Module.End (ZMod 2) X) = δ d := rfl

@[simp]
theorem unitRep_ker (δ : Representation (ZMod 2) D X) :
    (unitRep δ).ker = δ.ker := by
  ext d
  simp [MonoidHom.mem_ker, Units.ext_iff]

section Restrict

variable {G : Type*} [Group G]

@[expose] def restrictToSubmodule (ρ : Representation (ZMod 2) G X) (Z : Submodule (ZMod 2) X)
    (hZ : ∀ g, ∀ z ∈ Z, ρ g z ∈ Z) : Representation (ZMod 2) G Z where
  toFun g := (ρ g).restrict (p := Z) (q := Z) (hZ g)
  map_one' := by ext z; simp
  map_mul' g h := by ext z; simp

@[simp]
theorem restrictToSubmodule_apply (ρ : Representation (ZMod 2) G X)
    (Z : Submodule (ZMod 2) X) (hZ : ∀ g, ∀ z ∈ Z, ρ g z ∈ Z)
    (g : G) (z : Z) :
    ((restrictToSubmodule ρ Z hZ g z : Z) : X) = ρ g (z : X) := rfl

theorem restrictToSubmodule_isSimpleRep
    (σ : Representation (ZMod 2) M X) (Z : Submodule (ZMod 2) X)
    (hZ : ∀ g, ∀ z ∈ Z, σ g z ∈ Z)
    (hZne : Z ≠ ⊥)
    (hZsimple : ∀ W : Submodule (ZMod 2) X, W ≤ Z →
      (∀ g, ∀ w ∈ W, σ g w ∈ W) → W = ⊥ ∨ W = Z) :
    CFSG.Quasithin.SmithCurtis.IsSimpleRep (restrictToSubmodule σ Z hZ) := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.mpr hZne, ?_⟩
  intro W hW
  have hW'le : W.map Z.subtype ≤ Z := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hW'inv : ∀ g, ∀ w ∈ W.map Z.subtype, σ g w ∈ W.map Z.subtype := by
    intro g w hw
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
    exact Submodule.mem_map_of_mem (f := Z.subtype) (hW g z hz)
  have hinj : Function.Injective (Submodule.map Z.subtype) :=
    Submodule.map_injective_of_injective (Subtype.coe_injective)
  rcases hZsimple (W.map Z.subtype) hW'le hW'inv with h | h
  · left
    apply hinj
    rw [h, Submodule.map_bot]
  · right
    apply hinj
    rw [h, Submodule.map_top, Submodule.range_subtype]

theorem restrictToSubmodule_isIrreducible
    (σ : Representation (ZMod 2) M X) (Z : Submodule (ZMod 2) X)
    (hZ : ∀ g, ∀ z ∈ Z, σ g z ∈ Z)
    (hZne : Z ≠ ⊥)
    (hZsimple : ∀ W : Submodule (ZMod 2) X, W ≤ Z →
      (∀ g, ∀ w ∈ W, σ g w ∈ W) → W = ⊥ ∨ W = Z) :
    Representation.IsIrreducible (restrictToSubmodule σ Z hZ) := by
  have hrep := restrictToSubmodule_isSimpleRep σ Z hZ hZne hZsimple
  have hZnt : Nontrivial Z := Submodule.nontrivial_iff_ne_bot.mpr hZne
  have hsubnt : Nontrivial (Submodule (ZMod 2) Z) :=
    (Submodule.nontrivial_iff (R := ZMod 2) (M := Z)).mpr hZnt
  have hrepnt : Nontrivial (Subrepresentation (restrictToSubmodule σ Z hZ)) := by
    refine ⟨⊥, ⊤, ?_⟩
    intro h
    have h' : (⊥ : Subrepresentation (restrictToSubmodule σ Z hZ)).toSubmodule =
        (⊤ : Subrepresentation (restrictToSubmodule σ Z hZ)).toSubmodule :=
      congrArg Subrepresentation.toSubmodule h
    have h'' : (⊥ : Submodule (ZMod 2) Z) = ⊤ := by
      change (⊥ : Subrepresentation (restrictToSubmodule σ Z hZ)).toSubmodule =
        (⊤ : Subrepresentation (restrictToSubmodule σ Z hZ)).toSubmodule
      exact h'
    exact @bot_ne_top (Submodule (ZMod 2) Z) _ _ hsubnt h''
  change IsSimpleOrder (Subrepresentation (restrictToSubmodule σ Z hZ))
  refine @IsSimpleOrder.of_forall_eq_top
    (Subrepresentation (restrictToSubmodule σ Z hZ)) _ _ hrepnt ?_
  intro U hUne
  rcases hrep.2 U.toSubmodule U.apply_mem_toSubmodule with h | h
  · exact (hUne (Subrepresentation.toSubmodule_injective h)).elim
  · exact Subrepresentation.toSubmodule_injective h

end Restrict

@[expose] def restrictToRange (δ : Representation (ZMod 2) D X) (Z : Submodule (ZMod 2) X)
    (hZ : ∀ d, ∀ z ∈ Z, δ d z ∈ Z) :
    Representation (ZMod 2) (MonoidHom.mrange (representationHom δ)) Z where
  toFun f := (f.1 : Module.End (ZMod 2) X).restrict (p := Z) (q := Z) (by
    intro z hz
    obtain ⟨d, hd⟩ := f.2
    rw [← hd]
    exact hZ d z hz)
  map_one' := by ext z; simp
  map_mul' f g := by ext z; simp

@[simp]
theorem restrictToRange_apply (δ : Representation (ZMod 2) D X) (Z : Submodule (ZMod 2) X)
    (hZ : ∀ d, ∀ z ∈ Z, δ d z ∈ Z)
    (f : MonoidHom.mrange (representationHom δ)) (z : Z) :
    ((restrictToRange δ Z hZ f z : Z) : X) = (f.1 : Module.End (ZMod 2) X) (z : X) := rfl

end CFSG.HardMathSupport.GuralnickMalle

end

