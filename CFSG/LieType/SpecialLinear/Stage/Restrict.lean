module

public import CFSG.Quasithin.Background.SmithCurtisBasic
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs

public section

namespace CFSG.LieType.SpecialLinear

open CFSG.Quasithin.SmithCurtis
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

noncomputable section

variable {E X D : Type} [Field E] [Algebra (ZMod 2) E]
  [AddCommGroup X] [Module (ZMod 2) X] [Module E X] [IsScalarTower (ZMod 2) E X]
  [Group D]

@[expose] def stageInclusion (X' : Submodule E X) : X' →ₗ[ZMod 2] X where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) E X] in
theorem stageInclusion_injective (X' : Submodule E X) :
    Function.Injective (stageInclusion X') := fun _ _ h => Subtype.ext h

@[expose] noncomputable def stageRestrict (δ : Representation (ZMod 2) D X)
    (X' : Submodule E X) (hX' : ∀ d, ∀ x ∈ X', δ d x ∈ X') :
    Representation (ZMod 2) D X' :=
  restrictRep δ (X'.restrictScalars (ZMod 2)) hX'

@[simp]
theorem coe_stageRestrict_apply (δ : Representation (ZMod 2) D X) (X' : Submodule E X)
    (hX' : ∀ d, ∀ x ∈ X', δ d x ∈ X') (d : D) (x : X') :
    ((stageRestrict δ X' hX' d x : X') : X) = δ d x :=
  restrictRep_apply δ (X'.restrictScalars (ZMod 2)) hX' d x

theorem stageRestrict_smul (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (X' : Submodule E X) (hX' : ∀ d, ∀ x ∈ X', δ d x ∈ X') :
    ∀ d (c : E) (x : X'),
      stageRestrict δ X' hX' d (c • x) = c • stageRestrict δ X' hX' d x := by
  intro d c x
  apply Subtype.ext
  simp only [coe_stageRestrict_apply, Submodule.coe_smul]
  exact hδE d c (x : X)

theorem stageRestrict_mul_self (δ : Representation (ZMod 2) D X)
    (hD2 : ∀ d, δ d * δ d = 1) (X' : Submodule E X)
    (hX' : ∀ d, ∀ x ∈ X', δ d x ∈ X') :
    ∀ d, stageRestrict δ X' hX' d * stageRestrict δ X' hX' d = 1 := by
  intro d
  ext x
  have h := congrArg (fun f : X →ₗ[ZMod 2] X => f (x : X)) (hD2 d)
  simpa only [Module.End.mul_apply, coe_stageRestrict_apply, Module.End.one_apply] using h

theorem stageRestrict_quad (δ : Representation (ZMod 2) D X)
    (hquad : ∀ a b x, δ b (δ a x - x) = δ a x - x) (X' : Submodule E X)
    (hX' : ∀ d, ∀ x ∈ X', δ d x ∈ X') :
    ∀ a b (x : X'),
      stageRestrict δ X' hX' b (stageRestrict δ X' hX' a x - x) =
        stageRestrict δ X' hX' a x - x := by
  intro a b x
  apply Subtype.ext
  simp only [coe_stageRestrict_apply, Submodule.coe_sub]
  exact hquad a b (x : X)

section Transfer

variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {ρ' : Representation (ZMod 2) G W}
  {f : W →ₗ[ZMod 2] V}

theorem card_map_of_injective (hf : Function.Injective f)
    (Z : Submodule (ZMod 2) W) : Nat.card (Z.map f) = Nat.card Z :=
  (Nat.card_congr (Submodule.equivMapOfInjective f hf Z).toEquiv).symm

theorem cenOn_map_eq (hf : Function.Injective f)
    (hcomm : ∀ d w, f (ρ' d w) = ρ d (f w)) (A : Subgroup G)
    (Z : Submodule (ZMod 2) W) : cenOn ρ A (Z.map f) = cenOn ρ' A Z := by
  ext d
  constructor
  · rintro ⟨hdA, hd⟩
    refine ⟨hdA, fun z hz => ?_⟩
    apply hf
    rw [hcomm, hd (f z) (Submodule.mem_map_of_mem hz)]
  · rintro ⟨hdA, hd⟩
    refine ⟨hdA, ?_⟩
    rintro v ⟨z, hz, rfl⟩
    rw [← hcomm]
    exact congrArg f (hd z hz)

theorem map_fixOn_eq (hf : Function.Injective f)
    (hcomm : ∀ d w, f (ρ' d w) = ρ d (f w)) (A : Subgroup G)
    (Z : Submodule (ZMod 2) W) :
    (fixOn ρ' A Z).map f = fixOn ρ A (Z.map f) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨Submodule.mem_map_of_mem hw.1, fun d hd => by
      rw [← hcomm, hw.2 d hd]⟩
  · rintro ⟨hvZ, hvfix⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hvZ
    refine Submodule.mem_map.mpr ⟨z, ⟨hz, fun d hd => ?_⟩, rfl⟩
    apply hf
    rw [hcomm, hvfix d hd]

theorem card_fixOn_map (hf : Function.Injective f)
    (hcomm : ∀ d w, f (ρ' d w) = ρ d (f w)) (A : Subgroup G)
    (Z : Submodule (ZMod 2) W) :
    Nat.card (fixOn ρ A (Z.map f)) = Nat.card (fixOn ρ' A Z) := by
  rw [← map_fixOn_eq hf hcomm A Z]
  exact (Nat.card_congr
    (Submodule.equivMapOfInjective f hf (fixOn ρ' A Z)).toEquiv).symm

theorem isElemAbelianOn_map (hf : Function.Injective f)
    (hcomm : ∀ d w, f (ρ' d w) = ρ d (f w)) (A : Subgroup G)
    (Z : Submodule (ZMod 2) W) :
    IsElemAbelianOn ρ A (Z.map f) → IsElemAbelianOn ρ' A Z := by
  intro h a ha b hb
  constructor
  · intro z hz
    apply hf
    rw [hcomm]
    exact (h a ha b hb).1 (f z) (Submodule.mem_map_of_mem hz)
  · intro z hz
    apply hf
    rw [hcomm]
    exact (h a ha b hb).2 (f z) (Submodule.mem_map_of_mem hz)

theorem isOffenderOn_map (hf : Function.Injective f)
    (hcomm : ∀ d w, f (ρ' d w) = ρ d (f w)) (A : Subgroup G)
    (Z : Submodule (ZMod 2) W) :
    IsOffenderOn ρ A (Z.map f) → IsOffenderOn ρ' A Z := by
  rintro ⟨helem, hineq⟩
  refine ⟨isElemAbelianOn_map hf hcomm A Z helem, ?_⟩
  rw [← card_map_of_injective hf Z, ← cenOn_map_eq hf hcomm A Z,
    ← card_fixOn_map hf hcomm A Z]
  exact hineq

end Transfer

theorem stageRestrict_comm (δ : Representation (ZMod 2) D X) (X' : Submodule E X)
    (hX' : ∀ d, ∀ x ∈ X', δ d x ∈ X') (d : D) (x : X') :
    stageInclusion X' (stageRestrict δ X' hX' d x) = δ d (stageInclusion X' x) :=
  coe_stageRestrict_apply δ X' hX' d x

theorem stageRestrict_hered (δ : Representation (ZMod 2) D X) (X' : Submodule E X)
    (hX' : ∀ d, ∀ x ∈ X', δ d x ∈ X')
    (hered : ∀ Z : Submodule (ZMod 2) X,
      (∀ d, ∀ z ∈ Z, δ d z ∈ Z) → IsOffenderOn δ ⊤ Z) :
    ∀ Z' : Submodule (ZMod 2) X',
      (∀ d, ∀ z ∈ Z', stageRestrict δ X' hX' d z ∈ Z') →
        IsOffenderOn (stageRestrict δ X' hX') ⊤ Z' := by
  intro Z' hZ'
  have hZ : ∀ d, ∀ z ∈ Z'.map (stageInclusion X'), δ d z ∈ Z'.map (stageInclusion X') := by
    intro d z hz
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
    rw [← stageRestrict_comm δ X' hX' d w]
    exact Submodule.mem_map_of_mem (hZ' d w hw)
  exact isOffenderOn_map (stageInclusion_injective X')
    (stageRestrict_comm δ X' hX') ⊤ Z' (hered _ hZ)

end

end CFSG.LieType.SpecialLinear
