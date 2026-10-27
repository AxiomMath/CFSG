
module

public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.Monster.B.Classical.E6AdjointTable
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Blueprint.Catalog
public import Certificates.Data.CFSGNative.Chevalley.C2E6StdMatrix
public import CFSG.LieType.Chevalley.C2E6StdMatrixVec
public import CFSG.LieType.Chevalley.C2E6StdMatrixData
public import CFSG.LieType.Chevalley.C2E6StdMatrixModelInputs
public meta import Certificates.Data.CFSGNative.Chevalley.C2E6StdMatrix
public meta import CFSG.LieType.Chevalley.C2E6StdMatrixData
public meta import CFSG.Monster.B.Classical.E6AdjointTable
import CFSG.Monster.B.Classical.E6AdjointGroup
import CFSG.Monster.B.E6.StdF4LeviRank
import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
import CFSG.LieType.Chevalley.C2E6FirstResidueLevi
import CFSG.LieType.Chevalley.FoldedWeylIdentification
import CFSG.LieType.Chevalley.C2E6FirstResidueGeometry
import CFSG.LieType.Chevalley.TwistedE6FieldTwoCyclicKernel
import all CFSG.Fischer.F4
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public meta import Certificates.Certificate114
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Chevalley.C2E6A5ExteriorCubeModel
import CFSG.LieType.Chevalley.C2E6D4NaturalOrthogonal
import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
import CFSG.LieType.Chevalley.C2E6FourthResidueMinusEight
import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LieType.Chevalley.TwistedE6FieldTwoRelativeData
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Monster.B.Geometry.CoxeterWords
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Certificates.Certificate1953
import Certificates.Certificate1954
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.LieType.Chevalley.C2E6Std.MatrixModel

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.Monster.B.Classical.E6Adjoint

theorem vecOf_mask (m : ℕ) (k : Fin 78) : vecOf (m, 0) k = if m.testBit k then 1 else 0 := by
  cases h : m.testBit k <;> simp [vecOf, h, ofBits_false, ofBits_true_false]

theorem single_lab_apply (l k : Fin 78) :
    (Finsupp.single (lab l) (1 : K)) (lab k) = if (l : ℕ) = k then 1 else 0 := by
  rw [Finsupp.single_apply]
  by_cases h : l = k
  · subst h; simp
  · have h1 : lab l ≠ lab k := fun e => h (CFSG.Monster.B.E6.StdF4.lab_bijective.1 e)
    have h2 : (l : ℕ) ≠ k := fun e => h (Fin.ext e)
    simp [h1, h2]

theorem toMat_ofFn (f : ℕ → Native.Vec) (k l : Fin 78) :
    toMat ((List.range 78).toArray.map f) k l = vecOf (f l) k := by
  simp [toMat, Array.getD_eq_getD_getElem?]

theorem certRoot_neg_simple :
    ∀ i : Fin Tag.E6.rank, e6Certificate.root (6 + 2 * i) = -Pi.single i 1 := by
  decide

theorem twelve_add_lt (i : Fin Tag.E6.rank) : 12 + 2 * (i : ℕ) < 78 := by
  have := CFSG.Monster.B.E6.StdF4.val_lt_six i
  omega

theorem rootVec_neg_single (i : Fin Tag.E6.rank) :
    rootVec Tag.E6 K (-Pi.single i 1) = Finsupp.single (lab ⟨12 + 2 * i, twelve_add_lt i⟩) 1 := by
  rw [CFSG.Monster.B.Classical.E6Adjoint.rootVec_eq_single (isRoot_neg_single Tag.E6 i),
    lab_of_ge (by simp only [not_lt]; omega)]
  congr 3
  rw [show (12 + 2 * (i : ℕ)) - 6 = 6 + 2 * i by omega, certRoot_neg_simple]

section SLP

variable {M N : Type*} [Monoid M] [Monoid N]

@[expose] def lineProdG (vals : Array M) (line : List ℕ) : M :=
  line.foldl (fun acc i => acc * vals.getD i 1) 1

@[expose] def slpRunG (gens : Array M) (prog : List (List ℕ)) : Array M :=
  prog.foldl (fun vals line => vals.push (lineProdG vals line)) gens

theorem getD_map {α β : Type*} (f : α → β) (arr : Array α) (i : ℕ) (d : α) :
    (arr.map f).getD i (f d) = f (arr.getD i d) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases arr[i]? <;> rfl

theorem map_lineProdG (φ : M →* N) (vals : Array M) (line : List ℕ) :
    φ (lineProdG vals line) = lineProdG (vals.map φ) line := by
  have h : ∀ acc : M, φ (line.foldl (fun acc i => acc * vals.getD i 1) acc) =
      line.foldl (fun acc i => acc * (vals.map φ).getD i 1) (φ acc) := by
    induction line with
    | nil => intro acc; rfl
    | cons i line ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, ih, map_mul, ← map_one φ, getD_map, map_one]
  rw [lineProdG, lineProdG, h, map_one]

theorem map_slpRunG (φ : M →* N) (gens : Array M) (prog : List (List ℕ)) :
    (slpRunG gens prog).map φ = slpRunG (gens.map φ) prog := by
  induction prog generalizing gens with
  | nil => rfl
  | cons line prog ih =>
    rw [slpRunG, List.foldl_cons, ← slpRunG, ih, Array.map_push, map_lineProdG]
    rfl

theorem getD_mem {G : Type*} [Group G] (H : Subgroup G) {arr : Array G}
    (h : ∀ x ∈ arr, x ∈ H) (i : ℕ) : arr.getD i 1 ∈ H := by
  rw [Array.getD_eq_getD_getElem?]
  cases e : arr[i]? with
  | none => exact H.one_mem
  | some y => exact h y (Array.mem_of_getElem? e)

theorem lineProdG_mem {G : Type*} [Group G] (H : Subgroup G) {vals : Array G}
    (hg : ∀ x ∈ vals, x ∈ H) (line : List ℕ) : lineProdG vals line ∈ H := by
  have h : ∀ acc ∈ H, line.foldl (fun acc i => acc * vals.getD i 1) acc ∈ H := by
    induction line with
    | nil => exact fun acc h => h
    | cons i line ih => exact fun acc hacc => ih _ (H.mul_mem hacc (getD_mem H hg i))
  exact h 1 H.one_mem

theorem slpRunG_mem {G : Type*} [Group G] (H : Subgroup G) {gens : Array G}
    (hg : ∀ x ∈ gens, x ∈ H) (prog : List (List ℕ)) : ∀ x ∈ slpRunG gens prog, x ∈ H := by
  induction prog generalizing gens with
  | nil => exact hg
  | cons line prog ih =>
    refine ih fun x hx => ?_
    rcases Array.mem_push.1 hx with hx | rfl
    · exact hg x hx
    · exact lineProdG_mem H hg line

theorem toMat_lineProd (vals : Array Native.Mat) (line : List ℕ) :
    toMat (Native.lineProd vals line) = lineProdG (vals.map toMat) line := by
  have h : ∀ acc, toMat (line.foldl (fun acc i => Native.mul acc (vals.getD i Native.one)) acc) =
      line.foldl (fun acc i => acc * (vals.map toMat).getD i 1) (toMat acc) := by
    induction line with
    | nil => intro acc; rfl
    | cons i line ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, ih, toMat_mul, ← toMat_one, getD_map]
  rw [Native.lineProd, lineProdG, h, toMat_one]

theorem toMat_slpRun (gens : Array Native.Mat) (prog : List (List ℕ)) :
    (Native.slpRun gens prog).map toMat = slpRunG (gens.map toMat) prog := by
  induction prog generalizing gens with
  | nil => rfl
  | cons line prog ih =>
    rw [Native.slpRun, List.foldl_cons, ← Native.slpRun, ih, Array.map_push, toMat_lineProd]
    rfl

end SLP

open C2E6Std

theorem mem_orbitField_of_card_two {a : Fin TwistTag.E6.foldedTag.rank}
    (ha : (TwistTag.E6.orbit a).card = 2) (c : K) : c ∈ orbitField TwistTag.E6 K barHom a := by
  rw [mem_orbitField, ha, pow_two, RingHom.coe_mul, Function.comp_apply]
  exact bar_bar c

noncomputable def xL
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K barHom a) :
    ModGL Tag.E6 K :=
  (orbitX TwistTag.E6 K barHom a c : ModGL TwistTag.E6.tag K)

noncomputable def nL
    (a : Fin TwistTag.E6.foldedTag.rank) : ModGL Tag.E6 K :=
  canonicalRep (coxeterSystem Tag.E6) K (TwistTag.E6.orbitReflection a)

theorem foldedRank_eq : TwistTag.E6.foldedTag.rank = 4 := by decide

abbrev fa (i : Fin 4) : Fin TwistTag.E6.foldedTag.rank := Fin.cast foldedRank_eq.symm i

private theorem card_orbit_zero : (TwistTag.E6.orbit (fa 0)).card = 2 := by decide
private theorem card_orbit_one : (TwistTag.E6.orbit (fa 1)).card = 2 := by decide

noncomputable def pc (a : Fin TwistTag.E6.foldedTag.rank) (ha : (TwistTag.E6.orbit a).card = 2)
    (c : K) : orbitField TwistTag.E6 K barHom a :=
  ⟨c, mem_orbitField_of_card_two ha c⟩

theorem xL_mem
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K barHom a) :
    xL a c ∈ stdGroup :=
  graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 barHom a c)

theorem nL_mem
    (a : Fin TwistTag.E6.foldedTag.rank) : nL a ∈ stdGroup :=
  canonicalRep_mem_graphFixedRootGroup (TwistTag.E6.orbitReflection_mem a)

private theorem ofBits_one : ofBits true false = (1 : K) := ofBits_true_false

theorem card_orbit_two : (TwistTag.E6.orbit (fa 2)).card = 1 := by decide

theorem card_orbit_three : (TwistTag.E6.orbit (fa 3)).card = 1 := by decide

private theorem c_one {a : Fin TwistTag.E6.foldedTag.rank} :
    ((1 : orbitField TwistTag.E6 K barHom a) : K) = ofBits true false := ofBits_one.symm

private theorem prod_two {M : Type*} [Monoid M] (x y : M) : [x, y].prod = x * y := by
  simp

private theorem prod_one {M : Type*} [Monoid M] (x : M) : [x].prod = x := by
  simp

private theorem orbitWord_fa0 : TwistTag.E6.orbitWord (fa 0) =
    ([⟨0, by decide⟩, ⟨5, by decide⟩] : List (Fin TwistTag.E6.tag.rank)) := by decide

private theorem orbitWord_fa1 : TwistTag.E6.orbitWord (fa 1) =
    ([⟨2, by decide⟩, ⟨4, by decide⟩] : List (Fin TwistTag.E6.tag.rank)) := by decide

private theorem orbitWord_fa2 : TwistTag.E6.orbitWord (fa 2) =
    ([⟨3, by decide⟩] : List (Fin TwistTag.E6.tag.rank)) := by decide

private theorem orbitWord_fa3 : TwistTag.E6.orbitWord (fa 3) =
    ([⟨1, by decide⟩] : List (Fin TwistTag.E6.tag.rank)) := by decide

theorem barHom_surjective : Function.Surjective barHom := fun c => ⟨bar c, bar_bar c⟩

theorem stdGroup_le_of
    {H : Subgroup (ModGL Tag.E6 K)} (hx : ∀ a c, xL a c ∈ H)
    (hn : ∀ a, nL a ∈ H) : stdGroup ≤ H := by
  let φ : WeylGroup TwistTag.E6.tag →* ModGL Tag.E6 K := canonicalRepHom
  have hW : relWeylTwist TwistTag.E6 ≤ H.comap φ := by
    rw [relWeylTwist_eq_closure, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact hn a
  change graphFixedRootGroup TwistTag.E6 K barHom ≤ H
  rw [graphFixedRootGroup_eq_closure barHom barHom_surjective]
  refine (Subgroup.closure_le H).2 ?_
  rintro _ ⟨w, hw, a, c, rfl⟩
  have hnw : canonicalRep (coxeterSystem TwistTag.E6.tag) K w ∈ H := hW hw
  exact H.mul_mem (H.mul_mem hnw (hx a c)) (H.inv_mem hnw)

theorem xL_zero
    (a : Fin TwistTag.E6.foldedTag.rank)
    (h : (0 : K) ∈ orbitField TwistTag.E6 K barHom a) : xL a ⟨0, h⟩ = 1 := by
  rw [xL, coe_orbitX]
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  exact Units.ext (by rw [coe_xUnit, map_zero, xOp_zero]; rfl)

private theorem K_cases (c : K) : c = 0 ∨ c = ofBits true false ∨ c = ω ∨ c = ω ^ 2 := by
  revert c; decide

private theorem bar_omega_ne : bar ω ≠ ω := by decide

private theorem bar_omega_sq_ne : bar (ω ^ 2) ≠ ω ^ 2 := by decide

theorem exists_fa (a : Fin TwistTag.E6.foldedTag.rank) : ∃ i, fa i = a :=
  ⟨Fin.cast foldedRank_eq a, Fin.ext rfl⟩

@[expose] def matA : Matrix (Fin 78) (Fin 78) K := toMat nativeAB.1

@[expose] def matB : Matrix (Fin 78) (Fin 78) K := toMat nativeAB.2

open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

private theorem wordProd_cons {G : Type*} [Group G] (x : ℕ → G) (l : ℕ × Bool)
    (v : List (ℕ × Bool)) :
    wordProd x (l :: v) = (if l.2 then x l.1 else (x l.1)⁻¹) * wordProd x v := by
  simp [wordProd]

theorem nonempty_mulEquiv_stdGroup_of_lieModel
    {X : Type} [Group X]
    (hX : CFSG.Blueprint.LieModel X .twistedE6 0 2 1) : Nonempty (X ≃* stdGroup) := by
  rcases hX with ⟨hc, -⟩ | ⟨-, -, hX⟩ | ⟨-, hr, -⟩ | ⟨-, hs, -⟩
  · exact absurd hc (by decide)
  · obtain ⟨L, _, _, σ, hL, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hX
    obtain ⟨e'⟩ := nonempty_mulEquiv_stdGroup_of_card_eq_four (by rw [hL]; norm_num)
      σ.toRingHom fun c => by simpa using hσ c
    exact ⟨e.trans e'⟩
  · exact absurd hr (by decide)
  · exact absurd hs (by decide)

end CFSG.LieType.Chevalley.C2E6Std.MatrixModel
