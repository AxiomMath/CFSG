module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredGeneration
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.RankThree.PartOne.S15K.LayerModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Holt.Fixed
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import Init.Data.List.Lemmas
public import Init.Data.List.OfFn
public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.IsCommutative
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Quaternion
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Range
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Data.Set.PowersetCard
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.Swap
public import Mathlib.LinearAlgebra.Multilinear.Basis
public import Mathlib.Logic.Equiv.Option
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.Fermat
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Order.WellFounded
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Tauto
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Frobenius
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PreservesTensors
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.SpecialIsogeny
public import TauCeti.LinearAlgebra.Dimension.DirectSum
public import TauCeti.LinearAlgebra.GeneralLinearGroup.Congr
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence
public import TauCeti.LinearAlgebra.RootSystem.RootLength

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private abbrev castSupport (_E : QuadExt F K (unitaryInvolution K 2 f)) {k n : ℕ}
    (h : k ≤ n) : Submodule F ((F × F) × (Fin n → K)) :=
  coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K)))
    (Finset.univ.map (Fin.castLEEmb h))

private noncomputable def castTo (_E : QuadExt F K (unitaryInvolution K 2 f)) {k n : ℕ}
    (h : k ≤ n) : ((F × F) × (Fin k → K)) →ₗ[F] ((F × F) × (Fin n → K)) where
  toFun v := (v.1, fun j => if hj : (j : ℕ) < k then v.2 ⟨(j : ℕ), hj⟩ else 0)
  map_add' v w := by
    refine Prod.ext rfl (funext fun j => ?_)
    by_cases hj : (j : ℕ) < k <;> simp [hj, map_add]
  map_smul' c v := by
    refine Prod.ext rfl (funext fun j => ?_)
    by_cases hj : (j : ℕ) < k <;> simp [hj, map_smul]

private theorem castTo_apply (_E : QuadExt F K (unitaryInvolution K 2 f)) {k n : ℕ}
    (h : k ≤ n) (v : (F × F) × (Fin k → K)) :
    castTo _E h v =
      (v.1, fun j : Fin n => if hj : (j : ℕ) < k then v.2 ⟨(j : ℕ), hj⟩ else 0) :=
  rfl

private theorem castRestr_castTo (_E : QuadExt F K (unitaryInvolution K 2 f)) {k n : ℕ}
    (h : k ≤ n) (v : (F × F) × (Fin k → K)) :
    castRestr h (castTo _E h v) = v := by
  refine Prod.ext rfl (funext fun i => ?_)
  have hi : ((Fin.castLE h i : Fin n) : ℕ) < k := by
    rw [Fin.val_castLE]
    exact i.2
  simp [castRestr, castTo_apply, hi]

private def castRestrLin (_E : QuadExt F K (unitaryInvolution K 2 f)) {k n : ℕ}
    (h : k ≤ n) : ((F × F) × (Fin n → K)) →ₗ[F] ((F × F) × (Fin k → K)) where
  toFun := castRestr h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem mem_coordSupport_refl_iff (_E : QuadExt F K (unitaryInvolution K 2 f))
    {n : ℕ} (S : Finset (Fin n)) (v : (F × F) × (Fin n → K)) :
    v ∈ coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S ↔
      ∀ j, j ∉ S → v.2 j = 0 := by
  classical
  revert v
  induction S using Finset.induction_on with
  | empty =>
      intro v
      rw [coordSupport_empty]
      constructor
      · intro hv j _
        obtain ⟨r, hr⟩ := mem_coordAnchor.mp hv
        rw [← hr]
        rfl
      · intro hv
        refine mem_coordAnchor.mpr ⟨v.1, ?_⟩
        refine Prod.ext rfl (funext fun j => ?_)
        simpa using (hv j (by simp)).symm
  | insert i S hi ih =>
      intro v
      rw [coordSupport_insert _ hi]
      constructor
      · intro hv j hj
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
        have hji : j ≠ i := fun hji => hj (hji ▸ Finset.mem_insert_self i S)
        have hjS : j ∉ S := fun h => hj (Finset.mem_insert_of_mem h)
        have ha' : a.2 j = 0 := (ih a).mp ha j hjS
        have hb' : b.2 j = 0 := by
          obtain ⟨e, rfl⟩ := mem_coordPlane.mp hb
          change ((0, Pi.single i e) : (F × F) × (Fin n → K)).2 j = 0
          simp [Pi.single_eq_of_ne hji]
        simp [ha', hb']
      · intro hv
        have hmem1 : v - (0, Pi.single i (v.2 i)) ∈
            coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S := by
          refine (ih (v - (0, Pi.single i (v.2 i)))).mpr fun j hj => ?_
          rcases eq_or_ne j i with hji | hji
          · subst hji
            simp [Pi.single_eq_same]
          · have hvj : v.2 j = 0 := hv j (by simp [hji, hj])
            simp [Pi.single_eq_of_ne hji, hvj]
        have hmem2 : (0, Pi.single i (v.2 i)) ∈
            coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i :=
          mem_coordPlane.mpr ⟨v.2 i, rfl⟩
        rw [← sub_add_cancel v (0, Pi.single i (v.2 i))]
        exact Submodule.add_mem _
          (Submodule.mem_sup_left hmem1) (Submodule.mem_sup_right hmem2)

private theorem mem_castSupport_iff {k n : ℕ} (h : k ≤ n) (j : Fin n) :
    j ∈ Finset.univ.map (Fin.castLEEmb h) ↔ (j : ℕ) < k := by
  constructor
  · intro hj
    obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hj
    rw [← hi, Fin.castLEEmb_apply, Fin.val_castLE]
    exact i.2
  · intro hj
    refine Finset.mem_map.mpr ⟨⟨(j : ℕ), hj⟩, Finset.mem_univ _, ?_⟩
    rw [Fin.castLEEmb_apply]
    exact Fin.ext rfl

private theorem castTo_mem (_E : QuadExt F K (unitaryInvolution K 2 f)) {k n : ℕ}
    (h : k ≤ n) (v : (F × F) × (Fin k → K)) :
    castTo _E h v ∈ castSupport _E h := by
  change castTo _E h v ∈
    coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K)))
      (Finset.univ.map (Fin.castLEEmb h))
  rw [mem_coordSupport_refl_iff _E]
  intro j hj
  have hj' : ¬ (j : ℕ) < k := fun hlt => hj ((mem_castSupport_iff h j).mpr hlt)
  simp [castTo_apply, hj']

private theorem castTo_injective (_E : QuadExt F K (unitaryInvolution K 2 f)) {k n : ℕ}
    (h : k ≤ n) : Function.Injective (castTo _E h) := by
  intro v w hvw
  have h := congrArg (castRestr h) hvw
  simpa [castRestr_castTo] using h

private theorem castTo_castRestr (_E : QuadExt F K (unitaryInvolution K 2 f)) {k n : ℕ}
    (h : k ≤ n) {v : (F × F) × (Fin n → K)} (hv : v ∈ castSupport _E h) :
    castTo _E h (castRestr h v) = v := by
  have hv' : ∀ j, j ∉ Finset.univ.map (Fin.castLEEmb h) → v.2 j = 0 :=
    (mem_coordSupport_refl_iff _E (S := Finset.univ.map (Fin.castLEEmb h)) v).mp hv
  refine Prod.ext rfl (funext fun j => ?_)
  by_cases hj : (j : ℕ) < k
  · simp [castRestr, castTo_apply, hj]
  · have hjm : j ∉ Finset.univ.map (Fin.castLEEmb h) := fun hmem =>
      hj ((mem_castSupport_iff h j).mp hmem)
    simp [castRestr, castTo_apply, hj, hv' j hjm]

private noncomputable def castEquivCoord (_E : QuadExt F K (unitaryInvolution K 2 f))
    {k n : ℕ} (h : k ≤ n) :
    ((F × F) × (Fin k → K)) ≃ₗ[F] castSupport _E h :=
  LinearEquiv.ofLinearMap
    ((castTo _E h).codRestrict (castSupport _E h) (castTo_mem _E h))
    ((castRestrLin _E h).domRestrict (castSupport _E h))
    (by
      apply LinearMap.ext
      intro a
      apply Subtype.ext
      change castTo _E h (castRestr h (a : (F × F) × (Fin n → K))) =
        (a : (F × F) × (Fin n → K))
      exact castTo_castRestr _E h a.2)
    (by
      apply LinearMap.ext
      intro v
      change castRestr h (castTo _E h v) = v
      exact castRestr_castTo _E h v)

private theorem castEquivCoord_apply (_E : QuadExt F K (unitaryInvolution K 2 f))
    {k n : ℕ} (h : k ≤ n) (v : (F × F) × (Fin k → K)) :
    ((castEquivCoord _E h v : castSupport _E h) : (F × F) × (Fin n → K)) =
      castTo _E h v := by
  rfl

private theorem castEquivCoord_symm_apply (_E : QuadExt F K (unitaryInvolution K 2 f))
    {k n : ℕ} (h : k ≤ n) (a : castSupport _E h) :
    (castEquivCoord _E h).symm a =
      castRestr h (a : (F × F) × (Fin n → K)) := by
  rfl

private noncomputable def coordIsometry {k n : ℕ} (h : k ≤ n) :
    (normHypForm E k).IsometryEquiv
      ((normHypForm E n).comp (castSupport E h).subtype) where
  toLinearEquiv := castEquivCoord E h
  map_app' := by
    intro v
    change normHypForm E n (castTo E h v) = normHypForm E k v
    rw [normHypForm_eq_castRestr_add E h (castTo E h v)]
    have hzero : (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k),
        normQuad E ((castTo E h v).2 j)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' : ¬ (j : ℕ) < k := (Finset.mem_filter.mp hj).2
      rw [castTo_apply]
      simp [hj']
    rw [castRestr_castTo, hzero, add_zero]

private theorem polar_eq_zero_of_mem_coordSupport_refl {n : ℕ} (S : Finset (Fin n))
    (v : (F × F) × (Fin n → K)) (hv1 : v.1 = 0) (hvS : ∀ j ∈ S, v.2 j = 0) :
    ∀ w ∈ coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S,
      polar (normHypForm E n) w v = 0 := by
  classical
  revert v hv1 hvS
  induction S using Finset.induction_on with
  | empty =>
      intro v hv1 hvS w hw
      rw [coordSupport_empty] at hw
      obtain ⟨r, rfl⟩ := mem_coordAnchor.mp hw
      change polar (normHypForm E n) ((r, 0) : (F × F) × (Fin n → K)) v = 0
      rw [polar_hypSum]
      simp [hv1]
  | insert i S hi ih =>
      intro v hv1 hvS w hw
      rw [coordSupport_insert _ hi] at hw
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
      rw [polar_add_left]
      have h1 : polar (normHypForm E n) a v = 0 :=
        ih v hv1 (fun j hj => hvS j (Finset.mem_insert_of_mem hj)) a ha
      have h2 : polar (normHypForm E n) b v = 0 := by
        obtain ⟨e, rfl⟩ := mem_coordPlane.mp hb
        change polar (normHypForm E n) ((0, Pi.single i e) : (F × F) × (Fin n → K)) v = 0
        rw [polar_comm, polar_hypSum, polar_Qn_single,
          hvS i (Finset.mem_insert_self i S)]
        simp
      rw [h1, h2, add_zero]

private theorem mem_suppPerp_coordSupport_refl_iff_forward {n : ℕ} (S : Finset (Fin n))
    (v : (F × F) × (Fin n → K))
    (hv : v ∈ suppPerp (normHypForm E n)
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S)) :
    v.1 = 0 ∧ ∀ j ∈ S, v.2 j = 0 := by
  classical
  revert v
  induction S using Finset.induction_on with
  | empty =>
      intro v hv
      rw [coordSupport_empty] at hv
      have h1 : v.1.2 = 0 := by
        have h := mem_suppPerp.mp hv ((1, 0), 0)
          (mem_coordAnchor.mpr ⟨(1, 0), rfl⟩)
        rw [polar_hypSum] at h
        simpa using h
      have h2 : v.1.1 = 0 := by
        have h := mem_suppPerp.mp hv ((0, 1), 0)
          (mem_coordAnchor.mpr ⟨(0, 1), rfl⟩)
        rw [polar_hypSum] at h
        simpa using h
      exact ⟨Prod.ext h2 h1, fun j hj => by simp at hj⟩
  | insert i S hi ih =>
      intro v hv
      rw [coordSupport_insert _ hi] at hv
      have hvS : v ∈ suppPerp (normHypForm E n)
          (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S) := by
        rw [mem_suppPerp]
        intro w hw
        exact mem_suppPerp.mp hv w (Submodule.mem_sup_left hw)
      obtain ⟨hv1, hv2⟩ := ih v hvS
      refine ⟨hv1, fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst hji
        apply CFSG.ClassicalGroups.Orthogonal.eq_zero_of_polar_eq_zero
          (Q := normQuad E) (normQuad_polarBilin_nondegenerate E)
        intro y
        have h := mem_suppPerp.mp hv ((0, 0), Pi.single j y)
          (Submodule.mem_sup_right (mem_coordPlane.mpr ⟨y, rfl⟩))
        rw [polar_comm, polar_hypSum, polar_Qn_single] at h
        simpa using h
      · exact hv2 j hjS

theorem mem_suppPerp_coordSupport_refl_iff {n : ℕ} (S : Finset (Fin n))
    (v : (F × F) × (Fin n → K)) :
    v ∈ suppPerp (normHypForm E n)
        (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S) ↔
      v.1 = 0 ∧ ∀ j ∈ S, v.2 j = 0 :=
  ⟨fun hv => mem_suppPerp_coordSupport_refl_iff_forward E S v hv,
   fun hv => mem_suppPerp.mpr
     (polar_eq_zero_of_mem_coordSupport_refl E S v hv.1 hv.2)⟩

private theorem mem_suppPerp_castSupport_iff {k n : ℕ} (h : k ≤ n)
    (v : (F × F) × (Fin n → K)) :
    v ∈ suppPerp (normHypForm E n) (castSupport E h) ↔
      v.1 = 0 ∧ ∀ j ∈ Finset.univ.map (Fin.castLEEmb h), v.2 j = 0 :=
  mem_suppPerp_coordSupport_refl_iff E
    (S := Finset.univ.map (Fin.castLEEmb h)) v

private theorem castEquiv_apply_of_mem_suppPerp {k n : ℕ} (h : k ≤ n)
    (g : ((F × F) × (Fin k → K)) ≃ₗ[F] ((F × F) × (Fin k → K)))
    {v : (F × F) × (Fin n → K)}
    (hv : v ∈ suppPerp (normHypForm E n) (castSupport E h)) :
    castEquiv h g v = v := by
  obtain ⟨hv1, hv2⟩ := (mem_suppPerp_castSupport_iff E h v).mp hv
  have hzero : castRestr h v = 0 := by
    refine Prod.ext hv1 (funext fun i => ?_)
    exact hv2 (Fin.castLE h i) ((mem_castSupport_iff h _).mpr (by
      rw [Fin.val_castLE]
      exact i.2))
  refine Prod.ext ?_ (funext fun j => ?_)
  · rw [castEquiv_apply, castLin_fst, hzero, hv1]
    simp
  · by_cases hj : (j : ℕ) < k
    · rw [castEquiv_apply, castLin_snd_of_lt h g.toLinearMap v hj, hzero]
      simp [hv2 j ((mem_castSupport_iff h j).mpr hj)]
    · rw [castEquiv_apply, castLin_snd_of_not_lt h g.toLinearMap v hj]

private theorem castEquiv_apply_of_mem_castSupport (_E : QuadExt F K (unitaryInvolution K 2 f))
    {k n : ℕ} (h : k ≤ n)
    (g : ((F × F) × (Fin k → K)) ≃ₗ[F] ((F × F) × (Fin k → K)))
    {v : (F × F) × (Fin n → K)} (hv : v ∈ castSupport _E h) :
    castEquiv h g v = castTo _E h (g (castRestr h v)) := by
  have hv' : ∀ j, j ∉ Finset.univ.map (Fin.castLEEmb h) → v.2 j = 0 :=
    (mem_coordSupport_refl_iff _E (S := Finset.univ.map (Fin.castLEEmb h)) v).mp hv
  refine Prod.ext ?_ (funext fun j => ?_)
  · rw [castEquiv_apply, castLin_fst]
    rfl
  · by_cases hj : (j : ℕ) < k
    · rw [castEquiv_apply, castLin_snd_of_lt h g.toLinearMap v hj, castTo_apply]
      simp [hj]
    · rw [castEquiv_apply, castLin_snd_of_not_lt h g.toLinearMap v hj, castTo_apply]
      have hjm : j ∉ Finset.univ.map (Fin.castLEEmb h) := fun hmem =>
        hj ((mem_castSupport_iff h j).mp hmem)
      simp [hj, hv' j hjm]

private theorem isCompl_castSupport {k n : ℕ} (h : k ≤ n) :
    IsCompl (castSupport E h) (suppPerp (normHypForm E n) (castSupport E h)) := by
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  refine isCompl_suppPerp (polarNondegOn_of_nondegenerate ?_)
  exact coordSupport_nondegenerate (LinearEquiv.refl F ((F × F) × (Fin n → K)))
    (fun v => by
      rw [show normHypForm E n v = hypPlane F v.1 + Qn E n v.2 from
        QuadraticMap.prod_apply (hypPlane F) (Qn E n) v]
      rw [Qn_apply]
      rfl)
    (normHypForm_polarBilin_nondegenerate E n)
    (normQuad_polarBilin_nondegenerate E) (Finset.univ.map (Fin.castLEEmb h))

private theorem normOmegaCast_mem_supportedDerived {k n : ℕ} (h : k ≤ n)
    (g : normOmega E k) :
    ((normOmegaCast E h g : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) ∈
      supportedDerived (normHypForm E n) (castSupport E h) := by
  refine mem_supportedDerived.mpr ⟨?_, ?_⟩
  · intro v hv
    exact castEquiv_apply_of_mem_suppPerp E h (g : ((F × F) × (Fin k → K)) ≃ₗ[F]
      ((F × F) × (Fin k → K))) hv
  · let w : castSupport E h ≃ₗ[F] castSupport E h :=
      CFSG.RankThree.PartOne.linConj (coordIsometry E h).toLinearEquiv
        (g : ((F × F) × (Fin k → K)) ≃ₗ[F] ((F × F) × (Fin k → K)))
    have hw : w ∈ orthDerived ((normHypForm E n).comp (castSupport E h).subtype) := by
      rw [← CFSG.RankThree.PartOne.map_orthDerived_linConj (coordIsometry E h)]
      exact Subgroup.mem_map_of_mem _ g.2
    refine ⟨w, hw, fun a => ?_⟩
    rw [normOmegaCast_apply]
    change ((w a : castSupport E h) : (F × F) × (Fin n → K)) =
      castEquiv h g (a : (F × F) × (Fin n → K))
    change ((castEquivCoord E h ((g : ((F × F) × (Fin k → K)) ≃ₗ[F]
        ((F × F) × (Fin k → K))) ((castEquivCoord E h).symm a)) :
        castSupport E h) : (F × F) × (Fin n → K)) =
      castEquiv h g (a : (F × F) × (Fin n → K))
    rw [castEquivCoord_symm_apply, castEquivCoord_apply,
      castEquiv_apply_of_mem_castSupport E h g a.2]

private theorem mem_range_normOmegaCast_of_mem_supportedDerived {k n : ℕ} (h : k ≤ n)
    (x : normOmega E n)
    (hx : ((x : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) ∈
      supportedDerived (normHypForm E n) (castSupport E h)) :
    x ∈ (normOmegaCast E h).range := by
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  obtain ⟨hxfix, w, hw, hxact⟩ := mem_supportedDerived.mp hx
  rw [← CFSG.RankThree.PartOne.map_orthDerived_linConj (coordIsometry E h)] at hw
  obtain ⟨g, hg, hg_eq⟩ := Subgroup.mem_map.mp hw
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [normOmegaCast_apply]
  obtain ⟨a, ha, b, hb, hab⟩ :=
    suppExists_add_of_isCompl (isCompl_castSupport E h) v
  rw [← hab, map_add, map_add]
  congr 1
  · have hlin :
        CFSG.RankThree.PartOne.linConj (coordIsometry E h).toLinearEquiv g ⟨a, ha⟩ =
          w ⟨a, ha⟩ := by
      simpa using congrArg
        (fun e : castSupport E h ≃ₗ[F] castSupport E h => e ⟨a, ha⟩) hg_eq
    calc
      castEquiv h g a = castTo E h (g (castRestr h a)) :=
        castEquiv_apply_of_mem_castSupport E h g ha
      _ = ((CFSG.RankThree.PartOne.linConj
            (coordIsometry E h).toLinearEquiv g ⟨a, ha⟩ : castSupport E h) :
          (F × F) × (Fin n → K)) := rfl
      _ = ((w ⟨a, ha⟩ : castSupport E h) : (F × F) × (Fin n → K)) := by rw [hlin]
      _ = (x : ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) a :=
        hxact ⟨a, ha⟩
  · rw [castEquiv_apply_of_mem_suppPerp E h g hb]
    exact (hxfix b hb).symm

private theorem coordSupport_normHypForm_nondegenerate {m : ℕ} (S : Finset (Fin m)) :
    (polarBilin ((normHypForm E m).comp
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin m → K))) S).subtype)).Nondegenerate := by
  exact coordSupport_nondegenerate (Q := normHypForm E m)
    (ψ := LinearEquiv.refl F ((F × F) × (Fin m → K)))
    (hψ := normHypForm_apply_coord E m)
    (hQ := normHypForm_polarBilin_nondegenerate E m)
    (hQE := normQuad_polarBilin_nondegenerate E) S

private theorem map_castEquivCoord_coordSupport {k n : ℕ} (h : k ≤ n)
    (S : Finset (Fin k)) :
    (coordSupport (LinearEquiv.refl F ((F × F) × (Fin k → K))) S).map
        (castEquivCoord E h).toLinearMap =
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K)))
        (S.map (Fin.castLEEmb h))).comap (castSupport E h).subtype := by
  ext a
  constructor
  · rintro ⟨v, hv, rfl⟩
    change ((castEquivCoord E h v : castSupport E h) :
      (F × F) × (Fin n → K)) ∈
      coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K)))
        (S.map (Fin.castLEEmb h))
    rw [castEquivCoord_apply,
      mem_coordSupport_refl_iff E (S.map (Fin.castLEEmb h)) (castTo E h v)]
    intro j hj
    rw [castTo_apply]
    dsimp only
    by_cases hjlt : (j : ℕ) < k
    · rw [dif_pos hjlt]
      have hjS : (⟨(j : ℕ), hjlt⟩ : Fin k) ∉ S := by
        intro hmem
        apply hj
        rw [Finset.mem_map]
        exact ⟨⟨(j : ℕ), hjlt⟩, hmem, Fin.ext rfl⟩
      exact (mem_coordSupport_refl_iff E S v).mp hv ⟨(j : ℕ), hjlt⟩ hjS
    · rw [dif_neg hjlt]
  · intro ha
    change (a : (F × F) × (Fin n → K)) ∈
      coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K)))
        (S.map (Fin.castLEEmb h)) at ha
    refine ⟨castRestr h a, ?_, ?_⟩
    · change castRestr h (a : (F × F) × (Fin n → K)) ∈
        coordSupport (LinearEquiv.refl F ((F × F) × (Fin k → K))) S
      rw [mem_coordSupport_refl_iff E S
        (castRestr h (a : (F × F) × (Fin n → K)))]
      intro i hi
      have hi' : (Fin.castLE h i : Fin n) ∉ S.map (Fin.castLEEmb h) := by
        intro hmem
        obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hmem
        have hji' : j = i := Fin.castLE_injective h (by
          rwa [Fin.castLEEmb_apply] at hji)
        exact hi (hji'.symm ▸ hj)
      exact (mem_coordSupport_refl_iff E _ a).mp ha (Fin.castLE h i) hi'
    · apply Subtype.ext
      change castTo E h (castRestr h (a : (F × F) × (Fin n → K))) =
        (a : (F × F) × (Fin n → K))
      exact castTo_castRestr E h a.2

private theorem map_supportedDerived_castEquivCoord {k n : ℕ} (h : k ≤ n)
    (S : Finset (Fin k)) :
    (supportedDerived (normHypForm E k)
        (coordSupport (LinearEquiv.refl F ((F × F) × (Fin k → K))) S)).map
      (LinearEquiv.autCongr (castEquivCoord E h)).toMonoidHom =
      supportedDerived ((normHypForm E n).comp (castSupport E h).subtype)
        ((coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K)))
          (S.map (Fin.castLEEmb h))).comap (castSupport E h).subtype) := by
  refine map_supportedDerived_autCongr_of_map_eq (σ := RingEquiv.refl F)
    (castEquivCoord E h) 1 one_ne_zero ?_ (map_castEquivCoord_coordSupport E h S)
  intro v
  change normHypForm E n ↑(castEquivCoord E h v) = 1 * RingEquiv.refl F (normHypForm E k v)
  rw [RingEquiv.refl_apply, one_mul, castEquivCoord_apply,
    normHypForm_eq_castRestr_add E h (castTo E h v), castRestr_castTo]
  have htail : (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k),
      normQuad E ((castTo E h v).2 j)) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [castTo_apply]
    simp [(Finset.mem_filter.mp hj).2]
  rw [htail, add_zero]

private theorem coordSupport_map_castLEEmb_le {k n : ℕ} (h : k ≤ n)
    (S : Finset (Fin k)) :
    coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K)))
        (S.map (Fin.castLEEmb h)) ≤ castSupport E h := by
  simp only [castSupport, coordSupport]
  exact sup_le_sup_left (Finset.sup_mono
    (Finset.map_subset_map.mpr (Finset.subset_univ S))) _

private theorem map_supportedDerived_comap_castSupport {k n : ℕ} (h : k ≤ n)
    (S : Finset (Fin k)) :
    (supportedDerived ((normHypForm E n).comp (castSupport E h).subtype)
        ((coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K)))
          (S.map (Fin.castLEEmb h))).comap (castSupport E h).subtype)).map
        (orthExtend (isCompl_castSupport E h)) =
      supportedDerived (normHypForm E n)
        (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K)))
          (S.map (Fin.castLEEmb h))) := by
  exact map_supportedDerived_comap_subtype_eq_supportedDerived
    (Q := normHypForm E n) (B := castSupport E h)
    (coordSupport_map_castLEEmb_le E h S)
    (coordSupport_normHypForm_nondegenerate E (S.map (Fin.castLEEmb h)))
    (coordSupport_normHypForm_nondegenerate E (Finset.univ.map (Fin.castLEEmb h)))

private theorem castHom_eq_orthExtend_castEquivCoord {k n : ℕ} (h : k ≤ n) :
    castHom h =
      (orthExtend (isCompl_castSupport E h)).comp
        (LinearEquiv.autCongr (castEquivCoord E h)).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply LinearEquiv.ext
  intro v
  change (castEquiv h g) v =
    (orthExtend (isCompl_castSupport E h)
      ((LinearEquiv.autCongr (castEquivCoord E h)).toMonoidHom g)) v
  obtain ⟨a, ha, b, hb, hab⟩ :=
    suppExists_add_of_isCompl (isCompl_castSupport E h) v
  rw [← hab, map_add]
  rw [show a + b = ((⟨a, ha⟩ : castSupport E h) : (F × F) × (Fin n → K)) +
      ((⟨b, hb⟩ : suppPerp (normHypForm E n) (castSupport E h)) :
        (F × F) × (Fin n → K)) from rfl]
  rw [orthExtend_apply]
  change (castEquiv h g) a + (castEquiv h g) b =
    ((LinearEquiv.autCongr (castEquivCoord E h) g) ⟨a, ha⟩ :
      (F × F) × (Fin n → K)) +
      ((⟨b, hb⟩ : suppPerp (normHypForm E n) (castSupport E h)) :
        (F × F) × (Fin n → K))
  rw [castEquiv_apply_of_mem_castSupport E h g ha,
    castEquiv_apply_of_mem_suppPerp E h g hb]
  congr 1
  rw [LinearEquiv.autCongr_apply_apply, castEquivCoord_symm_apply, castEquivCoord_apply]

private theorem map_supportedDerived_castHom {k n : ℕ} (h : k ≤ n)
    (S : Finset (Fin k)) :
    (supportedDerived (normHypForm E k)
        (coordSupport (LinearEquiv.refl F ((F × F) × (Fin k → K))) S)).map (castHom h) =
      supportedDerived (normHypForm E n)
        (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K)))
          (S.map (Fin.castLEEmb h))) := by
  rw [castHom_eq_orthExtend_castEquivCoord E h, ← Subgroup.map_map,
    map_supportedDerived_castEquivCoord E h S,
    map_supportedDerived_comap_castSupport E h S]

theorem range_normOmegaCast {k n : ℕ} (h : k ≤ n) :
    (normOmegaCast E h).range = normBlock E n (Finset.univ.map (Fin.castLEEmb h)) := by
  apply le_antisymm
  · rintro x ⟨g, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr
      (normOmegaCast_mem_supportedDerived E h g)
  · intro x hx
    exact mem_range_normOmegaCast_of_mem_supportedDerived E h x
      (Subgroup.mem_subgroupOf.mp hx)

theorem map_normBlock_normOmegaCast {k n : ℕ} (h : k ≤ n) (S : Finset (Fin k)) :
    (normBlock E k S).map (normOmegaCast E h) =
      normBlock E n (S.map (Fin.castLEEmb h)) := by
  have hblock := map_supportedDerived_castHom E h S
  change ((supportedDerived (normHypForm E k)
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin k → K))) S)).subgroupOf
        (normOmega E k)).map (normOmegaCast E h) =
    (supportedDerived (normHypForm E n)
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K)))
        (S.map (Fin.castLEEmb h)))).subgroupOf (normOmega E n)
  apply Subgroup.map_injective (f := (normOmega E n).subtype) (normOmega E n).subtype_injective
  rw [Subgroup.map_map]
  have hcomp : (normOmega E n).subtype.comp (normOmegaCast E h) =
      (castHom h).comp (normOmega E k).subtype := by
    apply MonoidHom.ext
    intro x
    apply LinearEquiv.ext
    intro v
    rfl
  rw [hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (supportedDerived_le_orthDerived_of_regular
      (coordSupport_normHypForm_nondegenerate E S))]
  rw [Subgroup.map_subgroupOf_eq_of_le (supportedDerived_le_orthDerived_of_regular
    (coordSupport_normHypForm_nondegenerate E (S.map (Fin.castLEEmb h))))]
  exact hblock

theorem range_normOmegaCast_succ (m : ℕ) :
    (normOmegaCast E (Nat.le_succ m)).range =
      normBlock E (m + 1) (Finset.univ.erase (Fin.last m)) := by
  have hS : Finset.univ.map (Fin.castLEEmb (Nat.le_succ m)) =
      Finset.univ.erase (Fin.last m) := by
    ext j
    rw [Finset.mem_map, Finset.mem_erase]
    constructor
    · rintro ⟨i, -, rfl⟩
      have hlt : Fin.castLE (Nat.le_succ m) i < Fin.last m := by
        rw [show Fin.castLE (Nat.le_succ m) i = Fin.castSucc i from Fin.ext rfl]
        exact Fin.castSucc_lt_last i
      exact ⟨Fin.ne_of_lt hlt, Finset.mem_univ _⟩
    · rintro ⟨hj, -⟩
      obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hj
      refine ⟨i, Finset.mem_univ _, ?_⟩
      rw [Fin.castLEEmb_apply,
        show Fin.castLE (Nat.le_succ m) i = Fin.castSucc i from Fin.ext rfl, hi]
  rw [range_normOmegaCast E (Nat.le_succ m), hS]

theorem anchorBlock_eq_normBlock {m : ℕ} (h : 2 ≤ m) :
    anchorBlock E h = normBlock E m {⟨0, by omega⟩, ⟨1, by omega⟩} := by
  have hS : Finset.univ.map (Fin.castLEEmb h) =
      ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin m)) := by
    ext j
    rw [Finset.mem_map, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, -, rfl⟩
      fin_cases i
      · left
        rw [Fin.castLEEmb_apply]
        exact Fin.ext rfl
      · right
        rw [Fin.castLEEmb_apply]
        exact Fin.ext rfl
    · rintro (h0 | h1)
      · refine ⟨0, Finset.mem_univ _, ?_⟩
        rw [Fin.castLEEmb_apply, h0]
        exact Fin.ext rfl
      · refine ⟨1, Finset.mem_univ _, ?_⟩
        rw [Fin.castLEEmb_apply, h1]
        exact Fin.ext rfl
  rw [show anchorBlock E h = (normOmegaCast E h).range from rfl,
    range_normOmegaCast E h, hS]

theorem nonempty_normOmega_mulEquiv_normBlock
    (E : QuadExt F K (unitaryInvolution K 2 f)) {r : ℕ} (hr : 3 ≤ r) (S : Finset (Fin r)) :
    Nonempty (normOmega E S.card ≃* ↥(normBlock E r S)) := by
  classical
  have hcard : S.card ≤ r := by simpa using Finset.card_le_univ S
  let A : Finset (Fin r) := Finset.univ.map (Fin.castLEEmb hcard)
  have hAcard : A.card = S.card := by simp [A]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq A S hAcard
  let rho : normOmega E S.card →* normOmega E r :=
    (MulAut.conj (normPerm E hr σ)).toMonoidHom.comp (normOmegaCast E hcard)
  have hrho_inj : Function.Injective rho := by
    dsimp only [rho]
    exact (MulAut.conj (normPerm E hr σ)).injective.comp (normOmegaCast_injective E hcard)
  have hσ' : A.image σ = S := by
    simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using hσ
  have hrange : rho.range = normBlock E r S := by
    dsimp only [rho]
    rw [MonoidHom.range_comp, range_normOmegaCast E hcard,
      map_normBlock_normPerm E hr σ A, hσ']
  exact ⟨(MonoidHom.ofInjective hrho_inj).trans (MulEquiv.subgroupCongr hrange)⟩

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
