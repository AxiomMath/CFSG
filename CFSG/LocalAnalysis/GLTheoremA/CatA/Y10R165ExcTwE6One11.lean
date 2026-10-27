module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerAdj
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwisted
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.PartTwo.Census.Exceptional
  CFSG.RankThree.CentralCover CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.SeitzReduction
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One
open CFSG.SeitzReduction.F4Pilot

theorem e6Isogeny_simpleSL2_three_mem_subsystemGroup {K : Type} [Field K] [Finite K]
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (e6Isogeny K (simpleSL2 e6Data_valid K (3 : Fin Tag.E6.rank) A)).val ∈
      subsystemGroup Tag.E6 K E6GraphLevi.setA := by
  have h3A : (3 : Fin Tag.E6.rank) ∈ E6GraphLevi.setA := by
    change (3 : Fin 6) ≠ (1 : Fin 6)
    decide
  have hroot : IsRoot .E6 (Pi.single (3 : Fin Tag.E6.rank) 1) := isRoot_single .E6 _
  have hroot' : IsRoot .E6 (-Pi.single (3 : Fin Tag.E6.rank) 1) :=
    CFSG.LieType.Chevalley.IsRoot.neg hroot
  have hmem : e6Isogeny K (simpleSL2 e6Data_valid K (3 : Fin Tag.E6.rank) A) ∈
      rootGroup (rootOperatorFamily .E6) K (Pi.single (3 : Fin Tag.E6.rank) 1) ⊔
        rootGroup (rootOperatorFamily .E6) K (-Pi.single (3 : Fin Tag.E6.rank) 1) := by
    have h := Subgroup.mem_map_of_mem (e6Isogeny K)
      (simpleSL2_mem e6Data_valid K (3 : Fin Tag.E6.rank) A)
    rw [Subgroup.map_sup,
      CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup (k := K) hroot,
      CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup (k := K) hroot'] at h
    exact h
  have hle : (rootGroup (rootOperatorFamily .E6) K (Pi.single (3 : Fin Tag.E6.rank) 1) ⊔
      rootGroup (rootOperatorFamily .E6) K (-Pi.single (3 : Fin Tag.E6.rank) 1)).map
        (adjointGroup Tag.E6 K).subtype ≤ subsystemGroup Tag.E6 K E6GraphLevi.setA := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [← CFSG.ClassicalInvolution.RouteD.Exotic.subgroupOf_rootSubgroup_eq_rootGroup
          (rootOperatorFamily .E6) hroot,
        Subgroup.map_subgroupOf_eq_of_le
          (rootSubgroup_le_adjointGroup (Pi.single (3 : Fin Tag.E6.rank) 1))]
      exact rootSubgroup_le_subsystemGroup (single_mem_parabolicRoots h3A)
    · rw [← CFSG.ClassicalInvolution.RouteD.Exotic.subgroupOf_rootSubgroup_eq_rootGroup
          (rootOperatorFamily .E6) hroot',
        Subgroup.map_subgroupOf_eq_of_le
          (rootSubgroup_le_adjointGroup (-Pi.single (3 : Fin Tag.E6.rank) 1))]
      exact rootSubgroup_le_subsystemGroup
        (neg_mem_parabolicRoots (single_mem_parabolicRoots h3A))
  exact hle (Subgroup.mem_map_of_mem _ hmem)

private theorem e6Isogeny_e6NWord_mem {K : Type} [Field K] [Finite K]
    (ω : List (Fin Tag.E6.rank)) (hω : ∀ i ∈ ω, i ∈ E6GraphLevi.setA) :
    ((e6Isogeny K (e6NWord K ω) : adjointGroup Tag.E6 K) :
      ModGL Tag.E6 K) ∈ subsystemGroup Tag.E6 K E6GraphLevi.setA := by
  induction ω with
  | nil => simp [e6NWord]
  | cons i ω ih =>
    rw [e6NWord_cons, map_mul, Subgroup.coe_mul]
    rw [show ((e6Isogeny K (e6Data_valid.nm K i) : adjointGroup Tag.E6 K) :
        ModGL Tag.E6 K) = weylElt Tag.E6 K i 1 from e6Isogeny_nt_eq i 1]
    exact mul_mem (weylElt_mem_subsystemGroup (hω i List.mem_cons_self) 1)
      (ih fun j hj => hω j (List.mem_cons_of_mem i hj))

private theorem e6Isogeny_te6N_mem {K F : Type} [Field K] [Field F] [Finite K]
    (θ : K →+* K) (j : F →+* K) (hj : ∀ x, θ (j x) = j x) (i : Fin 4)
    (hset : ∀ m ∈ te6Words i, m ∈ E6GraphLevi.setA) :
    ((e6Isogeny K ((te6N θ i : fixedGroup K θ) : e6Data_valid.minGroup K) :
        adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈
      subsystemGroup Tag.E6 K E6GraphLevi.setA := by
  have hval : ((te6N θ i : fixedGroup K θ) : e6Data_valid.minGroup K) =
      e6NWord K (te6Words i) := by
    simpa [e6NWord] using te6N_val θ i
  rw [hval]
  exact e6Isogeny_e6NWord_mem (te6Words i) hset

private theorem e6Isogeny_te6SL2_mem_subsystemGroup {K F : Type} [Field K] [Field F]
    [Finite K] (θ : K →+* K) (j : F →+* K) (hj : ∀ x, θ (j x) = j x)
    (i : Fin 4) (hset : ∀ m ∈ te6Words i, m ∈ E6GraphLevi.setA)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((e6Isogeny K ((te6SL2 θ j hj i g : fixedGroup K θ) : e6Data_valid.minGroup K) :
        adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈
      subsystemGroup Tag.E6 K E6GraphLevi.setA := by
  have hte6 : ((te6SL2 θ j hj i g : fixedGroup K θ) : e6Data_valid.minGroup K) =
      (te6N θ i : e6Data_valid.minGroup K) *
        ((fixSL2 θ j hj rhoPerm_three g : fixedGroup K θ) : e6Data_valid.minGroup K) *
        (te6N θ i : e6Data_valid.minGroup K)⁻¹ := rfl
  rw [hte6]
  rw [map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hN := e6Isogeny_te6N_mem (θ := θ) (j := j) hj i hset
  have h3 : (((e6Isogeny K ((fixSL2 θ j hj rhoPerm_three g : fixedGroup K θ) :
      e6Data_valid.minGroup K)) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈
      subsystemGroup Tag.E6 K E6GraphLevi.setA := by
    rw [show ((fixSL2 θ j hj rhoPerm_three g : fixedGroup K θ) :
        e6Data_valid.minGroup K) = simpleSL2 e6Data_valid K (3 : Fin Tag.E6.rank)
          (Matrix.SpecialLinearGroup.map j g) from
      fixSL2_val (θ := θ) (j := j) (hj := hj) (a := (3 : Fin Tag.E6.rank))
        rhoPerm_three g]
    exact e6Isogeny_simpleSL2_three_mem_subsystemGroup
      (Matrix.SpecialLinearGroup.map j g)
  exact mul_mem (mul_mem hN h3) (inv_mem hN)

private theorem twistedIsogenyC_te6SL2_mem_su6Levi {f : ℕ} {k : Type} [Field k] [Finite k]
    [Algebra k (GaloisField 2 (2 * f))] (hf : 1 ≤ f)
    (hj : ∀ x, frobQ 2 f (algebraMap k (GaloisField 2 (2 * f)) x) =
      algebraMap k (GaloisField 2 (2 * f)) x)
    (i : Fin 4) (hset : ∀ m ∈ te6Words i, m ∈ E6GraphLevi.setA)
    (g : Matrix.SpecialLinearGroup (Fin 2) k) :
    (twistedIsogenyC hf
        (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
        (frobQ 2 f) (fun c => frobQ_apply 2 f c)
        (te6SL2 (frobQ 2 f) (algebraMap k (GaloisField 2 (2 * f))) hj i g) : C0 f) ∈
      ((TwistedE6Pilot.su6Levi (frobQ 2 f)).subgroupOf (C0 f)) := by
  rw [Subgroup.mem_subgroupOf, TwistedE6Pilot.su6Levi, Subgroup.mem_inf]
  constructor
  · rw [CFSG.SeitzReduction.F4Pilot.coe_twistedIsogenyC]
    exact e6Isogeny_te6SL2_mem_subsystemGroup (θ := frobQ 2 f)
      (j := algebraMap k (GaloisField 2 (2 * f))) hj i hset g
  · exact Subtype.coe_prop _

theorem map_te6WA_le_su6Levi {f : ℕ} {k : Type} [Field k] [Finite k]
    [Algebra k (GaloisField 2 (2 * f))] (hf : 1 ≤ f)
    (hj : ∀ x, frobQ 2 f (algebraMap k (GaloisField 2 (2 * f)) x) =
      algebraMap k (GaloisField 2 (2 * f)) x)
    (g : Matrix.SpecialLinearGroup (Fin 2) k) :
    (te6WA (frobQ 2 f) (algebraMap k (GaloisField 2 (2 * f))) hj g).map
      (twistedIsogenyC hf
        (CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf)
        (frobQ 2 f) (fun c => frobQ_apply 2 f c)) ≤
      (TwistedE6Pilot.su6Levi (frobQ 2 f)).subgroupOf (C0 f) := by
  have hset0 : ∀ m ∈ te6Words 0, m ∈ E6GraphLevi.setA := by
    change ∀ m : Fin 6, m ∈ ([] : List (Fin 6)) → m ≠ (1 : Fin 6)
    decide
  have hset1 : ∀ m ∈ te6Words 1, m ∈ E6GraphLevi.setA := by
    change ∀ m : Fin 6, m ∈ ([nd 2, nd 4] : List (Fin 6)) → m ≠ (1 : Fin 6)
    decide
  have hset2 : ∀ m ∈ te6Words 2, m ∈ E6GraphLevi.setA := by
    change ∀ m : Fin 6, m ∈ ([nd 0, nd 5, nd 2, nd 4] : List (Fin 6)) → m ≠ (1 : Fin 6)
    decide
  rw [te6WA, Subgroup.map_sup, Subgroup.map_sup]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr
      (twistedIsogenyC_te6SL2_mem_su6Levi hf hj 0 hset0 g)
  · rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr
      (twistedIsogenyC_te6SL2_mem_su6Levi hf hj 1 hset1 g)
  · rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr
      (twistedIsogenyC_te6SL2_mem_su6Levi hf hj 2 hset2 g)

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
