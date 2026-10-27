module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerLine
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryBasic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotToral
public import CFSG.LieType.Chevalley.E6GraphRootSL2Basic
public import CFSG.RankThree.PartOne.S11c.G2Torus
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofSL2
public import CFSG.LieType.Chevalley.CorootCoordinates
public import CFSG.HardMathSupport.Timmesfeld.Torality.A2Block
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLang
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Sporadic.Schreier.TitsIso

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ClassicalInvolution.ModelFacts.Levi

@[expose] def e6BlockPlaneChar {K : Type} [Field K] (a b : Kˣ) :
    Fin Tag.E6.rank → Kˣ :=
  ![1, a, 1, b, 1, 1]

@[expose] def e6BlockPlaneBeta : Fin Tag.E6.rank → ℤ :=
  Pi.single 1 1

@[expose] def e6BlockPlaneTheta : Fin Tag.E6.rank → ℤ :=
  highRoot .E6

@[expose] def e6BlockPlaneGamma : Fin Tag.E6.rank → ℤ :=
  e6BlockPlaneTheta - e6BlockPlaneBeta

@[expose] def e6BlockPlaneW : WeylGroup .E6 :=
  rootReflection e6BlockPlaneTheta * rootReflection e6BlockPlaneBeta

theorem e6BlockPlaneBeta_mem : e6BlockPlaneBeta ∈ e6LineRoots 2 := by
  change (Pi.single (1 : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ) ∈ e6LineRoots 2
  decide +kernel

theorem e6BlockPlaneTheta_mem : e6BlockPlaneTheta ∈ e6LineRoots 2 := by
  change (highRoot .E6) ∈ e6LineRoots 2
  decide +kernel

theorem e6BlockPlaneGamma_mem : e6BlockPlaneGamma ∈ e6LineRoots 2 := by
  change e6BlockPlaneTheta - e6BlockPlaneBeta ∈ e6LineRoots 2
  decide +kernel

theorem e6BlockPlaneChar_one {K : Type} [Field K] (a : Kˣ) :
    e6BlockPlaneChar a 1 = highDiag .E6 a := by
  funext i
  fin_cases i <;> rfl

theorem rootChar_e6BlockPlaneChar {K : Type} [Field K] (a b : Kˣ)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar (e6BlockPlaneChar a b) v = a ^ v 1 * b ^ v 3 := by
  change (∏ i : Fin 6, e6BlockPlaneChar a b i ^ v i) = a ^ v 1 * b ^ v 3
  rw [Fin.prod_univ_six]
  simp [e6BlockPlaneChar]
  rfl

section Reflection

variable {K : Type} [Field K]

theorem corootPair_e6BlockPlaneBeta (v : Fin Tag.E6.rank → ℤ) :
    corootPair e6BlockPlaneBeta v = 2 * v 1 - v 3 := by
  have hβ : e6BlockPlaneBeta =
      (1 : WeylGroup .E6) • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) := by
    simp [e6BlockPlaneBeta]
  rw [hβ, corootPair_smul_single]
  simp only [inv_one, one_smul]
  change (∑ k : Fin 6, Tag.cartan .E6 1 k * v k) = 2 * v 1 - v 3
  rw [Fin.sum_univ_six]
  change 0 * v 0 + 2 * v 1 + 0 * v 2 + (-1) * v 3 + 0 * v 4 + 0 * v 5 =
    2 * v 1 - v 3
  ring

theorem corootPair_e6BlockPlaneTheta (v : Fin Tag.E6.rank → ℤ) :
    corootPair e6BlockPlaneTheta v = v 1 := by
  change corootPair (highRoot .E6) v = v 1
  rw [corootPair_highRoot (Or.inl rfl)]
  rfl

theorem weylAct_rootReflection_beta (a b : Kˣ) :
    weylAct (rootReflection e6BlockPlaneBeta) (e6BlockPlaneChar a b) =
      e6BlockPlaneChar a⁻¹ (a * b) := by
  funext i
  fin_cases i <;>
    simp only [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct,
      rootReflection_inv (β := e6BlockPlaneBeta) (isRoot_single .E6 1),
      rootReflection_smul (β := e6BlockPlaneBeta) (isRoot_single .E6 1),
      corootPair_e6BlockPlaneBeta, rootChar_e6BlockPlaneChar]
  · change a ^ (0 : ℤ) * b ^ (0 : ℤ) = (1 : Kˣ)
    simp
  · change a ^ (-1 : ℤ) * b ^ (0 : ℤ) = a⁻¹
    simp
  · change a ^ (0 : ℤ) * b ^ (0 : ℤ) = (1 : Kˣ)
    simp
  · change a ^ (1 : ℤ) * b ^ (1 : ℤ) = a * b
    simp
  · change a ^ (0 : ℤ) * b ^ (0 : ℤ) = (1 : Kˣ)
    simp
  · change a ^ (0 : ℤ) * b ^ (0 : ℤ) = (1 : Kˣ)
    simp

theorem weylAct_rootReflection_theta (x y : Kˣ) :
    weylAct (rootReflection e6BlockPlaneTheta) (e6BlockPlaneChar x y) =
      e6BlockPlaneChar (x⁻¹ * y ^ (-3 : ℤ)) y := by
  funext i
  fin_cases i <;>
    simp only [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct,
      rootReflection_inv (β := e6BlockPlaneTheta) (isRoot_highRoot .E6),
      rootReflection_smul (β := e6BlockPlaneTheta) (isRoot_highRoot .E6),
      corootPair_e6BlockPlaneTheta, rootChar_e6BlockPlaneChar]
  · change x ^ (0 : ℤ) * y ^ (0 : ℤ) = (1 : Kˣ)
    simp
  · change x ^ (-1 : ℤ) * y ^ (-3 : ℤ) = x⁻¹ * y ^ (-3 : ℤ)
    simp
  · change x ^ (0 : ℤ) * y ^ (0 : ℤ) = (1 : Kˣ)
    simp
  · change x ^ (0 : ℤ) * y ^ (1 : ℤ) = y
    simp
  · change x ^ (0 : ℤ) * y ^ (0 : ℤ) = (1 : Kˣ)
    simp
  · change x ^ (0 : ℤ) * y ^ (0 : ℤ) = (1 : Kˣ)
    simp

theorem weylAct_e6BlockPlaneW (a b : Kˣ) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) :
    weylAct e6BlockPlaneW (e6BlockPlaneChar a b) =
      e6BlockPlaneChar a (a * b) := by
  unfold e6BlockPlaneW
  rw [weylAct_mul, weylAct_rootReflection_beta, weylAct_rootReflection_theta]
  have h : (a * b) ^ (-3 : ℤ) = 1 := by
    have hab : (a * b) ^ 3 = 1 := by
      rw [mul_pow, ha3, hb3, one_mul]
    rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
      hab, inv_one]
  rw [inv_inv, h, mul_one]

theorem weylAct_e6BlockPlaneW_sq (a b : Kˣ) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) :
    weylAct (e6BlockPlaneW * e6BlockPlaneW) (e6BlockPlaneChar a b) =
      e6BlockPlaneChar a (a ^ 2 * b) := by
  rw [weylAct_mul, weylAct_e6BlockPlaneW a b ha3 hb3]
  rw [weylAct_e6BlockPlaneW a (a * b) ha3]
  · congr 1
    rw [pow_two]
    group
  · rw [mul_pow, ha3, hb3, one_mul]

end Reflection

section RootSL2

@[expose] def e6BlockPlaneN (K : Type) [Field K] : ModGL .E6 K :=
  rootSL2 .E6 K e6BlockPlaneTheta WSL * rootSL2 .E6 K e6BlockPlaneBeta WSL

variable {K : Type} [Field K]

theorem e6BlockPlaneN_mem : e6BlockPlaneN K ∈ e6LineFactor K 2 := by
  unfold e6BlockPlaneN
  refine mul_mem ?_ ?_
  · refine rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (isRoot_highRoot .E6) WSL)
    intro α hα
    rcases hα with rfl | hα
    · exact e6BlockPlaneTheta_mem
    · rw [Set.mem_singleton_iff.1 hα]
      exact neg_mem_e6LineRoots e6BlockPlaneTheta_mem
  · refine rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (isRoot_single .E6 1) WSL)
    intro α hα
    rcases hα with rfl | hα
    · exact e6BlockPlaneBeta_mem
    · rw [Set.mem_singleton_iff.1 hα]
      exact neg_mem_e6LineRoots e6BlockPlaneBeta_mem

theorem e6BlockPlaneN_mem_monomial :
    e6BlockPlaneN K ∈ monomialSubgroup .E6 K := by
  unfold e6BlockPlaneN
  exact mul_mem (rootSL2_WSL_mem_monomialSubgroup (isRoot_highRoot .E6))
    (rootSL2_WSL_mem_monomialSubgroup (isRoot_single .E6 1))

theorem e6BlockPlaneN_conj_rootDiagUnit (u : Fin Tag.E6.rank → Kˣ) :
    e6BlockPlaneN K * rootDiagUnit .E6 u * (e6BlockPlaneN K)⁻¹ =
      rootDiagUnit .E6 (weylAct e6BlockPlaneW u) := by
  have hmem := e6BlockPlaneN_mem_monomial (K := K)
  have hθmaps := mapsRootLines_rootSL2_WSL (K := K) (isRoot_highRoot .E6)
  have hβmaps := mapsRootLines_rootSL2_WSL (K := K) (isRoot_single .E6 1)
  have hmaps : MapsRootLines (e6BlockPlaneN K) e6BlockPlaneW := by
    unfold e6BlockPlaneN e6BlockPlaneW
    exact hθmaps.mul hβmaps
  have hweyl : weylQuotientHom .E6 K ⟨e6BlockPlaneN K, hmem⟩ = e6BlockPlaneW :=
    weylQuotientHom_eq hmaps
  have h := monomial_conj_rootDiagUnit (K := K) ⟨e6BlockPlaneN K, hmem⟩ u
  change (e6BlockPlaneN K) * rootDiagUnit .E6 u * (e6BlockPlaneN K)⁻¹ =
    rootDiagUnit .E6 (weylAct (weylQuotientHom .E6 K ⟨e6BlockPlaneN K, hmem⟩) u) at h
  rwa [hweyl] at h

end RootSL2

section AntiIdWord

open CFSG.LieType.Chevalley.E6GraphLevi

variable {Ω : Type} [Field Ω] [CharP Ω 2]

@[expose] def e6AntiIdSL : Matrix.SpecialLinearGroup (Fin 6) Ω :=
  ⟨E6GraphLevi.antiId Ω, by
    have h2 : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2
    exact eq_one_of_mul_self_eq_one_of_two_eq_zero h2
      (E6GraphLevi.det_antiId_sq (E := Ω))⟩

@[expose] def e6AdjSwap (i : Fin 5) : Matrix.SpecialLinearGroup (Fin 6) Ω :=
  let h : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  Matrix.SpecialLinearGroup.transvection h 1 * Matrix.SpecialLinearGroup.transvection h.symm 1 *
    Matrix.SpecialLinearGroup.transvection h 1

@[expose] def e6AntiIdWord : Matrix.SpecialLinearGroup (Fin 6) Ω :=
  (([0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0] : List (Fin 5)).map e6AdjSwap).prod

theorem e6AntiIdWord_zmod2 :
    e6AntiIdSL (Ω := ZMod 2) = e6AntiIdWord (Ω := ZMod 2) := by
  decide +kernel

theorem e6AntiIdSL_eq_word : e6AntiIdSL (Ω := Ω) = e6AntiIdWord (Ω := Ω) := by
  let f : ZMod 2 →+* Ω := ZMod.castHom (dvd_refl 2) Ω
  have hleft : Matrix.SpecialLinearGroup.map f (e6AntiIdSL (Ω := ZMod 2)) =
      e6AntiIdSL (Ω := Ω) := by
    apply Subtype.ext
    ext i j
    change f ((E6GraphLevi.antiId (ZMod 2)) i j) = (E6GraphLevi.antiId Ω) i j
    by_cases h : j = i.rev
    · simp [E6GraphLevi.antiId, h]
    · simp [E6GraphLevi.antiId, h]
  have htrans_one (a b : Fin 6) (h : a ≠ b) :
      Matrix.SpecialLinearGroup.map f
        (Matrix.SpecialLinearGroup.transvection h (1 : ZMod 2)) =
      Matrix.SpecialLinearGroup.transvection h (1 : Ω) := by
    simpa using Matrix.SpecialLinearGroup.map_transvection f h (1 : ZMod 2)
  have htrans : ∀ i : Fin 5,
      Matrix.SpecialLinearGroup.map f (e6AdjSwap (Ω := ZMod 2) i) =
        e6AdjSwap (Ω := Ω) i := by
    intro i
    let h : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
    change Matrix.SpecialLinearGroup.map f
      (Matrix.SpecialLinearGroup.transvection h 1 *
        Matrix.SpecialLinearGroup.transvection h.symm 1 *
        Matrix.SpecialLinearGroup.transvection h 1) =
      Matrix.SpecialLinearGroup.transvection h 1 *
        Matrix.SpecialLinearGroup.transvection h.symm 1 *
        Matrix.SpecialLinearGroup.transvection h 1
    simp [map_mul, htrans_one]
  have hright : Matrix.SpecialLinearGroup.map f (e6AntiIdWord (Ω := ZMod 2)) =
      e6AntiIdWord (Ω := Ω) := by
    simp [e6AntiIdWord, List.map_map, Function.comp_def, map_list_prod, htrans]
  have hmap := congrArg (Matrix.SpecialLinearGroup.map f) e6AntiIdWord_zmod2
  rw [hleft, hright] at hmap
  exact hmap

@[expose] def e6AntiIdPathWord : List (Fin TwistTag.E6.tag.rank) :=
  [0, 2, 3, 4, 5, 0, 2, 3, 4, 0, 2, 3, 0, 2, 0]

theorem e6AdjSwap_realize (h2 : (2 : Ω) = 0) (i : Fin 5) :
    E6GraphLevi.realize h2 (e6AdjSwap (Ω := Ω) i) =
      weylElt TwistTag.E6.tag Ω (E6GraphLevi.pathIdx i) 1 := by
  simp [e6AdjSwap, map_mul, E6GraphLevi.realize_x, E6GraphLevi.realize_y,
    LieType.Chevalley.weylElt_eq_xUnit_mul, neg_eq_self_of_two h2]

theorem e6AntiIdWord_realize (h2 : (2 : Ω) = 0) :
    E6GraphLevi.realize h2 (e6AntiIdWord (Ω := Ω)) =
      E6GraphHighestRoot.wordElt Ω e6AntiIdPathWord := by
  have hpath : (([0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0] : List (Fin 5)).map
      E6GraphLevi.pathIdx) = e6AntiIdPathWord := by
    decide
  rw [e6AntiIdWord, map_list_prod]
  simp only [List.map_map, Function.comp_def, e6AdjSwap_realize h2]
  rw [← hpath]
  rfl

theorem e6AntiIdSL_realize (h2 : (2 : Ω) = 0) :
    E6GraphLevi.realize h2 (e6AntiIdSL (Ω := Ω)) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) Ω
        ((coxeterSystem TwistTag.E6.tag).wordProd e6AntiIdPathWord) := by
  rw [e6AntiIdSL_eq_word, e6AntiIdWord_realize h2, E6GraphHighestRoot.wordElt_eq_canonicalRep h2]

end AntiIdWord

section PinnedBeta

variable
  {K : Type} [Field K] [CharP K 2]

open CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphRadical

theorem e6AntiIdSL_diagramMap_pinnedX_general (α : Fin Tag.E6.rank → ℤ)
    (hα : IsRoot TwistTag.E6.tag α) (c : K) :
    E6GraphLevi.realize (CharP.cast_eq_zero K 2) (e6AntiIdSL (Ω := K)) *
        diagramMap TwistTag.E6 K * pinnedX TwistTag.E6.tag K α c *
        (E6GraphLevi.realize (CharP.cast_eq_zero K 2) (e6AntiIdSL (Ω := K)) *
          diagramMap TwistTag.E6 K)⁻¹ =
      pinnedX TwistTag.E6.tag K
        ((coxeterSystem TwistTag.E6.tag).wordProd e6AntiIdPathWord •
          permLattice TwistTag.E6.perm α) c := by
  let w : WeylGroup TwistTag.E6.tag :=
    (coxeterSystem TwistTag.E6.tag).wordProd e6AntiIdPathWord
  have hpermα : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm α) :=
    (isRoot_permLattice_iff (π := TwistTag.E6.perm)
      (TwistTag.cartan_perm .E6)).2 hα
  have hδ := diagramMap_conj_pinnedX_of_two (E := K)
    (h2 := CharP.cast_eq_zero K 2) hα c
  have hw := canonicalRep_mul_pinnedX_mul_inv_of_two
    (h2 := CharP.cast_eq_zero K 2) w hpermα c
  have hj : E6GraphLevi.realize (CharP.cast_eq_zero K 2) (e6AntiIdSL (Ω := K)) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w :=
    e6AntiIdSL_realize (h2 := CharP.cast_eq_zero K 2)
  calc
    E6GraphLevi.realize (CharP.cast_eq_zero K 2) (e6AntiIdSL (Ω := K)) *
        diagramMap TwistTag.E6 K * pinnedX TwistTag.E6.tag K α c *
        (E6GraphLevi.realize (CharP.cast_eq_zero K 2) (e6AntiIdSL (Ω := K)) *
          diagramMap TwistTag.E6 K)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        diagramMap TwistTag.E6 K * pinnedX TwistTag.E6.tag K α c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
          diagramMap TwistTag.E6 K)⁻¹ := by rw [hj]
    _ = canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        (diagramMap TwistTag.E6 K * pinnedX TwistTag.E6.tag K α c *
          (diagramMap TwistTag.E6 K)⁻¹) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by group
    _ = canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm α) c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by rw [hδ]
    _ = pinnedX TwistTag.E6.tag K (w • permLattice TwistTag.E6.perm α) c := hw

theorem e6AntiIdSL_diagramMap_pinnedBeta (c : K) :
    E6GraphLevi.realize (CharP.cast_eq_zero K 2) (e6AntiIdSL (Ω := K)) *
        diagramMap TwistTag.E6 K * pinnedX TwistTag.E6.tag K e6BlockPlaneBeta c *
        (E6GraphLevi.realize (CharP.cast_eq_zero K 2) (e6AntiIdSL (Ω := K)) *
          diagramMap TwistTag.E6 K)⁻¹ =
      pinnedX TwistTag.E6.tag K e6BlockPlaneGamma c := by
  have hβ : IsRoot TwistTag.E6.tag e6BlockPlaneBeta := by
    exact isRoot_single Tag.E6 1
  have hroot : (coxeterSystem TwistTag.E6.tag).wordProd e6AntiIdPathWord •
      permLattice TwistTag.E6.perm e6BlockPlaneBeta = e6BlockPlaneGamma := by
    rw [wordProd_smul]
    funext i
    fin_cases i <;> decide +kernel
  have h := e6AntiIdSL_diagramMap_pinnedX_general e6BlockPlaneBeta hβ c
  rwa [hroot] at h

theorem e6AntiIdSL_diagramMap_pinnedNegBeta (c : K) :
    E6GraphLevi.realize (CharP.cast_eq_zero K 2) (e6AntiIdSL (Ω := K)) *
        diagramMap TwistTag.E6 K * pinnedX TwistTag.E6.tag K (-e6BlockPlaneBeta) c *
        (E6GraphLevi.realize (CharP.cast_eq_zero K 2) (e6AntiIdSL (Ω := K)) *
          diagramMap TwistTag.E6 K)⁻¹ =
      pinnedX TwistTag.E6.tag K (-e6BlockPlaneGamma) c := by
  have hβ : IsRoot TwistTag.E6.tag e6BlockPlaneBeta := by
    exact isRoot_single Tag.E6 1
  have hβneg : IsRoot TwistTag.E6.tag (-e6BlockPlaneBeta) := IsRoot.neg hβ
  have hrootneg : (coxeterSystem TwistTag.E6.tag).wordProd e6AntiIdPathWord •
      permLattice TwistTag.E6.perm (-e6BlockPlaneBeta) = -e6BlockPlaneGamma := by
    rw [wordProd_smul]
    funext i
    fin_cases i <;> decide +kernel
  have h := e6AntiIdSL_diagramMap_pinnedX_general (-e6BlockPlaneBeta) hβneg c
  rwa [hrootneg] at h

end PinnedBeta

section Frobenius

variable
  {Ω : Type} [Field Ω] [CharP Ω 2]

open CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphRadical
open CFSG.LieType.Chevalley.E6GraphRootSL2 CFSG.LieType.Chevalley.E6GraphHighestRoot
open CFSG.Blueprint.Chevalley

@[expose] def e6AntiIdJ : ModGL Tag.E6 Ω :=
  E6GraphLevi.realize (CharP.cast_eq_zero Ω 2) (e6AntiIdSL (Ω := Ω))

@[expose] def e6ThetaN : ModGL Tag.E6 Ω :=
  rootSL2 Tag.E6 Ω e6HighestRoot WSL

@[expose] def e6FrobEnd (σQ : Ω →+* Ω) (η : Ωˣ) :
    ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
  (MulAut.conj ((thetaTorusHom Ω η : ModGL Tag.E6 Ω) * e6ThetaN * e6AntiIdJ)).toMonoidHom.comp
    (twistHom TwistTag.E6 Ω σQ)

@[expose] def e6ThetaAct (α : Fin Tag.E6.rank → ℤ) :
    Fin Tag.E6.rank → ℤ :=
  thetaWord.foldr (reflect Tag.E6)
    (reflect Tag.E6 (e6Idx 0)
      (thetaWord.reverse.foldr (reflect Tag.E6) α))

@[expose] def e6BetaN : ModGL Tag.E6 Ω :=
  rootSL2 Tag.E6 Ω e6BlockPlaneBeta WSL

@[expose] def e6BetaTorus (r : Ωˣ) : ModGL Tag.E6 Ω :=
  rootSL2 Tag.E6 Ω e6BlockPlaneBeta (HSL r)

@[expose] def e6ThetaTorus (r : Ωˣ) : ModGL Tag.E6 Ω :=
  thetaTorusHom Ω r

theorem e6ThetaTorus_mul (a b : Ωˣ) :
    e6ThetaTorus (a * b) = e6ThetaTorus a * e6ThetaTorus b := by
  unfold e6ThetaTorus
  exact map_mul (thetaTorusHom Ω) a b

theorem e6ThetaTorus_zpow (r : Ωˣ) (n : ℤ) :
    e6ThetaTorus (r ^ n) = (e6ThetaTorus r) ^ n := by
  change (thetaTorusHom Ω (r ^ n) : ModGL Tag.E6 Ω) =
    ((thetaTorusHom Ω r : ModGL Tag.E6 Ω) ^ n)
  exact map_zpow (thetaTorusHom Ω) r n

@[expose] def e6BetaCorootTuple : Fin Tag.E6.rank → ℤ :=
  fun i => corootPair e6BlockPlaneBeta (Pi.single i 1)

@[expose] def e6BetaTorusChar (r : Ωˣ) : Fin Tag.E6.rank → Ωˣ :=
  fun i => r ^ e6BetaCorootTuple i

@[expose] def e6ThetaTorusChar (r : Ωˣ) : Fin Tag.E6.rank → Ωˣ :=
  Pi.mulSingle (1 : Fin Tag.E6.rank) r

theorem e6FrobEnd_apply (σQ : Ω →+* Ω) (η : Ωˣ)
    (g : ModGL Tag.E6 Ω) :
    e6FrobEnd σQ η g =
      (((thetaTorusHom Ω η : ModGL Tag.E6 Ω) : ModGL Tag.E6 Ω) * e6ThetaN * e6AntiIdJ) *
        twistHom TwistTag.E6 Ω σQ g *
        (((thetaTorusHom Ω η : ModGL Tag.E6 Ω) : ModGL Tag.E6 Ω) * e6ThetaN * e6AntiIdJ)⁻¹ := rfl

private theorem e6Vuv (h2 : (2 : Ω) = 0) (a : Ωˣ) :
    vSL ((a⁻¹ : Ωˣ) : Ω) * uSL (a : Ω) * vSL ((a⁻¹ : Ωˣ) : Ω) = nSL a := by
  have h12 : (1 : Ω) + 1 = 0 := by
    rw [show (1 : Ω) + 1 = (2 : Ω) by norm_num, h2]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [nSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val,
      neg_eq_self_of_two h2, h12]

theorem e6ThetaAct_gamma : e6ThetaAct e6BlockPlaneGamma = -e6BlockPlaneBeta := by
  unfold e6ThetaAct
  funext i
  fin_cases i <;> decide +kernel

theorem e6ThetaAct_negGamma : e6ThetaAct (-e6BlockPlaneGamma) = e6BlockPlaneBeta := by
  unfold e6ThetaAct
  funext i
  fin_cases i <;> decide +kernel

theorem e6AntiIdJ_mem_subsystem :
    e6AntiIdJ ∈ subsystemGroup TwistTag.E6.tag Ω setA := by
  rw [← range_realize (E := Ω) (CharP.cast_eq_zero Ω 2)]
  exact ⟨e6AntiIdSL, rfl⟩

theorem e6AntiIdJ_mul_thetaSL2 (B : SL2 Ω) :
    e6AntiIdJ * thetaSL2 Ω B = thetaSL2 Ω B * e6AntiIdJ := by
  have hcent := subsystemGroup_le_centralizer_thetaSL2 (E := Ω)
    (CharP.cast_eq_zero Ω 2) e6AntiIdJ_mem_subsystem
  exact ((Subgroup.mem_centralizer_iff.1 hcent) (thetaSL2 Ω B) ⟨B, rfl⟩).symm

theorem e6ThetaTorus_eq_rootDiagUnit (r : Ωˣ) :
    ((thetaTorusHom Ω r : ModGL Tag.E6 Ω) : ModGL Tag.E6 Ω) =
      rootDiagUnit Tag.E6 (e6ThetaTorusChar r) := by
  unfold e6ThetaTorusChar thetaTorusHom
  rfl

theorem e6BetaTorus_eq_rootDiagUnit (r : Ωˣ) :
    (e6BetaTorus r : ModGL Tag.E6 Ω) =
      rootDiagUnit Tag.E6 (e6BetaTorusChar r) := by
  unfold e6BetaTorus e6BetaTorusChar e6BetaCorootTuple
  exact CFSG.RankThree.PartOne.rootSL2_HSL_eq_rootDiagUnit
    (isRoot_single Tag.E6 1)
    (fun i => corootPair e6BlockPlaneBeta (Pi.single i 1))
    (fun δ hδ => by
      simpa [corootPair, e6BlockPlaneBeta] using
        CFSG.HardMathSupport.Timmesfeld.CrossChar.corootPair_eq_sum
          (isRoot_single Tag.E6 1) δ) r

theorem e6BetaTorus_mul (a b : Ωˣ) :
    e6BetaTorus (a * b) = e6BetaTorus a * e6BetaTorus b := by
  unfold e6BetaTorus
  have hHSL : HSL (a * b) = HSL a * HSL b := by
    simpa only [CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_apply] using
      map_mul (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom Ω) a b
  rw [hHSL, map_mul]

theorem e6ThetaTorus_mem (r : Ωˣ) :
    ((thetaTorusHom Ω r : ModGL Tag.E6 Ω) : ModGL Tag.E6 Ω) ∈ e6LineFactor Ω 2 := by
  rw [thetaTorusHom_apply]
  change rootSL2 Tag.E6 Ω e6HighestRoot (HSL r) ∈ e6LineFactor Ω 2
  refine rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (isRoot_highRoot .E6) (HSL r))
  intro α hα
  rcases hα with rfl | hα
  · exact e6BlockPlaneTheta_mem
  · rw [Set.mem_singleton_iff.1 hα]
    exact neg_mem_e6LineRoots e6BlockPlaneTheta_mem

theorem e6BetaTorus_mem (r : Ωˣ) :
    (e6BetaTorus r : ModGL Tag.E6 Ω) ∈ e6LineFactor Ω 2 := by
  refine rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (isRoot_single Tag.E6 1) (HSL r))
  intro α hα
  rcases hα with rfl | hα
  · exact e6BlockPlaneBeta_mem
  · rw [Set.mem_singleton_iff.1 hα]
    exact neg_mem_e6LineRoots e6BlockPlaneBeta_mem

theorem e6ThetaN_conj_pinnedX {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) (c : Ω) :
    e6ThetaN * pinnedX TwistTag.E6.tag Ω α c * e6ThetaN⁻¹ =
      pinnedX TwistTag.E6.tag Ω (e6ThetaAct α) c := by
  rw [e6ThetaN]
  exact thetaSL2_WSL_conj (E := Ω) (CharP.cast_eq_zero Ω 2) hα c

theorem e6ThetaN_mem_monomial :
    e6ThetaN ∈ monomialSubgroup Tag.E6 Ω := by
  change rootSL2 Tag.E6 Ω (highRoot .E6) WSL ∈ monomialSubgroup Tag.E6 Ω
  exact rootSL2_WSL_mem_monomialSubgroup (isRoot_highRoot .E6)

theorem e6ThetaN_mapsRootLines :
    MapsRootLines (R := Ω) e6ThetaN (rootReflection e6BlockPlaneTheta) := by
  change MapsRootLines (R := Ω) (rootSL2 Tag.E6 Ω (highRoot .E6) WSL)
    (rootReflection (highRoot .E6))
  exact mapsRootLines_rootSL2_WSL (isRoot_highRoot .E6)

theorem e6ThetaN_weylQuotient :
    weylQuotientHom Tag.E6 Ω ⟨e6ThetaN, e6ThetaN_mem_monomial⟩ =
      rootReflection e6BlockPlaneTheta :=
  weylQuotientHom_eq e6ThetaN_mapsRootLines

theorem e6WeylAct_rootReflection_theta_betaChar (r : Ωˣ) :
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct (τ := Tag.E6)
        (rootReflection e6BlockPlaneTheta) (e6BetaTorusChar r) =
      e6BetaTorusChar r * (e6ThetaTorusChar r)⁻¹ := by
  have hβchar : e6BetaTorusChar r = e6BlockPlaneChar (r ^ 2) (r⁻¹) := by
    funext i
    change r ^ corootPair e6BlockPlaneBeta (Pi.single i 1) = _
    rw [corootPair_e6BlockPlaneBeta]
    change Fin 6 at i
    change r ^ (2 * (Pi.single i 1 : Fin 6 → ℤ) 1 - (Pi.single i 1 : Fin 6 → ℤ) 3) =
      (![1, r ^ 2, 1, r⁻¹, 1, 1] : Fin 6 → Ωˣ) i
    fin_cases i <;> norm_num [Pi.single_apply]
  have hθchar : e6ThetaTorusChar r = e6BlockPlaneChar r 1 := by
    change (Pi.mulSingle (1 : Fin 6) r : Fin 6 → Ωˣ) = ![1, r, 1, 1, 1, 1]
    funext i
    fin_cases i <;> simp [Pi.mulSingle_apply]
  have harg : (r ^ 2)⁻¹ * (r⁻¹) ^ (-3 : ℤ) = r := by group
  have hmul : e6BlockPlaneChar (r ^ 2) (r⁻¹) * (e6BlockPlaneChar r 1)⁻¹ =
      e6BlockPlaneChar r (r⁻¹) := by
    change (![1, r ^ 2, 1, r⁻¹, 1, 1] : Fin 6 → Ωˣ) *
      (![1, r, 1, 1, 1, 1] : Fin 6 → Ωˣ)⁻¹ = ![1, r, 1, r⁻¹, 1, 1]
    funext i
    fin_cases i <;> simp [Pi.mul_apply, Pi.inv_apply, pow_two]
  rw [hβchar, hθchar, weylAct_rootReflection_theta, harg, hmul]

theorem e6ThetaN_conj_betaTorus (r : Ωˣ) :
    (e6ThetaN : ModGL Tag.E6 Ω) * (e6BetaTorus r : ModGL Tag.E6 Ω) *
        (e6ThetaN : ModGL Tag.E6 Ω)⁻¹ =
      (((thetaTorusHom Ω r : ModGL Tag.E6 Ω)⁻¹ : ModGL Tag.E6 Ω) : ModGL Tag.E6 Ω) *
        (e6BetaTorus r : ModGL Tag.E6 Ω) := by
  have hconj := monomial_conj_rootDiagUnit (K := Ω)
    ⟨e6ThetaN, e6ThetaN_mem_monomial⟩ (e6BetaTorusChar r)
  change (e6ThetaN : ModGL Tag.E6 Ω) * rootDiagUnit Tag.E6 (e6BetaTorusChar r) *
      (e6ThetaN : ModGL Tag.E6 Ω)⁻¹ =
    rootDiagUnit Tag.E6
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
        (weylQuotientHom Tag.E6 Ω ⟨e6ThetaN, e6ThetaN_mem_monomial⟩)
        (e6BetaTorusChar r)) at hconj
  rw [e6ThetaN_weylQuotient, e6WeylAct_rootReflection_theta_betaChar] at hconj
  rw [e6BetaTorus_eq_rootDiagUnit, e6ThetaTorus_eq_rootDiagUnit]
  calc
    (e6ThetaN : ModGL Tag.E6 Ω) * rootDiagUnit Tag.E6 (e6BetaTorusChar r) *
        (e6ThetaN : ModGL Tag.E6 Ω)⁻¹ =
        rootDiagUnit Tag.E6 (e6BetaTorusChar r * (e6ThetaTorusChar r)⁻¹) := hconj
    _ = rootDiagUnit Tag.E6 ((e6ThetaTorusChar r)⁻¹ * e6BetaTorusChar r) := by
      congr 1
      exact mul_comm _ _
    _ = rootDiagUnit Tag.E6 ((e6ThetaTorusChar r)⁻¹) *
          rootDiagUnit Tag.E6 (e6BetaTorusChar r) := by
      rw [rootDiagUnit_mul]
    _ = (rootDiagUnit Tag.E6 (e6ThetaTorusChar r))⁻¹ *
          rootDiagUnit Tag.E6 (e6BetaTorusChar r) := by
      rw [rootDiagUnit_inv]

theorem e6FrobEnd_rootSL2_highest (σQ : Ω →+* Ω) (η : Ωˣ) (B : SL2 Ω) :
    e6FrobEnd σQ η (rootSL2 Tag.E6 Ω e6BlockPlaneTheta B) =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta
        ((HSL η * WSL : SL2 Ω) * Matrix.SpecialLinearGroup.map σQ B *
          (HSL η * WSL : SL2 Ω)⁻¹) := by
  have h2 : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2
  have happ := e6FrobEnd_apply (Ω := Ω) σQ η
    (rootSL2 Tag.E6 Ω e6BlockPlaneTheta B : ModGL Tag.E6 Ω)
  refine happ.trans ?_
  have hH : (thetaTorusHom Ω η : ModGL Tag.E6 Ω) =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) :=
    thetaTorusHom_eq_thetaSL2 (E := Ω) η
  have hX : twistHom TwistTag.E6 Ω σQ (rootSL2 Tag.E6 Ω e6BlockPlaneTheta B) =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ B) :=
    twistHom_thetaSL2 (E := Ω) h2 σQ B
  have hjX : e6AntiIdJ * rootSL2 Tag.E6 Ω e6BlockPlaneTheta
        (Matrix.SpecialLinearGroup.map σQ B) =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ B) * e6AntiIdJ :=
    e6AntiIdJ_mul_thetaSL2 (Matrix.SpecialLinearGroup.map σQ B)
  rw [hH, hX]
  have hjc : e6AntiIdJ * rootSL2 Tag.E6 Ω e6BlockPlaneTheta
        (Matrix.SpecialLinearGroup.map σQ B) * e6AntiIdJ⁻¹ =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ B) := by
    rw [hjX]
    group
  have hAB : rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
        rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η * WSL) :=
    (map_mul (rootSL2 Tag.E6 Ω e6BlockPlaneTheta) (HSL η) WSL).symm
  calc
    (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL * e6AntiIdJ) *
        rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ B) *
        (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL * e6AntiIdJ)⁻¹
      = rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL *
          (e6AntiIdJ * rootSL2 Tag.E6 Ω e6BlockPlaneTheta
            (Matrix.SpecialLinearGroup.map σQ B) * e6AntiIdJ⁻¹) *
          (rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL)⁻¹ *
          (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η))⁻¹ := by group
    _ = rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ B) *
          (rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL)⁻¹ *
          (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η))⁻¹ := by rw [hjc]
    _ = rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ B) *
          (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
            rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL)⁻¹ := by group
    _ = rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η * WSL) *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ B) *
          (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η * WSL))⁻¹ := by rw [hAB]
    _ = rootSL2 Tag.E6 Ω e6BlockPlaneTheta
          ((HSL η * WSL) * Matrix.SpecialLinearGroup.map σQ B *
            (HSL η * WSL)⁻¹) := by
        conv_rhs => rw [map_mul, map_mul, map_inv]

theorem e6FrobEnd_thetaTorus (σQ : Ω →+* Ω) (η : Ωˣ) (r : Ωˣ) :
    e6FrobEnd σQ η (thetaTorusHom Ω r : ModGL Tag.E6 Ω) =
      (thetaTorusHom Ω ((Units.map σQ.toMonoidHom r)⁻¹) : ModGL Tag.E6 Ω) := by
  have hs : (thetaTorusHom Ω r : ModGL Tag.E6 Ω) =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL r) :=
    thetaTorusHom_eq_thetaSL2 (E := Ω) r
  have hs' : @Eq (ModGL Tag.E6 Ω)
      (thetaTorusHom Ω ((Units.map σQ.toMonoidHom r)⁻¹) : ModGL Tag.E6 Ω)
      (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL ((Units.map σQ.toMonoidHom r)⁻¹))) :=
    thetaTorusHom_eq_thetaSL2 (E := Ω) _
  have hHSL_inv : ∀ t : Ωˣ, (HSL t : SL2 Ω)⁻¹ = HSL t⁻¹ := fun t => by
    simpa only [CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_apply] using
      (map_inv (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom Ω) t).symm
  have hW : (WSL : SL2 Ω) * HSL (Units.map σQ.toMonoidHom r) =
      (HSL (Units.map σQ.toMonoidHom r) : SL2 Ω)⁻¹ * WSL := by
    rw [WSL_mul_HSL, ← hHSL_inv]
  have hcancel : HSL η * (HSL (Units.map σQ.toMonoidHom r) : SL2 Ω)⁻¹ * (HSL η : SL2 Ω)⁻¹ =
      (HSL (Units.map σQ.toMonoidHom r) : SL2 Ω)⁻¹ := by
    simpa only [map_mul, map_inv,
      CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_apply] using
      congrArg (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom Ω)
        (show η * (Units.map σQ.toMonoidHom r)⁻¹ * η⁻¹ =
          (Units.map σQ.toMonoidHom r)⁻¹ by
            rw [mul_right_comm, mul_inv_cancel, one_mul])
  have hSL : (HSL η * WSL : SL2 Ω) * HSL (Units.map σQ.toMonoidHom r) *
        (HSL η * WSL : SL2 Ω)⁻¹ = HSL (Units.map σQ.toMonoidHom r)⁻¹ := by
    calc
      (HSL η * WSL : SL2 Ω) * HSL (Units.map σQ.toMonoidHom r) *
          (HSL η * WSL : SL2 Ω)⁻¹
        = HSL η * (WSL * HSL (Units.map σQ.toMonoidHom r)) * WSL⁻¹ * (HSL η)⁻¹ := by
            group
      _ = HSL η * ((HSL (Units.map σQ.toMonoidHom r) : SL2 Ω)⁻¹ * WSL) * WSL⁻¹ *
            (HSL η)⁻¹ := by rw [hW]
      _ = HSL η * (HSL (Units.map σQ.toMonoidHom r) : SL2 Ω)⁻¹ * (HSL η)⁻¹ := by group
      _ = (HSL (Units.map σQ.toMonoidHom r) : SL2 Ω)⁻¹ := hcancel
      _ = HSL (Units.map σQ.toMonoidHom r)⁻¹ := hHSL_inv _
  have h1 : e6FrobEnd σQ η (thetaTorusHom Ω r : ModGL Tag.E6 Ω) =
      e6FrobEnd σQ η (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL r)) := congrArg _ hs
  have h2 : e6FrobEnd σQ η (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL r)) =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta
        ((HSL η * WSL) * Matrix.SpecialLinearGroup.map σQ (HSL r) *
          (HSL η * WSL)⁻¹) := e6FrobEnd_rootSL2_highest (Ω := Ω) σQ η (HSL r)
  have h3 : rootSL2 Tag.E6 Ω e6BlockPlaneTheta
        ((HSL η * WSL) * Matrix.SpecialLinearGroup.map σQ (HSL r) *
          (HSL η * WSL)⁻¹) =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta
        (HSL ((Units.map σQ.toMonoidHom r)⁻¹)) := by
    rw [map_HSL (E := Ω) σQ r]
    exact congrArg (rootSL2 Tag.E6 Ω e6BlockPlaneTheta) hSL
  have h4 : rootSL2 Tag.E6 Ω e6BlockPlaneTheta
        (HSL ((Units.map σQ.toMonoidHom r)⁻¹)) =
      (thetaTorusHom Ω ((Units.map σQ.toMonoidHom r)⁻¹) : ModGL Tag.E6 Ω) := hs'.symm
  exact h1.trans (h2.trans (h3.trans h4))

theorem e6FrobEnd_thetaN (σQ : Ω →+* Ω) (η : Ωˣ) :
    e6FrobEnd σQ η e6ThetaN =
      (thetaTorusHom Ω (η ^ 2) : ModGL Tag.E6 Ω) * e6ThetaN := by
  have h2 : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2
  have happ := e6FrobEnd_apply (Ω := Ω) σQ η (e6ThetaN : ModGL Tag.E6 Ω)
  refine happ.trans ?_
  have hH : (thetaTorusHom Ω η : ModGL Tag.E6 Ω) =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) :=
    thetaTorusHom_eq_thetaSL2 (E := Ω) η
  have hX : twistHom TwistTag.E6 Ω σQ e6ThetaN =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ WSL) :=
    twistHom_thetaSL2 (E := Ω) h2 σQ WSL
  have hjX : e6AntiIdJ * rootSL2 Tag.E6 Ω e6BlockPlaneTheta
        (Matrix.SpecialLinearGroup.map σQ WSL) =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ WSL) * e6AntiIdJ :=
    e6AntiIdJ_mul_thetaSL2 (Matrix.SpecialLinearGroup.map σQ WSL)
  rw [hH, hX]
  rw [show e6ThetaN = rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL from rfl]
  have hs : (thetaTorusHom Ω (η ^ 2) : ModGL Tag.E6 Ω) =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL (η ^ 2)) :=
    thetaTorusHom_eq_thetaSL2 (E := Ω) (η ^ 2)
  rw [hs]
  have hjc : e6AntiIdJ * rootSL2 Tag.E6 Ω e6BlockPlaneTheta
        (Matrix.SpecialLinearGroup.map σQ WSL) * e6AntiIdJ⁻¹ =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ WSL) := by
    rw [hjX]
    group
  have hAB : rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
        rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL =
      rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η * WSL) :=
    (map_mul (rootSL2 Tag.E6 Ω e6BlockPlaneTheta) (HSL η) WSL).symm
  have hHSL_inv : (HSL η : SL2 Ω)⁻¹ = HSL η⁻¹ := by
    simpa only [CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_apply] using
      (map_inv (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom Ω) η).symm
  have hW : (WSL : SL2 Ω) * (HSL η)⁻¹ = HSL η * WSL := by
    rw [hHSL_inv, WSL_mul_HSL η⁻¹, inv_inv]
  have hmul : HSL η * HSL η = HSL (η * η) := by
    simpa only [CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_apply] using
      (map_mul (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom Ω) η η).symm
  have hSL : (HSL η * WSL : SL2 Ω) * WSL * (HSL η * WSL : SL2 Ω)⁻¹ =
      HSL (η ^ 2) * WSL := by
    calc
      (HSL η * WSL : SL2 Ω) * WSL * (HSL η * WSL : SL2 Ω)⁻¹
        = HSL η * WSL * (HSL η)⁻¹ := by group
      _ = HSL η * (WSL * (HSL η)⁻¹) := by group
      _ = HSL η * (HSL η * WSL) := by rw [hW]
      _ = HSL η * HSL η * WSL := by group
      _ = HSL (η * η) * WSL := by rw [hmul]
      _ = HSL (η ^ 2) * WSL := by rw [pow_two]
  calc
    (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL * e6AntiIdJ) *
        rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ WSL) *
        (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL * e6AntiIdJ)⁻¹
      = rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL *
          (e6AntiIdJ * rootSL2 Tag.E6 Ω e6BlockPlaneTheta
            (Matrix.SpecialLinearGroup.map σQ WSL) * e6AntiIdJ⁻¹) *
          (rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL)⁻¹ *
          (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η))⁻¹ := by group
    _ = rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ WSL) *
          (rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL)⁻¹ *
          (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η))⁻¹ := by rw [hjc]
    _ = rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ WSL) *
          (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η) *
            rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL)⁻¹ := by group
    _ = rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η * WSL) *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta (Matrix.SpecialLinearGroup.map σQ WSL) *
          (rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL η * WSL))⁻¹ := by rw [hAB]
    _ = rootSL2 Tag.E6 Ω e6BlockPlaneTheta
          ((HSL η * WSL) * Matrix.SpecialLinearGroup.map σQ WSL * (HSL η * WSL)⁻¹) := by
        conv_rhs => rw [map_mul, map_mul, map_inv]
    _ = rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL (η ^ 2) * WSL) := by
        rw [map_WSL (f := σQ), hSL]
    _ = rootSL2 Tag.E6 Ω e6BlockPlaneTheta (HSL (η ^ 2)) *
          rootSL2 Tag.E6 Ω e6BlockPlaneTheta WSL := by rw [map_mul]

theorem e6ThetaTorusChar_eq_blockPlaneChar (r : Ωˣ) :
    e6ThetaTorusChar r = e6BlockPlaneChar r 1 := by
  change (Pi.mulSingle (1 : Fin 6) r : Fin 6 → Ωˣ) = ![1, r, 1, 1, 1, 1]
  funext i
  fin_cases i <;> simp [Pi.mulSingle_apply]

theorem rootChar_e6ThetaTorusChar_beta (r : Ωˣ) :
    rootChar (e6ThetaTorusChar r) e6BlockPlaneBeta = r := by
  rw [e6ThetaTorusChar_eq_blockPlaneChar, rootChar_e6BlockPlaneChar]
  simp [e6BlockPlaneBeta]

theorem rootChar_e6ThetaTorusChar_negBeta (r : Ωˣ) :
    rootChar (e6ThetaTorusChar r) (-e6BlockPlaneBeta) = r⁻¹ := by
  rw [e6ThetaTorusChar_eq_blockPlaneChar, rootChar_e6BlockPlaneChar]
  simp [e6BlockPlaneBeta]

theorem e6FrobEnd_pinnedBeta (σQ : Ω →+* Ω) (η : Ωˣ) (c : Ω) :
    e6FrobEnd σQ η (pinnedX Tag.E6 Ω e6BlockPlaneBeta c) =
      pinnedX Tag.E6 Ω (-e6BlockPlaneBeta)
        (((η⁻¹ : Ωˣ) : Ω) * σQ c) := by
  let H : ModGL Tag.E6 Ω := thetaTorusHom Ω η
  let n : ModGL Tag.E6 Ω := e6ThetaN
  let j : ModGL Tag.E6 Ω := e6AntiIdJ
  let δ : ModGL Tag.E6 Ω := diagramMap TwistTag.E6 Ω
  let X : ModGL Tag.E6 Ω := pinnedX Tag.E6 Ω e6BlockPlaneBeta c
  let Xσ : ModGL Tag.E6 Ω := pinnedX Tag.E6 Ω e6BlockPlaneBeta (σQ c)
  let Y : ModGL Tag.E6 Ω := pinnedX Tag.E6 Ω (-e6BlockPlaneBeta) (σQ c)
  let Z : ModGL Tag.E6 Ω := pinnedX Tag.E6 Ω e6BlockPlaneGamma (σQ c)
  let Yout : ModGL Tag.E6 Ω :=
    pinnedX Tag.E6 Ω (-e6BlockPlaneBeta) (((η⁻¹ : Ωˣ) : Ω) * σQ c)
  let σGL : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
    baseChangeGL (τ := Tag.E6) σQ
  let τGL : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
    ((MulAut.conj : ModGL Tag.E6 Ω →* MulAut (ModGL Tag.E6 Ω)) δ).toMonoidHom.comp σGL
  have hβ : IsRoot Tag.E6 e6BlockPlaneBeta := isRoot_single Tag.E6 1
  have hγ : IsRoot Tag.E6 e6BlockPlaneGamma :=
    isRoot_of_mem_e6LineRoots e6BlockPlaneGamma_mem
  have hnegβ : IsRoot Tag.E6 (-e6BlockPlaneBeta) := IsRoot.neg hβ
  have hfield : σGL X = Xσ := by
    simpa only [σGL, X, Xσ] using
      (baseChangeGL_pinnedX (τ := Tag.E6) (f := σQ) e6BlockPlaneBeta c)
  have hX : τGL X = δ * Xσ * δ⁻¹ := by
    change δ * σGL X * δ⁻¹ = δ * Xσ * δ⁻¹
    rw [hfield]
  have hJ : (j * δ) * Xσ * (j * δ)⁻¹ = Z := by
    exact e6AntiIdSL_diagramMap_pinnedBeta (K := Ω) (c := σQ c)
  have hN0 :
      (e6ThetaN : ModGL Tag.E6 Ω) *
          pinnedX Tag.E6 Ω e6BlockPlaneGamma (σQ c) * e6ThetaN⁻¹ =
        pinnedX Tag.E6 Ω (e6ThetaAct e6BlockPlaneGamma) (σQ c) := by
    exact e6ThetaN_conj_pinnedX (Ω := Ω) hγ (σQ c)
  have hN : n * Z * n⁻¹ = Y := by
    simpa only [n, Z, Y, e6ThetaAct_gamma] using hN0
  have hH : H = rootDiagUnit Tag.E6 (e6ThetaTorusChar η) :=
    e6ThetaTorus_eq_rootDiagUnit η
  have hHconj : H * Y * H⁻¹ = Yout := by
    have h := rootDiagUnit_conj_pinnedX (τ := Tag.E6) (K := Ω)
      (e6ThetaTorusChar η) hnegβ (σQ c)
    rw [rootChar_e6ThetaTorusChar_negBeta η] at h
    rw [hH]
    simpa only [Y, Yout] using h
  have happ : e6FrobEnd σQ η X =
      (H * n * j) * τGL X * (H * n * j)⁻¹ := by rfl
  change e6FrobEnd σQ η X = Yout
  refine happ.trans ?_
  rw [hX]
  calc
    (H * n * j) * (δ * Xσ * δ⁻¹) * (H * n * j)⁻¹
      = H * (n * ((j * δ) * Xσ * (j * δ)⁻¹) * n⁻¹) * H⁻¹ := by group
    _ = H * (n * Z * n⁻¹) * H⁻¹ := by rw [hJ]
    _ = H * Y * H⁻¹ := by rw [hN]
    _ = Yout := hHconj

theorem e6FrobEnd_pinnedNegBeta (σQ : Ω →+* Ω) (η : Ωˣ) (c : Ω) :
    e6FrobEnd σQ η (pinnedX Tag.E6 Ω (-e6BlockPlaneBeta) c) =
      pinnedX Tag.E6 Ω e6BlockPlaneBeta
        (((η : Ωˣ) : Ω) * σQ c) := by
  let H : ModGL Tag.E6 Ω := thetaTorusHom Ω η
  let n : ModGL Tag.E6 Ω := e6ThetaN
  let j : ModGL Tag.E6 Ω := e6AntiIdJ
  let δ : ModGL Tag.E6 Ω := diagramMap TwistTag.E6 Ω
  let X : ModGL Tag.E6 Ω := pinnedX Tag.E6 Ω (-e6BlockPlaneBeta) c
  let Xσ : ModGL Tag.E6 Ω := pinnedX Tag.E6 Ω (-e6BlockPlaneBeta) (σQ c)
  let Y : ModGL Tag.E6 Ω := pinnedX Tag.E6 Ω e6BlockPlaneBeta (σQ c)
  let Z : ModGL Tag.E6 Ω := pinnedX Tag.E6 Ω (-e6BlockPlaneGamma) (σQ c)
  let Yout : ModGL Tag.E6 Ω :=
    pinnedX Tag.E6 Ω e6BlockPlaneBeta (((η : Ωˣ) : Ω) * σQ c)
  let σGL : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
    baseChangeGL (τ := Tag.E6) σQ
  let τGL : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
    ((MulAut.conj : ModGL Tag.E6 Ω →* MulAut (ModGL Tag.E6 Ω)) δ).toMonoidHom.comp σGL
  have hβ : IsRoot Tag.E6 e6BlockPlaneBeta := isRoot_single Tag.E6 1
  have hγ : IsRoot Tag.E6 e6BlockPlaneGamma :=
    isRoot_of_mem_e6LineRoots e6BlockPlaneGamma_mem
  have hnegγ : IsRoot Tag.E6 (-e6BlockPlaneGamma) := IsRoot.neg hγ
  have hfield : σGL X = Xσ := by
    simpa only [σGL, X, Xσ] using
      (baseChangeGL_pinnedX (τ := Tag.E6) (f := σQ) (-e6BlockPlaneBeta) c)
  have hX : τGL X = δ * Xσ * δ⁻¹ := by
    change δ * σGL X * δ⁻¹ = δ * Xσ * δ⁻¹
    rw [hfield]
  have hJ : (j * δ) * Xσ * (j * δ)⁻¹ = Z := by
    exact e6AntiIdSL_diagramMap_pinnedNegBeta (K := Ω) (c := σQ c)
  have hN0 :
      (e6ThetaN : ModGL Tag.E6 Ω) *
          pinnedX Tag.E6 Ω (-e6BlockPlaneGamma) (σQ c) * e6ThetaN⁻¹ =
        pinnedX Tag.E6 Ω (e6ThetaAct (-e6BlockPlaneGamma)) (σQ c) := by
    exact e6ThetaN_conj_pinnedX (Ω := Ω) hnegγ (σQ c)
  have hN : n * Z * n⁻¹ = Y := by
    simpa only [n, Z, Y, e6ThetaAct_negGamma] using hN0
  have hH : H = rootDiagUnit Tag.E6 (e6ThetaTorusChar η) :=
    e6ThetaTorus_eq_rootDiagUnit η
  have hHconj : H * Y * H⁻¹ = Yout := by
    have h := rootDiagUnit_conj_pinnedX (τ := Tag.E6) (K := Ω)
      (e6ThetaTorusChar η) hβ (σQ c)
    rw [rootChar_e6ThetaTorusChar_beta η] at h
    rw [hH]
    simpa only [Y, Yout] using h
  have happ : e6FrobEnd σQ η X =
      (H * n * j) * τGL X * (H * n * j)⁻¹ := by rfl
  change e6FrobEnd σQ η X = Yout
  refine happ.trans ?_
  rw [hX]
  calc
    (H * n * j) * (δ * Xσ * δ⁻¹) * (H * n * j)⁻¹
      = H * (n * ((j * δ) * Xσ * (j * δ)⁻¹) * n⁻¹) * H⁻¹ := by group
    _ = H * (n * Z * n⁻¹) * H⁻¹ := by rw [hJ]
    _ = H * Y * H⁻¹ := by rw [hN]
    _ = Yout := hHconj

theorem e6Beta_rootSL2_nSL (t : Ωˣ) :
    rootSL2 Tag.E6 Ω e6BlockPlaneBeta (nSL t) = e6BetaTorus t * e6BetaN := by
  rw [CFSG.LieType.Chevalley.nSL_eq_HSL_mul, map_mul]
  rfl

theorem e6BetaTorus_inv (r : Ωˣ) : (e6BetaTorus r)⁻¹ = e6BetaTorus r⁻¹ := by
  unfold e6BetaTorus
  rw [← map_inv]
  congr 1
  simpa only [CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_apply] using
    (map_inv (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom Ω) r).symm

theorem e6BetaTorus_zpow (r : Ωˣ) (n : ℤ) :
    e6BetaTorus (r ^ n) = (e6BetaTorus r) ^ n := by
  unfold e6BetaTorus
  rw [← map_zpow (rootSL2 Tag.E6 Ω e6BlockPlaneBeta) (HSL r) n]
  congr 1
  simpa only [CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_apply] using
    map_zpow (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom Ω) r n

theorem e6FrobEnd_rootSL2_beta (σQ : Ω →+* Ω) (η : Ωˣ) (r : Ωˣ) :
    e6FrobEnd σQ η (rootSL2 Tag.E6 Ω e6BlockPlaneBeta (nSL r)) =
      rootSL2 Tag.E6 Ω e6BlockPlaneBeta
        (nSL (η * (Units.map σQ.toMonoidHom r)⁻¹)) := by
  let s : Ωˣ := Units.map σQ.toMonoidHom r
  let a : Ωˣ := η * s⁻¹
  have hβ : IsRoot Tag.E6 e6BlockPlaneBeta := isRoot_single Tag.E6 1
  have hword : rootSL2 Tag.E6 Ω e6BlockPlaneBeta (nSL r) =
      pinnedX Tag.E6 Ω e6BlockPlaneBeta (r : Ω) *
        pinnedX Tag.E6 Ω (-e6BlockPlaneBeta) (-((r⁻¹ : Ωˣ) : Ω)) *
        pinnedX Tag.E6 Ω e6BlockPlaneBeta (r : Ω) := by
    rw [CFSG.HardMathSupport.Timmesfeld.Torality.nSL_eq_uSL_vSL_uSL]
    simp only [map_mul, CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hβ,
      CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hβ]
  have hs : (s : Ω) = σQ (r : Ω) := rfl
  have hcoef1 : (((η⁻¹ : Ωˣ) : Ω) * σQ (r : Ω)) = ((a⁻¹ : Ωˣ) : Ω) := by
    rw [← hs, ← Units.val_mul]
    congr 1
    unfold a
    rw [mul_comm]
    group
  have hcoef2 : (((η : Ωˣ) : Ω) * σQ (-((r⁻¹ : Ωˣ) : Ω))) = (a : Ω) := by
    have hmap : σQ (-((r⁻¹ : Ωˣ) : Ω)) = -((s : Ω)⁻¹) := by
      rw [map_neg, Units.val_inv_eq_inv_val, map_inv₀]
      rfl
    rw [hmap, neg_eq_self_of_two (CharP.cast_eq_zero Ω 2)]
    change ((η : Ωˣ) : Ω) * (s : Ω)⁻¹ = ((η * s⁻¹ : Ωˣ) : Ω)
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [hword]
  simp only [map_mul]
  rw [e6FrobEnd_pinnedBeta σQ η (r : Ω),
    e6FrobEnd_pinnedNegBeta σQ η (-((r⁻¹ : Ωˣ) : Ω))]
  rw [hcoef1, hcoef2]
  have hv := congrArg (rootSL2 Tag.E6 Ω e6BlockPlaneBeta)
    (e6Vuv (Ω := Ω) (CharP.cast_eq_zero Ω 2) a)
  simp only [map_mul] at hv
  rw [CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hβ,
    CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hβ] at hv
  exact hv

theorem e6FrobEnd_betaN (σQ : Ω →+* Ω) (η : Ωˣ) :
    e6FrobEnd σQ η e6BetaN = e6BetaTorus η * e6BetaN := by
  have h := e6FrobEnd_rootSL2_beta σQ η 1
  rw [CFSG.LieType.Chevalley.nSL_one] at h
  rw [show rootSL2 Tag.E6 Ω e6BlockPlaneBeta
        (nSL (η * (Units.map σQ.toMonoidHom (1 : Ωˣ))⁻¹)) =
      e6BetaTorus η * e6BetaN by
    rw [e6Beta_rootSL2_nSL]
    rw [show η * (Units.map σQ.toMonoidHom (1 : Ωˣ))⁻¹ = η by
      rw [map_one, inv_one, mul_one]]] at h
  simpa only [e6BetaN] using h

theorem e6FrobEnd_betaTorus (σQ : Ω →+* Ω) (η : Ωˣ) (r : Ωˣ) :
    e6FrobEnd σQ η (e6BetaTorus r) =
      e6BetaTorus ((Units.map σQ.toMonoidHom r)⁻¹) := by
  let s : Ωˣ := Units.map σQ.toMonoidHom r
  let a : Ωˣ := η * s⁻¹
  have hHSL : (HSL r : SL2 Ω) = nSL r * (WSL : SL2 Ω)⁻¹ := by
    rw [CFSG.LieType.Chevalley.nSL_eq_HSL_mul]
    group
  have hdecomp : e6BetaTorus r =
      rootSL2 Tag.E6 Ω e6BlockPlaneBeta (nSL r) * (e6BetaN)⁻¹ := by
    unfold e6BetaTorus e6BetaN
    rw [hHSL, map_mul, map_inv]
  calc
    e6FrobEnd σQ η (e6BetaTorus r)
      = e6FrobEnd σQ η
          (rootSL2 Tag.E6 Ω e6BlockPlaneBeta (nSL r) * (e6BetaN)⁻¹) := by
        rw [hdecomp]
    _ = e6FrobEnd σQ η (rootSL2 Tag.E6 Ω e6BlockPlaneBeta (nSL r)) *
          (e6FrobEnd σQ η e6BetaN)⁻¹ := by rw [map_mul, map_inv]
    _ = rootSL2 Tag.E6 Ω e6BlockPlaneBeta (nSL a) *
          (e6BetaTorus η * e6BetaN)⁻¹ := by
        rw [e6FrobEnd_rootSL2_beta, e6FrobEnd_betaN]
    _ = (e6BetaTorus a * e6BetaN) * (e6BetaTorus η * e6BetaN)⁻¹ := by
        rw [e6Beta_rootSL2_nSL]
    _ = e6BetaTorus a * (e6BetaTorus η)⁻¹ := by group
    _ = e6BetaTorus (a * η⁻¹) := by rw [e6BetaTorus_inv, ← e6BetaTorus_mul]
    _ = e6BetaTorus (s⁻¹) := by
        congr 1
        unfold a
        rw [mul_comm (η : Ωˣ) s⁻¹]
        group

theorem e6BlockPlaneN_eq_thetaN_mul_betaN :
    e6BlockPlaneN Ω = e6ThetaN * e6BetaN := by
  unfold e6BlockPlaneN e6ThetaN e6BetaN e6BlockPlaneTheta
  rfl

theorem e6BlockPlaneN_frob (σQ : Ω →+* Ω) (η : Ωˣ) :
    e6FrobEnd σQ η (e6BlockPlaneN Ω) =
      e6ThetaTorus η * e6BetaTorus η * e6BlockPlaneN Ω := by
  have hconj : e6ThetaN * e6BetaTorus η =
      (e6ThetaTorus η)⁻¹ * e6BetaTorus η * e6ThetaN := by
    rw [show e6ThetaTorus η = (thetaTorusHom Ω η : ModGL Tag.E6 Ω) from rfl]
    have h := e6ThetaN_conj_betaTorus (r := η)
    rw [← h]
    group
  have hsq : e6ThetaTorus (η ^ 2) =
      e6ThetaTorus η * e6ThetaTorus η := by
    rw [pow_two, e6ThetaTorus_mul]
  have hmul :
      (e6ThetaTorus (η ^ 2) * e6ThetaN) *
          (e6BetaTorus η * e6BetaN) =
        e6ThetaTorus η * e6BetaTorus η *
          (e6ThetaN * e6BetaN) := by
    rw [hsq]
    calc
      ((e6ThetaTorus η *
            e6ThetaTorus η) * e6ThetaN) *
          (e6BetaTorus η * e6BetaN)
        = (e6ThetaTorus η *
              e6ThetaTorus η) *
            (e6ThetaN * e6BetaTorus η) * e6BetaN := by group
      _ = (e6ThetaTorus η *
              e6ThetaTorus η) *
            ((e6ThetaTorus η)⁻¹ *
              e6BetaTorus η * e6ThetaN) * e6BetaN := by rw [hconj]
      _ = e6ThetaTorus η * e6BetaTorus η *
            (e6ThetaN * e6BetaN) := by group
  calc
    e6FrobEnd σQ η (e6BlockPlaneN Ω)
      = e6FrobEnd σQ η (e6ThetaN * e6BetaN) := by
        rw [e6BlockPlaneN_eq_thetaN_mul_betaN]
    _ = e6FrobEnd σQ η e6ThetaN * e6FrobEnd σQ η e6BetaN := by rw [map_mul]
    _ = (e6ThetaTorus (η ^ 2) * e6ThetaN) *
          (e6BetaTorus η * e6BetaN) := by
        rw [e6FrobEnd_thetaN, e6FrobEnd_betaN]
        rfl
    _ = e6ThetaTorus η * e6BetaTorus η *
          (e6ThetaN * e6BetaN) := hmul
    _ = e6ThetaTorus η * e6BetaTorus η * e6BlockPlaneN Ω := by
        rw [← e6BlockPlaneN_eq_thetaN_mul_betaN]

theorem e6ThetaBetaTorus_eq_rootDiagUnit (r : Ωˣ) :
    e6ThetaTorus r * e6BetaTorus r =
      rootDiagUnit Tag.E6 (e6ThetaTorusChar r * e6BetaTorusChar r) := by
  have hθ : e6ThetaTorus r = rootDiagUnit Tag.E6 (e6ThetaTorusChar r) := by
    change (thetaTorusHom Ω r : ModGL Tag.E6 Ω) =
      rootDiagUnit Tag.E6 (e6ThetaTorusChar r)
    exact e6ThetaTorus_eq_rootDiagUnit r
  rw [hθ, e6BetaTorus_eq_rootDiagUnit, rootDiagUnit_mul]

theorem e6ThetaBetaTorus_commute (r : Ωˣ) :
    Commute (e6ThetaTorus r) (e6BetaTorus r) := by
  have hθ : e6ThetaTorus r = rootDiagUnit Tag.E6 (e6ThetaTorusChar r) := by
    change (thetaTorusHom Ω r : ModGL Tag.E6 Ω) =
      rootDiagUnit Tag.E6 (e6ThetaTorusChar r)
    exact e6ThetaTorus_eq_rootDiagUnit r
  rw [hθ, e6BetaTorus_eq_rootDiagUnit]
  show rootDiagUnit Tag.E6 (e6ThetaTorusChar r) *
      rootDiagUnit Tag.E6 (e6BetaTorusChar r) =
    rootDiagUnit Tag.E6 (e6BetaTorusChar r) *
      rootDiagUnit Tag.E6 (e6ThetaTorusChar r)
  have h := rootDiagUnit_conj_rootDiagUnit
    (e6ThetaTorusChar r) (e6BetaTorusChar r)
  calc
    rootDiagUnit Tag.E6 (e6ThetaTorusChar r) *
        rootDiagUnit Tag.E6 (e6BetaTorusChar r) =
        (rootDiagUnit Tag.E6 (e6ThetaTorusChar r) *
          rootDiagUnit Tag.E6 (e6BetaTorusChar r) *
          (rootDiagUnit Tag.E6 (e6ThetaTorusChar r))⁻¹) *
          rootDiagUnit Tag.E6 (e6ThetaTorusChar r) := by group
    _ = rootDiagUnit Tag.E6 (e6BetaTorusChar r) *
          rootDiagUnit Tag.E6 (e6ThetaTorusChar r) := by rw [h]

@[expose] def e6BlockPlaneActor (r : Ωˣ) : ModGL Tag.E6 Ω :=
  e6ThetaTorus r * e6BetaTorus r * e6BlockPlaneN Ω

theorem e6BlockPlaneActor_mem (r : Ωˣ) :
    e6BlockPlaneActor r ∈ e6LineFactor Ω 2 := by
  refine mul_mem (mul_mem ?_ ?_) (e6BlockPlaneN_mem (K := Ω))
  · change (thetaTorusHom Ω r : ModGL Tag.E6 Ω) ∈ e6LineFactor Ω 2
    exact e6ThetaTorus_mem r
  · exact e6BetaTorus_mem r

theorem e6BlockPlaneActor_conj_rootDiagUnit (r : Ωˣ)
    (u : Fin Tag.E6.rank → Ωˣ) :
    e6BlockPlaneActor r * rootDiagUnit Tag.E6 u * (e6BlockPlaneActor r)⁻¹ =
      rootDiagUnit Tag.E6 (weylAct e6BlockPlaneW u) := by
  calc
    e6BlockPlaneActor r * rootDiagUnit Tag.E6 u * (e6BlockPlaneActor r)⁻¹
      = (e6ThetaTorus r * e6BetaTorus r) *
          (e6BlockPlaneN Ω * rootDiagUnit Tag.E6 u * (e6BlockPlaneN Ω)⁻¹) *
          (e6ThetaTorus r * e6BetaTorus r)⁻¹ := by
        unfold e6BlockPlaneActor
        group
    _ = (e6ThetaTorus r * e6BetaTorus r) *
          rootDiagUnit Tag.E6 (weylAct e6BlockPlaneW u) *
          (e6ThetaTorus r * e6BetaTorus r)⁻¹ := by
        rw [e6BlockPlaneN_conj_rootDiagUnit (K := Ω)]
    _ = rootDiagUnit Tag.E6 (weylAct e6BlockPlaneW u) := by
        rw [e6ThetaBetaTorus_eq_rootDiagUnit]
        exact rootDiagUnit_conj_rootDiagUnit _ _

theorem e6BlockPlaneActor_sq_conj (r : Ωˣ) (u : Fin Tag.E6.rank → Ωˣ) :
    (e6BlockPlaneActor r) ^ 2 * rootDiagUnit Tag.E6 u *
        ((e6BlockPlaneActor r) ^ 2)⁻¹ =
      rootDiagUnit Tag.E6 (weylAct (e6BlockPlaneW * e6BlockPlaneW) u) := by
  calc
    (e6BlockPlaneActor r) ^ 2 * rootDiagUnit Tag.E6 u *
        ((e6BlockPlaneActor r) ^ 2)⁻¹ =
        e6BlockPlaneActor r *
          (e6BlockPlaneActor r * rootDiagUnit Tag.E6 u *
            (e6BlockPlaneActor r)⁻¹) *
          (e6BlockPlaneActor r)⁻¹ := by
        rw [pow_two]
        group
    _ = e6BlockPlaneActor r *
          rootDiagUnit Tag.E6 (weylAct e6BlockPlaneW u) *
          (e6BlockPlaneActor r)⁻¹ := by
        rw [e6BlockPlaneActor_conj_rootDiagUnit]
    _ = rootDiagUnit Tag.E6
          (weylAct e6BlockPlaneW (weylAct e6BlockPlaneW u)) :=
      e6BlockPlaneActor_conj_rootDiagUnit r _
    _ = rootDiagUnit Tag.E6 (weylAct (e6BlockPlaneW * e6BlockPlaneW) u) := by
        rw [weylAct_mul]

theorem e6BlockPlaneActor_fixed (σQ : Ω →+* Ω) (q : ℕ)
    (hσ : ∀ c : Ω, σQ c = c ^ q) (η r : Ωˣ) (hr : r ^ (q + 1) = η) :
    e6FrobEnd σQ η (e6BlockPlaneActor r) = e6BlockPlaneActor r := by
  have hσu : Units.map σQ.toMonoidHom r = r ^ q := by
    ext
    simp only [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hσ (r : Ω)
  have hFθ : e6FrobEnd σQ η (e6ThetaTorus r) =
      e6ThetaTorus ((Units.map σQ.toMonoidHom r)⁻¹) := by
    change e6FrobEnd σQ η (thetaTorusHom Ω r) =
      (thetaTorusHom Ω ((Units.map σQ.toMonoidHom r)⁻¹) : ModGL Tag.E6 Ω)
    exact e6FrobEnd_thetaTorus σQ η r
  have hFβ : e6FrobEnd σQ η (e6BetaTorus r) =
      e6BetaTorus ((Units.map σQ.toMonoidHom r)⁻¹) :=
    e6FrobEnd_betaTorus σQ η r
  have hFt : e6FrobEnd σQ η (e6ThetaTorus r * e6BetaTorus r) =
      (e6ThetaTorus r * e6BetaTorus r) ^ (-(q : ℤ)) := by
    rw [map_mul, hFθ, hFβ, hσu]
    rw [show (r ^ q)⁻¹ = r ^ (-(q : ℤ)) by rw [zpow_neg, zpow_natCast]]
    rw [e6ThetaTorus_zpow, e6BetaTorus_zpow]
    rw [← (e6ThetaBetaTorus_commute r).mul_zpow]
  have hFN : e6FrobEnd σQ η (e6BlockPlaneN Ω) =
      (e6ThetaTorus r * e6BetaTorus r) ^ (((q + 1 : ℕ) : ℤ)) *
        e6BlockPlaneN Ω := by
    rw [e6BlockPlaneN_frob, ← hr]
    rw [show r ^ (q + 1) = r ^ (((q + 1 : ℕ) : ℤ)) by rw [zpow_natCast]]
    rw [e6ThetaTorus_zpow, e6BetaTorus_zpow]
    rw [← (e6ThetaBetaTorus_commute r).mul_zpow]
  calc
    e6FrobEnd σQ η (e6BlockPlaneActor r)
      = e6FrobEnd σQ η (e6ThetaTorus r * e6BetaTorus r) *
          e6FrobEnd σQ η (e6BlockPlaneN Ω) := by
        unfold e6BlockPlaneActor
        rw [map_mul]
    _ = (e6ThetaTorus r * e6BetaTorus r) ^ (-(q : ℤ)) *
          ((e6ThetaTorus r * e6BetaTorus r) ^ (((q + 1 : ℕ) : ℤ)) *
            e6BlockPlaneN Ω) := by
        rw [hFt, hFN]
    _ = (e6ThetaTorus r * e6BetaTorus r) * e6BlockPlaneN Ω := by
        have hq1 : (((q + 1 : ℕ) : ℤ)) = (q : ℤ) + 1 := by
          push_cast
          ring
        rw [hq1]
        group
    _ = e6BlockPlaneActor r := rfl

theorem exists_e6LineFactor_conj_blockPlane_fixed [IsAlgClosed Ω]
    (q : ℕ) (σQ : Ω →+* Ω) (hσ : ∀ c : Ω, σQ c = c ^ q)
    (η a b : Ωˣ) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1) :
    ∃ n ∈ e6LineFactor Ω 2,
      e6FrobEnd σQ η n = n ∧
      n * rootDiagUnit Tag.E6 (e6BlockPlaneChar a b) * n⁻¹ =
        rootDiagUnit Tag.E6 (highDiag .E6 a) ∧
      (∀ x ∈ e6LineFactor Ω 0, n * x = x * n) ∧
      (∀ x ∈ e6LineFactor Ω 1, n * x = x * n) := by
  obtain ⟨r, hr⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.Levi.exists_unit_pow_eq η
      (n := q + 1) (Nat.succ_pos q)
  obtain ⟨j, hj, hb⟩ := e6Line_exists_pow_eq_of_pow_three_eq_one ha3 ha1 hb3
  interval_cases j
  · have hb' : b = 1 := by simpa using hb
    refine ⟨1, one_mem _, ?_, ?_, ?_, ?_⟩
    · simp
    · rw [one_mul, inv_one, mul_one, hb', e6BlockPlaneChar_one]
    · intro x hx
      rw [one_mul, mul_one]
    · intro x hx
      rw [one_mul, mul_one]
  · have hb' : b = a := by simpa using hb
    refine ⟨(e6BlockPlaneActor r) ^ 2, pow_mem (e6BlockPlaneActor_mem r) 2,
      ?_, ?_, ?_, ?_⟩
    · rw [map_pow, e6BlockPlaneActor_fixed σQ q hσ η r hr]
    · rw [hb', e6BlockPlaneActor_sq_conj,
        weylAct_e6BlockPlaneW_sq a a ha3 ha3,
        show a ^ 2 * a = 1 by rw [← pow_succ, show 2 + 1 = 3 by omega, ha3],
        e6BlockPlaneChar_one]
    · intro x hx
      exact e6LineFactor_commute (i := 2) (j := 0) (by decide)
        (pow_mem (e6BlockPlaneActor_mem r) 2) hx
    · intro x hx
      exact e6LineFactor_commute (i := 2) (j := 1) (by decide)
        (pow_mem (e6BlockPlaneActor_mem r) 2) hx
  · have hb' : b = a ^ 2 := by simpa using hb
    have ha2 : (a ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, ha3, one_pow]
    refine ⟨e6BlockPlaneActor r, e6BlockPlaneActor_mem r, ?_, ?_, ?_, ?_⟩
    · exact e6BlockPlaneActor_fixed σQ q hσ η r hr
    · rw [hb', e6BlockPlaneActor_conj_rootDiagUnit,
        weylAct_e6BlockPlaneW a (a ^ 2) ha3 ha2,
        show a * a ^ 2 = 1 by rw [← pow_succ', show 2 + 1 = 3 by omega, ha3],
        e6BlockPlaneChar_one]
    · intro x hx
      exact e6LineFactor_commute (i := 2) (j := 0) (by decide)
        (e6BlockPlaneActor_mem r) hx
    · intro x hx
      exact e6LineFactor_commute (i := 2) (j := 1) (by decide)
        (e6BlockPlaneActor_mem r) hx

end Frobenius

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
