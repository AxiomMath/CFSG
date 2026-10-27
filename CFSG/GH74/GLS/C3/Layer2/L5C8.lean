module

public import CFSG.GH74.GLS.C3.Layer2.L5C0
public import CFSG.GH74.GLS.C3.Layer2.L5B7
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public import Certificates.Certificate5045
public import Certificates.Certificate5051
public import Certificates.Certificate5070
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.Foundations
public import CFSG.GH74.GLS.C3.Layer2.L5B3
public import CFSG.GH74.GLS.C3.Layer2.L5B4
public import CFSG.GH74.GLS.C3.Layer2.L5B5
public import CFSG.GH74.GLS.C3.Layer2.L5Pat
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.C3.Layers
public import CFSG.GH74.GLS.C3.Prop121.Defs
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.After
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_7
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements129b
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

section Lift

variable {h : IsAConfig 5 x K T Q S a} (c : Coord5 h)

noncomputable def Coord5.liftEl
    (i : Fin 16) : G :=
  (Coord5.exists_lift_rco c Rm_le_Fgrp (el16_mem i)).choose

theorem Coord5.liftEl_mem
    (i : Fin 16) : c.liftEl i ∈ c.lift Rm :=
  (Coord5.exists_lift_rco c Rm_le_Fgrp (el16_mem i)).choose_spec.1

theorem Coord5.rco_liftEl
    (i : Fin 16) : c.rco (c.liftEl i) = el16 i :=
  (Coord5.exists_lift_rco c Rm_le_Fgrp (el16_mem i)).choose_spec.2

theorem Coord5.liftEl_mem_C
    (i : Fin 16) : c.liftEl i ∈ centralizer ({x} : Set G) :=
  Coord5.lift_mem_cent (c.liftEl_mem i)

theorem Coord5.liftEl_mem_T
    (i : Fin 16) : c.liftEl i ∈ T := Coord5.Rg_le_T (c := c) (c.liftEl_mem i)

theorem Coord5.exists_liftEl
    {g : G} (hg : g ∈ c.lift Rm) : g = c.liftEl (idx16 (c.rco g)) := by
  have hr : c.rco g ∈ Rm := Coord5.rco_mem c hg
  refine Coord5.rco_inj c (Coord5.lift_mem_cent hg) (c.liftEl_mem_C _) ?_
  rw [c.rco_liftEl, el16_idx16 hr]

theorem Coord5.liftEl_inj
    {i j : Fin 16} (hij : c.liftEl i = c.liftEl j) : i = j := by
  have := congrArg c.rco hij
  rw [c.rco_liftEl, c.rco_liftEl] at this
  have h2 := congrArg idx16 this
  rwa [idx16_el16, idx16_el16] at h2

theorem Coord5.liftEl_xor
    (i j : Fin 16) :
    c.liftEl (xor16 i j) = c.liftEl i * c.liftEl j := by
  refine Coord5.rco_inj c (c.liftEl_mem_C _) (mul_mem (c.liftEl_mem_C _) (c.liftEl_mem_C _)) ?_
  rw [Coord5.rco_mul c (c.liftEl_mem_C _) (c.liftEl_mem_C _), c.rco_liftEl, c.rco_liftEl,
    c.rco_liftEl, el16_xor]

theorem el16_zero : el16 0 = 1 :=
  Certificates.certificate5070

theorem Coord5.liftEl_zero :
    c.liftEl 0 = 1 := by
  refine Coord5.rco_inj c (c.liftEl_mem_C _) (one_mem _) ?_
  rw [c.rco_liftEl, el16_zero, Coord5.rco_one]

theorem Coord5.liftEl_sq
    (i : Fin 16) : c.liftEl i * c.liftEl i = 1 := by
  rw [← c.liftEl_xor]
  have : xor16 i i = 0 := Fin.ext (by simp [xor16])
  rw [this, c.liftEl_zero]


noncomputable def Coord5.rhoFun
    (n : G) (i : Fin 16) : Fin 16 :=
  idx16 (c.rco (n * c.liftEl i * n⁻¹))

variable {c}

theorem Coord5.rhoFun_spec
    {n : G} (hn : n ∈ normalizer ((c.lift Rm : Subgroup G) : Set G))
    (i : Fin 16) : c.liftEl (c.rhoFun n i) = n * c.liftEl i * n⁻¹ := by
  have hr : n * c.liftEl i * n⁻¹ ∈ c.lift Rm := (mem_normalizer_iff.1 hn _).1 (c.liftEl_mem i)
  exact (Coord5.exists_liftEl c hr).symm

theorem Coord5.rhoFun_mul
    {n n' : G} (hn : n ∈ normalizer ((c.lift Rm : Subgroup G) : Set G))
    (hn' : n' ∈ normalizer ((c.lift Rm : Subgroup G) : Set G)) (i : Fin 16) :
    c.rhoFun (n * n') i = c.rhoFun n (c.rhoFun n' i) := by
  apply Coord5.liftEl_inj c
  rw [Coord5.rhoFun_spec (mul_mem hn hn'), Coord5.rhoFun_spec hn, Coord5.rhoFun_spec hn']
  group

theorem Coord5.rhoFun_one
    (i : Fin 16) : c.rhoFun 1 i = i := by
  apply Coord5.liftEl_inj c
  rw [Coord5.rhoFun_spec (one_mem _)]
  group

theorem Coord5.rhoFun_xor
    {n : G} (hn : n ∈ normalizer ((c.lift Rm : Subgroup G) : Set G))
    (i j : Fin 16) : c.rhoFun n (xor16 i j) = xor16 (c.rhoFun n i) (c.rhoFun n j) := by
  apply Coord5.liftEl_inj c
  rw [Coord5.rhoFun_spec hn, Coord5.liftEl_xor, Coord5.liftEl_xor, Coord5.rhoFun_spec hn,
    Coord5.rhoFun_spec hn]
  group

variable (c)

@[expose] noncomputable def Coord5.rhoPerm
    (n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G))) :
    Perm (Fin 16) where
  toFun := c.rhoFun (n : G)
  invFun := c.rhoFun ((n : G)⁻¹)
  left_inv := fun i => by
    rw [← Coord5.rhoFun_mul (inv_mem n.2) n.2, inv_mul_cancel, Coord5.rhoFun_one]
  right_inv := fun i => by
    rw [← Coord5.rhoFun_mul n.2 (inv_mem n.2), mul_inv_cancel, Coord5.rhoFun_one]

@[expose] noncomputable def Coord5.rhoG :
    ↥(normalizer ((c.lift Rm : Subgroup G) : Set G)) →* Perm (Fin 16) where
  toFun := c.rhoPerm
  map_one' := Equiv.ext fun i => Coord5.rhoFun_one i
  map_mul' n n' := Equiv.ext fun i => by
    simp only [Equiv.Perm.mul_apply]
    exact Coord5.rhoFun_mul n.2 n'.2 i

theorem Coord5.rhoG_apply
    (n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G))) (i : Fin 16) :
    c.rhoG n i = c.rhoFun (n : G) i := rfl

theorem Coord5.rhoG_spec
    (n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G))) (i : Fin 16) :
    c.liftEl (c.rhoG n i) = (n : G) * c.liftEl i * (n : G)⁻¹ :=
  Coord5.rhoFun_spec n.2 i

theorem Coord5.rhoG_xor
    (n : ↥(normalizer ((c.lift Rm : Subgroup G) : Set G))) (i j : Fin 16) :
    c.rhoG n (xor16 i j) = xor16 (c.rhoG n i) (c.rhoG n j) :=
  Coord5.rhoFun_xor n.2 i j

theorem Coord5.T_le_N :
    T ≤ normalizer ((c.lift Rm : Subgroup G) : Set G) := fun t ht =>
  (mem_normalizer_iff).2 fun r => ⟨fun hr => Coord5.Rg_norm_T (c := c) ht hr, fun hr => by
    have := Coord5.Rg_norm_T (c := c) (T.inv_mem ht) hr
    simpa [mul_assoc] using this⟩

theorem Coord5.rhoG_T
    {t : G} (ht : t ∈ T) (i : Fin 16) :
    c.rhoG ⟨t, Coord5.T_le_N c ht⟩ i = actF (c.rco t) i := by
  rw [Coord5.rhoG_apply, Coord5.rhoFun, actF]
  congr 1
  rw [Coord5.rco_T_mul c (T.mul_mem ht (c.liftEl_mem_T i)) (T.inv_mem ht),
    Coord5.rco_T_mul c ht (c.liftEl_mem_T i), Coord5.rco_T_inv c ht, c.rco_liftEl]

theorem Coord5.rhoG_wC (i : Fin 16) :
    c.rhoG ⟨(c.wC : G), w_mem_N h c⟩ i = wHat i := by
  rw [Coord5.rhoG_apply, Coord5.rhoFun, ← actF_wm]
  unfold actF
  congr 1
  rw [Coord5.rco_conj_w c (c.liftEl_mem_C i), c.rco_liftEl]

theorem Coord5.R_le_N :
    c.lift Rm ≤ normalizer ((c.lift Rm : Subgroup G) : Set G) :=
  Subgroup.le_normalizer

theorem Coord5.rhoG_R
    {r : G} (hr : r ∈ c.lift Rm) (i : Fin 16) :
    c.rhoG ⟨r, Coord5.R_le_N c hr⟩ i = i := by
  apply Coord5.liftEl_inj c
  rw [Coord5.rhoG_spec]
  have hcomm : r * c.liftEl i = c.liftEl i * r :=
    Coord5.lift_comm (c := c) (M := Rm) (fun p hp q hq => Rm_comm p hp q hq) hr (c.liftEl_mem i)
  rw [hcomm]
  group

end Lift

end CFSG.GH74.GLS.C3.Layer2.L5
