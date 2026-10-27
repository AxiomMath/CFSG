module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeShortCore
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeOrthField

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt E mat_elt)
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.SeitzReduction.LinearPilot (upperUnit diagUnit weylUnit coe_weylUnit)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Weyl

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def weylPlaneOne : StatedSp 3 K :=
  longBlock K 3 1 weylUnit

@[expose] def rotThree : Equiv.Perm (Fin 3) :=
  (finRotate 3).symm

variable (K) in
@[expose] noncomputable def shortWeyl : StatedSp 3 K :=
  weylPlaneOne K * permSp K rotThree

theorem simpleRootHom_zero_upperUnit_one :
    simpleRootHom K (0 : Fin 3) (upperUnit 1) = elt (.difference 0 1 (by decide)) 1 := by
  rw [simpleRootHom_of_lt (by decide), upperUnit_eq_sl2Upper, shortBlock_sl2Upper]
  rfl

theorem weylPlaneOne_mul_twoCentralElt :
    weylPlaneOne K * twoCentralElt 3 (0 : Fin 3) 1 (0 : K) 1 =
      elt (.difference 0 1 (by decide)) 1 * weylPlaneOne K := by
  apply mat_injective
  rw [map_mul, map_mul, weylPlaneOne, mat_longBlock, mat_twoCentralElt_eq_add, mat_elt]
  ext r s
  rcases r with i | i <;> rcases s with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three, blockMat, E, coe_weylUnit,
      Matrix.single_apply, Matrix.one_apply]

theorem weylPlaneOne_mul_diagSp (r : Kˣ) :
    weylPlaneOne K * diagSp K 3 ![r, r⁻¹, 1] = diagSp K 3 ![r, r, 1] * weylPlaneOne K := by
  apply mat_injective
  rw [map_mul, map_mul, weylPlaneOne, mat_longBlock, mat_diagSp, mat_diagSp]
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three, blockMat, coe_weylUnit,
      Matrix.diagonal_apply, diagSpEntry]

theorem rotThree_apply_one : rotThree (1 : Fin 3) = 0 := rfl

theorem rotThree_apply_two : rotThree (2 : Fin 3) = 1 := rfl

theorem shortWeyl_conj_twoCentralElt :
    shortWeyl K * twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 * (shortWeyl K)⁻¹ =
      elt (.difference 0 1 (by decide)) 1 := by
  have hP := conj_permSp_twoCentralElt (K := K) rotThree (1 : Fin 3) 2 0 1
  rw [rotThree_apply_one, rotThree_apply_two] at hP
  have e1 : shortWeyl K * twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 * (shortWeyl K)⁻¹ =
      weylPlaneOne K * (permSp K rotThree * twoCentralElt 3 (1 : Fin 3) 2 (0 : K) 1 *
        (permSp K rotThree)⁻¹) * (weylPlaneOne K)⁻¹ := by
    rw [shortWeyl]
    group
  rw [e1, hP, weylPlaneOne_mul_twoCentralElt, mul_inv_cancel_right]

theorem shortWeyl_conj_diagSp (r : Kˣ) :
    shortWeyl K * diagSp K 3 ![1, r, r⁻¹] * (shortWeyl K)⁻¹ = diagSp K 3 ![r, r, 1] := by
  have hP := conj_permSp_diagSp (K := K) rotThree ![1, r, r⁻¹]
  have hcomp : (![1, r, r⁻¹] : Fin 3 → Kˣ) ∘ rotThree.symm = ![r, r⁻¹, 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp] at hP
  have e1 : shortWeyl K * diagSp K 3 ![1, r, r⁻¹] * (shortWeyl K)⁻¹ =
      weylPlaneOne K * (permSp K rotThree * diagSp K 3 ![1, r, r⁻¹] * (permSp K rotThree)⁻¹) *
        (weylPlaneOne K)⁻¹ := by
    rw [shortWeyl]
    group
  rw [e1, hP, weylPlaneOne_mul_diagSp, mul_inv_cancel_right]

theorem diagSp_rr1_mem_complSp_two (r : Kˣ) : diagSp K 3 ![r, r, 1] ∈ complSp K (2 : Fin 3) := by
  rw [mem_complSp]
  intro a b h
  rw [mat_diagSp]
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [mem_coords] at h ⊢

end Weyl

section Core

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

@[expose] noncomputable def shortChart (e : L ≃* StatedSp 3 K) : L ≃* StatedSp 3 K :=
  e.trans (MulAut.conj (shortWeyl K)⁻¹)

omit [Finite G] [Finite K] [CharP K 2] in
theorem shortChart_symm_apply (e : L ≃* StatedSp 3 K) (y : StatedSp 3 K) :
    (shortChart e).symm y = e.symm (shortWeyl K * y * (shortWeyl K)⁻¹) := by
  rw [shortChart, MulEquiv.symm_trans_apply, MulAut.conj_symm_apply, inv_inv]

omit [Finite G] [Finite K] [CharP K 2] in
theorem modelToG_shortChart_shortTorus_le (e : L ≃* StatedSp 3 K) :
    modelToG (shortChart e) (shortTorus K) ≤
      modelToG e (leviTorusSp K ({0} : Finset (Fin 3))) ⊓
        modelToG e (leviTorusSp K ({2} : Finset (Fin 3))) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (UnitaryPilot.mem_modelToG _).1 hx
  obtain ⟨r, rfl⟩ := mem_shortTorus.1 hy
  rw [shortChart_symm_apply, shortWeyl_conj_diagSp]
  exact ⟨UnitaryPilot.symm_mem_modelToG e (diagSp_rr1_mem_leviTorusSp_zero r),
    UnitaryPilot.symm_mem_modelToG e (diagSp_rr1_mem_leviTorusSp_two r)⟩

omit [Finite G] [Finite K] [CharP K 2] in
theorem modelToG_shortChart_shortTorus_le_complSp (e : L ≃* StatedSp 3 K) :
    modelToG (shortChart e) (shortTorus K) ≤ modelToG e (complSp K (2 : Fin 3)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (UnitaryPilot.mem_modelToG _).1 hx
  obtain ⟨r, rfl⟩ := mem_shortTorus.1 hy
  rw [shortChart_symm_apply, shortWeyl_conj_diagSp]
  exact UnitaryPilot.symm_mem_modelToG e (diagSp_rr1_mem_complSp_two r)

omit [Finite K] [CharP K 2] in
theorem elt_difference_zero_one_mem_complSp_two :
    elt (.difference 0 1 (by decide)) (1 : K) ∈ complSp K (2 : Fin 3) := by
  rw [← simpleRootHom_zero_upperUnit_one]
  exact simpleRootSL2_zero_le_complSp_two ⟨upperUnit 1, rfl⟩

theorem le_centralizer_of_conj_eq_mul_three_short_zero_two (hset : CFSG.EvenSmallLie.StandardSetting G L)
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L))
    (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {g : G}
    (hg : g⁻¹ * t * g = t * ((e.symm (elt (.difference 0 1 (by decide)) 1) : L) : G))
    {φ' : StatedSp 3 K →* G} (hφ' : Function.Injective φ')
    (hφ'r : φ'.range = CFSG.conjugate L g)
    (hφ'z : φ' (elt (.difference 0 1 (by decide)) 1) =
      ((e.symm (elt (.difference 0 1 (by decide)) 1) : L) : G))
    {S : Subgroup G} (hSperf : ⁅S, S⁆ = S)
    (hSsimple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤)
    (hSt : S ≤ centralizer ({g⁻¹ * t * g} : Set G))
    (hSY : S ≤ centralizer ((modelToG e (leviTorusSp K ({0} : Finset (Fin 3))) ⊓
      modelToG e (leviTorusSp K ({2} : Finset (Fin 3))) : Subgroup G) : Set G))
    (hzS : ((e.symm (elt (.difference 0 1 (by decide)) 1) : L) : G) ∈ S) :
    S ≤ centralizer (modelToG e (longRootSp2 K 3 (2 : Fin 3)) : Set G) := by
  set e' := shortChart e with he'
  set x : StatedSp 3 K := elt (.difference 0 1 (by decide)) 1 with hx
  have hz' : ((e'.symm (twoCentralElt 3 1 2 0 1) : L) : G) = ((e.symm x : L) : G) := by
    rw [he', shortChart_symm_apply, shortWeyl_conj_twoCentralElt]
  set φ₂ : StatedSp 3 K →* G := φ'.comp (MulAut.conj (shortWeyl K)).toMonoidHom with hφ₂
  have hφ₂inj : Function.Injective φ₂ := hφ'.comp (MulAut.conj (shortWeyl K)).injective
  have hφ₂r : φ₂.range = CFSG.conjugate L g := by
    rw [hφ₂, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj (shortWeyl K)).surjective,
      ← MonoidHom.range_eq_map, hφ'r]
  have hφ₂z : φ₂ (twoCentralElt 3 1 2 0 1) = ((e'.symm (twoCentralElt 3 1 2 0 1) : L) : G) := by
    rw [hz']
    change φ' (shortWeyl K * twoCentralElt 3 1 2 0 1 * (shortWeyl K)⁻¹) = _
    rw [shortWeyl_conj_twoCentralElt]
    exact hφ'z
  set B := modelToG e (longRootSp2 K 3 (2 : Fin 3)) with hBdef
  have hBperf : ⁅B, B⁆ = B := by
    have h2 : ¬ (2 : Fin 3).val + 1 < 3 := by decide
    rw [hBdef, UnitaryPilot.modelToG_def, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
      ← simpleRootSL2_of_not_lt h2, commutator_simpleRootSL2_eq_of_four_le hK 2]
  have hBL : B ≤ L := map_subtype_le _
  have hBC : B ≤ centralizer (modelToG e (complSp K (2 : Fin 3)) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e
      (fun _ ha => mem_centralizer_iff.2 fun _ hb =>
        (commute_of_mem_longRootSp2_of_mem_complSp ha hb).eq.symm)
  have hBz : B ≤ centralizer ({((e'.symm (twoCentralElt 3 1 2 0 1) : L) : G)} : Set G) := by
    rw [hz']
    exact hBC.trans (centralizer_le (Set.singleton_subset_iff.2
      (UnitaryPilot.symm_mem_modelToG e elt_difference_zero_one_mem_complSp_two)))
  have hBY : B ≤ centralizer (modelToG e' (shortTorus K) : Set G) :=
    hBC.trans (centralizer_le (modelToG_shortChart_shortTorus_le_complSp e))
  exact le_centralizer_of_conj_eq_mul_three_short hset hOut hK e' htC ht (by rw [hz']; exact hg)
    hφ₂inj hφ₂r hφ₂z hSperf hSsimple hSt
    (hSY.trans (centralizer_le (modelToG_shortChart_shortTorus_le e))) (by rw [hz']; exact hzS)
    hBperf hBL hBz hBY

end Core

end CFSG.SeitzReduction.SymplecticPilot
