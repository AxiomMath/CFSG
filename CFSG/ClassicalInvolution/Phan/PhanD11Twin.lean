module

public import CFSG.ClassicalInvolution.Phan.PhanD10Twin
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
import CFSG.ClassicalInvolution.RouteD.TypeDModel
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy
public import CFSG.LieType.HighestRoot.CentSpinBasic
public import CFSG.LieType.HighestRoot.Defs
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.PhanD4

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.HighestRoot
open scoped MatrixGroups commutatorElement

section General

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}

theorem conj_lift_props (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    (x : spinGroup Q) (fr : Frame Q)
    (hx : ∀ A, fr.La A = spinAction Q x * (F₀.toFrame hij s t).La A * (spinAction Q x)⁻¹)
    (hperf : Group.IsPerfect SL(2, K)) :
    ((F₀.longSL2 hij s t).range.map (MulAut.conj x).toMonoidHom).map (spinAction Q) =
        fr.La.range ∧
      ⁅(F₀.longSL2 hij s t).range.map (MulAut.conj x).toMonoidHom,
        (F₀.longSL2 hij s t).range.map (MulAut.conj x).toMonoidHom⁆ =
        (F₀.longSL2 hij s t).range.map (MulAut.conj x).toMonoidHom ∧
      ∀ r ∈ (F₀.longSL2 hij s t).range.map (MulAut.conj x).toMonoidHom,
        spinAction Q r = 1 → r = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_conj_map, map_longSL2_range, La_range_eq_map_conj hx]
  · have hR₀ : ⁅(F₀.longSL2 hij s t).range, (F₀.longSL2 hij s t).range⁆ =
        (F₀.longSL2 hij s t).range :=
      Subgroup.isPerfect_iff.mp (Group.IsPerfect.range _)
    rw [← Subgroup.map_commutator, hR₀]
  · rintro r ⟨_, ⟨A, rfl⟩, rfl⟩ hr
    have hθ := DFunLike.congr_fun (spinAction_comp_longSL2 F₀ hij s t) A
    have h1 : (F₀.toFrame hij s t).La A = 1 := by
      have h2' : spinAction Q x * spinAction Q (F₀.longSL2 hij s t A) *
          (spinAction Q x)⁻¹ = 1 := by
        simpa [MulAut.conj_apply, map_mul, map_inv] using hr
      rw [← hθ]
      simpa using h2'
    have : A = 1 :=
      (F₀.toFrame hij s t).La_injective (h1.trans (F₀.toFrame hij s t).La.map_one.symm)
    subst this
    simp

theorem longSL2_inf_twin (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    (h2 : (2 : K) ≠ 0) :
    (F₀.longSL2 hij s t).range ⊓ (F₀.longSL2 hij s (!t)).range = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨M, rfl⟩, ⟨M', hM'⟩⟩
  rw [Subgroup.mem_bot]
  have h1 : (F₀.toFrame hij s t).La M = (F₀.toFrame hij s t).swap.La M' := by
    rw [← spinAction_longSL2, ← toFrame_not, ← spinAction_longSL2, hM']
  have hmem : (F₀.toFrame hij s t).La M ∈ (F₀.toFrame hij s t).swap.La.range := ⟨M', h1.symm⟩
  rcases (Frame.La_mem_swap_range_iff _ M).mp hmem with rfl | rfl
  · simp
  · exfalso
    have hM'1 : M' = -1 := by
      refine (F₀.toFrame hij s t).swap.La_injective ?_
      rw [← h1, ← Frame.La_swap_neg_one]
    subst hM'1
    have e1 := congrArg (fun z : spinGroup Q => (z : CliffordAlgebra Q)) hM'
    have e2 := coe_longSL2_not_neg_one F₀ hij s t
    rw [e2] at e1
    exact coe_ne_neg_coe h2 _ e1.symm

end General

section Twin

variable {p e : ℕ} [Fact p.Prime]

theorem toFrame_congr {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {m : ℕ} (F₀ : HypFrame Q m) {i j i' j' : Fin m} (h1 : i = i')
    (h2 : j = j') (hij : i ≠ j) (hij' : i' ≠ j') (s t : Bool) :
    F₀.toFrame hij s t = F₀.toFrame hij' s t := by
  subst h1 h2
  rfl

theorem longSL2_congr {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {m : ℕ} (F₀ : HypFrame Q m) {i j i' j' : Fin m} (h1 : i = i')
    (h2 : j = j') (hij : i ≠ j) (hij' : i' ≠ j') (s t : Bool) :
    F₀.longSL2 hij s t = F₀.longSL2 hij' s t := by
  subst h1 h2
  rfl

theorem exists_lift_frame_twin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (fr : Frame (quadPlus 4 (GaloisField p e))) :
    ∃ R R' : Subgroup (spinGroup (quadPlus 4 (GaloisField p e))),
      R ∈ longestFundamental (plusDatum 4 (GaloisField p e) (by norm_num)) ∧
      R' ∈ longestFundamental (plusDatum 4 (GaloisField p e) (by norm_num)) ∧
      R.map (spinAction (quadPlus 4 (GaloisField p e))) = fr.La.range ∧
      R'.map (spinAction (quadPlus 4 (GaloisField p e))) = fr.swap.La.range ∧
      ⁅R, R⁆ = R ∧ ⁅R', R'⁆ = R' ∧
      (∀ r ∈ R, spinAction (quadPlus 4 (GaloisField p e)) r = 1 → r = 1) ∧
      (∀ r ∈ R', spinAction (quadPlus 4 (GaloisField p e)) r = 1 → r = 1) ∧
      R ⊓ R' = ⊥ := by
  obtain ⟨hodd, h4⟩ := card_galoisField_facts hp2 hq
  have hn3 : 3 ≤ 4 := by norm_num
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have hperf : Group.IsPerfect SL(2, GaloisField p e) := sl2_isPerfect h4
  have : Invertible (2 : GaloisField p e) := invertibleOfNonzero h2
  have hdim : Module.finrank (GaloisField p e) (Fin 4 ⊕ Fin 4 → GaloisField p e) = 2 * 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  let H₀ := plusFrame 4 (GaloisField p e) hn3
  have hij3 : rootIdxD 4 (3 : Fin 4) ≠ rootIdxD' 4 (3 : Fin 4) := rootIdxD_ne 4 (by omega) 3
  have hij2 : rootIdxD 4 (2 : Fin 4) ≠ rootIdxD' 4 (2 : Fin 4) := rootIdxD_ne 4 (by omega) 2
  have hs3 : rootSignD 4 (3 : Fin 4) = true := by decide
  have hs2 : rootSignD 4 (2 : Fin 4) = false := by decide
  have hperp : 2 ≤ Module.finrank (GaloisField p e) (H₀.toFrame hij3 true true).perp := by
    have := finrank_perp_add_four (H₀.toFrame hij3 true true)
    omega
  obtain ⟨x, g, hxg, hmap⟩ := exists_spin_conj_map hodd
    (nondegenerate_polarBilin_quadPlus 4 (GaloisField p e)) (H₀.toFrame hij3 true true) fr hperp
  subst hmap
  have hx : ∀ A, ((H₀.toFrame hij3 true true).map g.2).La A =
      spinAction (quadPlus 4 (GaloisField p e)) x * (H₀.toFrame hij3 true true).La A *
        (spinAction (quadPlus 4 (GaloisField p e)) x)⁻¹ := by
    intro A
    rw [hxg]
    exact Frame.map_La _ g.2 A
  have hx2 : ∀ A, ((H₀.toFrame hij3 true true).map g.2).swap.La A =
      spinAction (quadPlus 4 (GaloisField p e)) x * (H₀.toFrame hij2 true false).La A *
        (spinAction (quadPlus 4 (GaloisField p e)) x)⁻¹ := by
    intro A
    have hfr : H₀.toFrame hij2 true false = (H₀.toFrame hij3 true true).swap := by
      rw [toFrame_congr H₀ (by decide : rootIdxD 4 (2 : Fin 4) = rootIdxD 4 (3 : Fin 4))
        (by decide : rootIdxD' 4 (2 : Fin 4) = rootIdxD' 4 (3 : Fin 4)) hij2 hij3 true false]
      exact toFrame_not H₀ hij3 true true
    rw [hfr, hxg]
    exact Frame.map_La (H₀.toFrame hij3 true true).swap g.2 A
  have hx1 : ∀ A, ((H₀.toFrame hij3 true true).map g.2).La A =
      spinAction (quadPlus 4 (GaloisField p e)) x *
        (H₀.toFrame hij3 true (rootSignD 4 (3 : Fin 4))).La A *
        (spinAction (quadPlus 4 (GaloisField p e)) x)⁻¹ := by
    intro A
    rw [hs3]
    exact hx A
  have hx2' : ∀ A, ((H₀.toFrame hij3 true true).map g.2).swap.La A =
      spinAction (quadPlus 4 (GaloisField p e)) x *
        (H₀.toFrame hij2 true (rootSignD 4 (2 : Fin 4))).La A *
        (spinAction (quadPlus 4 (GaloisField p e)) x)⁻¹ := by
    intro A
    rw [hs2]
    exact hx2 A
  have h3 := conj_lift_props H₀ hij3 true (rootSignD 4 (3 : Fin 4)) x _ hx1 hperf
  have h2' := conj_lift_props H₀ hij2 true (rootSignD 4 (2 : Fin 4)) x _ hx2' hperf
  have hi3 : (Pi.single (3 : Fin 4) 1 : Fin 4 → ℤ) ∈ (plusDatum 4 (GaloisField p e) hn3).roots :=
    CFSG.ClassicalInvolution.RouteD.single_mem_roots (plusDatum 4 (GaloisField p e) hn3)
      (3 : Fin 4)
  have hi2 : (Pi.single (2 : Fin 4) 1 : Fin 4 → ℤ) ∈ (plusDatum 4 (GaloisField p e) hn3).roots :=
    CFSG.ClassicalInvolution.RouteD.single_mem_roots (plusDatum 4 (GaloisField p e) hn3)
      (2 : Fin 4)
  have hL2 : H₀.longSL2 hij2 true (rootSignD 4 (2 : Fin 4)) =
      H₀.longSL2 hij3 true (!true) := by
    rw [hs2]
    exact longSL2_congr H₀ (by decide) (by decide) hij2 hij3 true false
  have hinf : (H₀.longSL2 hij3 true true).range ⊓
      (H₀.longSL2 hij2 true (rootSignD 4 (2 : Fin 4))).range = ⊥ := by
    rw [hL2]
    exact longSL2_inf_twin H₀ hij3 true true h2
  refine ⟨(H₀.longSL2 hij3 true (rootSignD 4 (3 : Fin 4))).range.map (MulAut.conj x).toMonoidHom,
    (H₀.longSL2 hij2 true (rootSignD 4 (2 : Fin 4))).range.map (MulAut.conj x).toMonoidHom,
    ⟨x, Pi.single (3 : Fin 4) 1,
      CFSG.ClassicalInvolution.RouteD.isLongestRoot_of_mem_roots_plusDatum hn3 hi3,
      congrArg (Subgroup.map (MulAut.conj x).toMonoidHom)
        (PlusCT.rankOne_plusRootGroup hn3 (3 : Fin 4) (n := 4)
          (K := GaloisField p e)).symm⟩,
    ⟨x, Pi.single (2 : Fin 4) 1,
      CFSG.ClassicalInvolution.RouteD.isLongestRoot_of_mem_roots_plusDatum hn3 hi2,
      congrArg (Subgroup.map (MulAut.conj x).toMonoidHom)
        (PlusCT.rankOne_plusRootGroup hn3 (2 : Fin 4) (n := 4)
          (K := GaloisField p e)).symm⟩,
    h3.1, h2'.1, h3.2.1, h2'.2.1, h3.2.2, h2'.2.2, ?_⟩
  rw [← Subgroup.map_inf _ _ (MulAut.conj x).toMonoidHom (MulAut.conj x).injective, hs3, hinf,
    Subgroup.map_bot]

end Twin

end CFSG.ClassicalInvolution.PhanD4
