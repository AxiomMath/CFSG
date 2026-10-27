module

public import CFSG.ClassicalInvolution.RouteD.TWU2Sep
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWU

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.RouteD.TWE.B6
  CliffordAlgebra
open CFSG.ClassicalInvolution.Generic (Commutes fundamentalSubgroups)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Model

variable {p f : ℕ} [Fact p.Prime]


local notation "𝔔₅" => quadMinus 5 (GaloisField p f) (Prod.fst (minusCoeffs p f))
  (Prod.snd (minusCoeffs p f))

local notation "n0" => (⟨0, by norm_num⟩ : Fin (5 - 1))
local notation "n1" => (⟨1, by norm_num⟩ : Fin (5 - 1))
local notation "n2" => (⟨2, by norm_num⟩ : Fin (5 - 1))
local notation "n3" => (⟨3, by norm_num⟩ : Fin (5 - 1))

theorem chain_twin_model (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hi : ∃ i : GaloisField p f, i * i = -1)
    {R₀ R₁ RT : Subgroup (spinGroup 𝔔₅)}
    (h₀ : R₀ ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 (minusCoeffs_irr p f)))
    (h₁ : R₁ ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 (minusCoeffs_irr p f)))
    (hT : RT ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 (minusCoeffs_irr p f)))
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W R₀ R₁) (hTne : RT ≠ R₀)
    (hTinv : ∃ r r', InvOf R₀ r ∧ InvOf RT r' ∧ r⁻¹ * r' ∈ Subgroup.center (spinGroup 𝔔₅)) :
    ChainTwin (fundamentalSubgroups .POmegaMinus (minusDatum 5 (minusCoeffs_irr p f)))
      (GaloisField p f) R₀ R₁ RT := by
  classical
  obtain ⟨i, hi⟩ := hi
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf0
  have hirr := minusCoeffs_irr p f
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have hodd : Odd (Nat.card (GaloisField p f)) := hK ▸ (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaMinus 5 p f :=
    ⟨Fact.out, hf1, by show 4 ≤ 5; omega⟩
  have cq := Exotic.centralQuot_minus hp2 hq hadm
  have hq4 : 4 ≤ p ^ f := by omega
  have hQ : (quadMinus 5 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite 5 (GaloisField p f) hirr)
  have hfr10 : Module.finrank (GaloisField p f)
      (Fin (5 - 1) ⊕ Fin (5 - 1) ⊕ Fin 2 → GaloisField p f) = 10 := by
    rw [finrank_minus p f 5 (by omega)]
  have : Nontrivial (Fin (5 - 1) ⊕ Fin (5 - 1) ⊕ Fin 2 → GaloisField p f) :=
    Module.nontrivial_of_finrank_pos (R := GaloisField p f) (by rw [hfr10]; norm_num)
  set F₀ : HypFrame 𝔔₅ (5 - 1) := (minusFrame 5 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame
    with hF₀
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair_gen hp2 hq hQ (m := 5 - 1) (by norm_num) F₀
    (by omega) cq h₀ h₁ hadj hlin
  have hQ0 := hQ.ne_zero
  have h01 : n0 ≠ n1 := by simp
  have h12 : n1 ≠ n2 := by simp
  have h23 : n2 ≠ n3 := by simp
  have h02 : n0 ≠ n2 := by simp
  have h03 : n0 ≠ n3 := by simp
  have h13 : n1 ≠ n3 := by simp
  obtain ⟨R₀', hR₀'e⟩ : ∃ R, R = (F₀.longSL2 h01 true true).range.map
      (MulAut.conj x₀).toMonoidHom := ⟨_, rfl⟩
  obtain ⟨RJ, hRJe⟩ : ∃ R, R = (F₀.longSL2 h23 true false).range.map
      (MulAut.conj x₀).toMonoidHom := ⟨_, rfl⟩
  obtain ⟨RJ', hRJ'e⟩ : ∃ R, R = (F₀.longSL2 h23 true true).range.map
      (MulAut.conj x₀).toMonoidHom := ⟨_, rfl⟩
  have hR₀e : R₀ = (F₀.longSL2 h01 true false).range.map (MulAut.conj x₀).toMonoidHom := hx0
  have hR₁e : R₁ = (F₀.longSL2 h12 true false).range.map (MulAut.conj x₀).toMonoidHom := hx1
  have hR₀'f : R₀' ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 hirr) := by
    rw [hR₀'e]
    exact rootSL2_conj_mem_gen hq4 cq F₀ (a := 0) (b := 1) (by omega) (by omega) (by omega)
      true true x₀
  have hRJf : RJ ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 hirr) := by
    rw [hRJe]
    exact rootSL2_conj_mem_gen hq4 cq F₀ (a := 2) (b := 3) (by omega) (by omega) (by omega)
      true false x₀
  have hRJ'f : RJ' ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 hirr) := by
    rw [hRJ'e]
    exact rootSL2_conj_mem_gen hq4 cq F₀ (a := 2) (b := 3) (by omega) (by omega) (by omega)
      true true x₀
  have hRTeq : RT = R₀' :=
    eq_twin_of_involution hodd (by rw [hfr10]; norm_num) F₀ x₀ h01 cq hR₀e hR₀'e h₀ hR₀'f hT
      hTne hTinv
  have hd8 : 8 < Module.finrank (GaloisField p f)
      (Fin (5 - 1) ⊕ Fin (5 - 1) ⊕ Fin 2 → GaloisField p f) := by rw [hfr10]; norm_num
  have cJ0 : Commutes RJ R₀ := by
    rw [hRJe, hR₀e]
    exact (commutes_map_equiv (MulAut.conj x₀)).mpr (commutes_rootSL2_disjoint F₀ (a := 2) (b := 3)
      (c := 0) (d := 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) true false true false)
  have cJT : Commutes RJ RT := by
    rw [hRTeq, hRJe, hR₀'e]
    exact (commutes_map_equiv (MulAut.conj x₀)).mpr (commutes_rootSL2_disjoint F₀ (a := 2) (b := 3)
      (c := 0) (d := 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) true false true true)
  have cJ'0 : Commutes RJ' R₀ := by
    rw [hRJ'e, hR₀e]
    exact (commutes_map_equiv (MulAut.conj x₀)).mpr (commutes_rootSL2_disjoint F₀ (a := 2) (b := 3)
      (c := 0) (d := 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) true true true false)
  have cJ'T : Commutes RJ' RT := by
    rw [hRTeq, hRJ'e, hR₀'e]
    exact (commutes_map_equiv (MulAut.conj x₀)).mpr (commutes_rootSL2_disjoint F₀ (a := 2) (b := 3)
      (c := 0) (d := 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) true true true true)
  have cJJ' : Commutes RJ RJ' := by
    rw [hRJe, hRJ'e]
    exact (commutes_map_equiv (MulAut.conj x₀)).mpr (commutes_rootSL2_twin F₀ (a := 2) (b := 3)
      (by omega) (by omega) (by omega) true)
  have hne : RJ' ≠ RJ := by
    intro h
    have h1 := congrArg (Subgroup.map (spinAction _)) h
    rw [hRJ'e, hRJe, map_conj_longSL2_range, map_conj_longSL2_range, toFrame_map_true_true] at h1
    exact Frame.La_range_ne_swap_La_range _ h1.symm
  have hlinJ : ∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ RJ := by
    obtain ⟨W, hW⟩ := linearBlockStandardPair_minusDatum hirr h2 (n := 5) (by norm_num)
      (i := n1) (j := n2) rfl (by norm_num)
    have hrk : ∀ (k : ℕ) (hk : k + 1 < 5 - 1),
        rankOne (minusDatum 5 hirr).rootGroup (⟨k, by omega⟩ : Fin (5 - 1)) =
          rootSL2 F₀ k (k + 1) (by omega) hk (by omega) true false := fun k hk =>
      rankOne_minusDatum_of_lt hirr (k := ⟨k, by omega⟩) hk
    rw [hrk 1 (by norm_num), hrk 2 (by norm_num)] at hW
    refine ⟨W.map (MulAut.conj x₀).toMonoidHom, ?_⟩
    rw [hR₁e, hRJe]
    exact linearBlockStandardPair_map_equiv (MulAut.conj x₀) hW
  have hsepJ := not_mem_center_of_orth hodd hd8 F₀ x₀ h01 h23 h02 h03 h12 h13 cq false h₀ hR₀e hRJe
  have hsepJ' := not_mem_center_of_orth hodd hd8 F₀ x₀ h01 h23 h02 h03 h12 h13 cq true h₀ hR₀e
    hRJ'e
  refine ⟨RJ, RJ', hRJf, hRJ'f, cJ0, cJT, cJ'0, cJ'T, cJJ', hne, hlinJ, hsepJ, hsepJ', ?_⟩
  have sqA : MulAut.conj x₀ (F₀.longSL2 h01 true false (diagI i hi)) *
      MulAut.conj x₀ (F₀.longSL2 h01 true false (diagI i hi)) =
      MulAut.conj x₀ (F₀.longSL2 h01 true false (-1)) := by
    rw [conj_longSL2_mul_self, diagI_mul_self_sl]
  have sqA' : MulAut.conj x₀ (F₀.longSL2 h01 true true (diagM i hi)) *
      MulAut.conj x₀ (F₀.longSL2 h01 true true (diagM i hi)) =
      MulAut.conj x₀ (F₀.longSL2 h01 true true (-1)) := by
    rw [conj_longSL2_mul_self, diagM_mul_self_sl]
  have sqB : MulAut.conj x₀ (F₀.longSL2 h23 true false (diagI i hi)) *
      MulAut.conj x₀ (F₀.longSL2 h23 true false (diagI i hi)) =
      MulAut.conj x₀ (F₀.longSL2 h23 true false (-1)) := by
    rw [conj_longSL2_mul_self, diagI_mul_self_sl]
  have sqB' : MulAut.conj x₀ (F₀.longSL2 h23 true true (diagI i hi)) *
      MulAut.conj x₀ (F₀.longSL2 h23 true true (diagI i hi)) =
      MulAut.conj x₀ (F₀.longSL2 h23 true true (-1)) := by
    rw [conj_longSL2_mul_self, diagI_mul_self_sl]
  have hP : spinAction _ (MulAut.conj x₀ (F₀.longSL2 h01 true false (diagI i hi)) *
        MulAut.conj x₀ (F₀.longSL2 h01 true true (diagM i hi)) *
        (MulAut.conj x₀ (F₀.longSL2 h23 true false (diagI i hi)) *
          MulAut.conj x₀ (F₀.longSL2 h23 true true (diagI i hi)))) =
      spinAction _ (MulAut.conj x₀ (F₀.longSL2 h12 true false (-1))) :=
    spinAction_chain F₀ x₀ h01 h12 h23 i hi
  refine ⟨MulAut.conj x₀ (F₀.longSL2 h01 true false (diagI i hi)),
    MulAut.conj x₀ (F₀.longSL2 h01 true true (diagM i hi)),
    MulAut.conj x₀ (F₀.longSL2 h23 true false (diagI i hi)),
    MulAut.conj x₀ (F₀.longSL2 h23 true true (diagI i hi)),
    MulAut.conj x₀ (F₀.longSL2 h12 true false (-1)), spinGroup.negOne _ hQ0, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR₀e]
    exact conj_mem_map_range F₀ h01 true false x₀ _
  · rw [hRTeq, hR₀'e]
    exact conj_mem_map_range F₀ h01 true true x₀ _
  · rw [hRJe]
    exact conj_mem_map_range F₀ h23 true false x₀ _
  · rw [hRJ'e]
    exact conj_mem_map_range F₀ h23 true true x₀ _
  · rw [hR₁e]
    exact conj_mem_map_range F₀ h12 true false x₀ _
  · intro r hr hord
    rw [sqA]
    exact eq_conj_longSL2_neg_one h2 F₀ h01 true false x₀ (by rw [← hR₀e]; exact hr) hord
  · intro r hr hord
    rw [hRTeq, hR₀'e] at hr
    rw [sqA']
    exact eq_conj_longSL2_neg_one h2 F₀ h01 true true x₀ hr hord
  · intro r hr hord
    rw [sqB]
    exact eq_conj_longSL2_neg_one h2 F₀ h23 true false x₀ (by rw [← hRJe]; exact hr) hord
  · intro r hr hord
    rw [sqB']
    exact eq_conj_longSL2_neg_one h2 F₀ h23 true true x₀ (by rw [← hRJ'e]; exact hr) hord
  · intro r hr hord
    exact eq_conj_longSL2_neg_one h2 F₀ h12 true false x₀ (by rw [← hR₁e]; exact hr) hord
  · exact Subgroup.mem_center_iff.mpr fun y => mul_negOne_comm hQ0 y
  · rw [sqA, sqA']
    exact conj_longSL2_neg_one_mul_twin hQ0 F₀ h01 true false x₀
  · rw [sqB, sqB']
    exact conj_longSL2_neg_one_mul_twin hQ0 F₀ h23 true false x₀
  · exact eq_or_eq_negOne_mul hQ hP

end Model
end CFSG.ClassicalInvolution.RouteD.TWU
