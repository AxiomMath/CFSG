module

public import CFSG.LocalAnalysis.SteinbergSFCentralInvolutionFusion
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisStructure

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialSwap

open Subgroup
open CFSG.LocalAnalysis.SymplecticFourStandard GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.LocalAnalysis.SymplecticFourRankThompson (minorAut_sq_pow_uElt)

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem mul_uElt_ne_of_ne_zero (g : antiSp K) {b c : K} (hb : b ≠ 0) :
    g * uElt 0 b 0 0 ≠ uElt 0 0 c 0 * g := by
  intro h
  have hm := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h
  have hinv := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) (inv_mul_cancel g)
  simp only [Subgroup.coe_mul, Units.val_mul, glMat_uElt, OneMemClass.coe_one,
    Units.val_one] at hm hinv
  set G : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hG
  set G' : Matrix (Fin 4) (Fin 4) K :=
    (((g⁻¹ : antiSp K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hG'
  have e : ∀ i j : Fin 4, (G * uMat (0 : K) b 0 0) i j = (uMat (0 : K) 0 c 0 * G) i j :=
    fun i j => by rw [hm]
  have f : ∀ i j : Fin 4, (G' * G) i j = (1 : Matrix (Fin 4) (Fin 4) K) i j :=
    fun i j => by rw [hinv]
  have e12 := e 1 2
  have e22 := e 2 2
  have e32 := e 3 2
  have e13 := e 1 3
  have e23 := e 2 3
  have e33 := e 3 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat, hb] at e12 e22 e32 e13 e23 e33
  have f00 := f 0 0
  have f10 := f 1 0
  have f11 := f 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, e12, e22, e32, e13, e23, e33] at f00 f10 f11
  rcases f10 with h0 | h0
  · rw [h0, zero_mul] at f11
    exact zero_ne_one f11
  · rw [h0, mul_zero] at f00
    exact zero_ne_one f00

variable [Finite K]

theorem odd_of_conj_mul_pow_maps_rootU {g : antiSp K} {j : ℕ}
    (hα : ∀ x ∈ rootU K Axis.two, (MulAut.conj g * minorAut K ^ j) x ∈ rootU K Axis.one) :
    Odd j := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
  · exfalso
    have hx : uElt (0 : K) 0 1 0 ∈ rootU K Axis.two := ⟨1, rfl⟩
    have h1 := hα _ hx
    have hfix : (minorAut K ^ (2 * m)) (uElt 0 0 1 0) = uElt 0 0 1 0 := by
      rw [pow_mul, minorAut_sq_pow_uElt]
      have h0 : (0 : K) ^ 2 ^ m = 0 := zero_pow (pow_ne_zero m two_ne_zero)
      rw [h0, one_pow]
    rw [MulAut.mul_apply, hfix, MulAut.conj_apply] at h1
    obtain ⟨b, hb⟩ := h1
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [uElt_zero_eq_one, mul_inv_eq_one] at hb
      have h2 : uElt (0 : K) 0 1 0 = 1 := by
        have := congrArg (fun y => g⁻¹ * y) hb
        simpa using this
      rw [← uElt_zero_eq_one] at h2
      exact one_ne_zero (uElt_inj h2).2.2.1
    apply mul_uElt_ne_of_ne_zero g⁻¹ (c := 1) hb0
    calc g⁻¹ * uElt 0 b 0 0 = g⁻¹ * (g * uElt 0 0 1 0 * g⁻¹) := by rw [hb]
      _ = uElt 0 0 1 0 * g⁻¹ := by group
  · exact ⟨m, rfl⟩

theorem minorAut_pow_mem_inner_iff {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (m : ℕ) :
    minorAut K ^ m ∈ inner (antiSp K) ↔ 2 * n ∣ m := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := exists_frobenius_data hn hK
  obtain ⟨-, -, -, -, -, -, -, -, hmem, -⟩ := exceptionalAut_structure hn hFr hord hzp
  rw [← mem_inner_iff_autCongr, autCongr_pow, autCongr_minorAut, hmem]

theorem odd_of_aut_swap {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {α : MulAut (antiSp K)}
    (hα : ∀ x ∈ rootU K Axis.two, α x ∈ rootU K Axis.one) (hα2 : α * α ∈ inner (antiSp K)) :
    Odd n := by
  obtain ⟨g, j, -, rfl⟩ := aut_eq_conj_mul_pow hn hK α
  have hj := odd_of_conj_mul_pow_maps_rootU hα
  have hN := inner_normal (antiSp K)
  have hcg : MulAut.conj g ∈ inner (antiSp K) := ⟨g, rfl⟩
  have hconj : minorAut K ^ j * MulAut.conj g * (minorAut K ^ j)⁻¹ ∈ inner (antiSp K) :=
    hN.conj_mem _ hcg _
  have h2j : minorAut K ^ (2 * j) ∈ inner (antiSp K) := by
    have e : minorAut K ^ (2 * j) = (MulAut.conj g * (minorAut K ^ j * MulAut.conj g *
        (minorAut K ^ j)⁻¹))⁻¹ * ((MulAut.conj g * minorAut K ^ j) *
        (MulAut.conj g * minorAut K ^ j)) := by
      rw [two_mul, pow_add]
      group
    rw [e]
    exact mul_mem (inv_mem (mul_mem hcg hconj)) hα2
  have hdvd := (minorAut_pow_mem_inner_iff hn hK _).mp h2j
  have hnj : n ∣ j := Nat.dvd_of_mul_dvd_mul_left two_pos hdvd
  exact Odd.of_dvd_nat hj hnj

end Model

section Swap

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K]
  {n : ℕ} {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G}

theorem odd_of_swap (hS : Setup L K n φ TG t) {u : G} (huC : u ∈ centralizer ({t} : Set G))
    (hU : ∀ x ∈ pull φ (rootU K Axis.two), u * x * u⁻¹ ∈ pull φ (rootU K Axis.one))
    {l : G} (hl : l ∈ L) (hcent : l⁻¹ * (u * u) ∈ centralizer (L : Set G)) : Odd n := by
  refine odd_of_aut_swap (α := subAct φ hS.cent_le ⟨u, huC⟩) (by have := hS.two_le; omega)
    hS.card_K (fun x hx => ?_) ?_
  · have h1 : ((φ.symm (subAct φ hS.cent_le ⟨u, huC⟩ x) : L) : G) = u * φ.symm x * u⁻¹ :=
      subAct_symm_apply φ hS.cent_le ⟨u, huC⟩ x
    have h2 := hU _ (symm_mem_pull.mpr hx)
    rw [← h1] at h2
    exact symm_mem_pull.mp h2
  · have hlC : l ∈ centralizer ({t} : Set G) := hS.L_le hl
    have hcC : l⁻¹ * (u * u) ∈ centralizer ({t} : Set G) :=
      mul_mem (inv_mem hlC) (mul_mem huC huC)
    have e : (⟨u, huC⟩ * ⟨u, huC⟩ : centralizer ({t} : Set G)) =
        ⟨l, hlC⟩ * ⟨l⁻¹ * (u * u), hcC⟩ := Subtype.ext (by simp)
    rw [← map_mul, e, map_mul, subAct_of_eq φ hS.cent_le (l := ⟨l, hl⟩) rfl,
      (subAct_eq_one_iff φ hS.cent_le _).mpr hcent, mul_one]
    exact ⟨_, rfl⟩

end Swap

end BothTrivialSwap

end CFSG.LocalAnalysis.EvenBN.Sp4
