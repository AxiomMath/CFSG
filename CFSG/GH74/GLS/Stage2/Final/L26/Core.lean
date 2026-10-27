module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Final19C

public section

namespace CFSG.GH74.GLS.Stage2.Final.L26

open Subgroup CFSG CFSG.LocalCores CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final.Thm4
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Abstract

theorem mem_of_two_pow_of_mem_sup_odd {Γ : Type*} [Group Γ] {K N : Subgroup Γ} [K.Normal]
    (hN : ∀ n ∈ N, Nat.Coprime (orderOf n) 2) {x : Γ} (hx : x ∈ K ⊔ N) {a : ℕ} (hxa : x ^ (2 ^ a) = 1) :
    x ∈ K := by
  have himg : (QuotientGroup.mk' K) x ∈ N.map (QuotientGroup.mk' K) := by
    have h' : (K ⊔ N).map (QuotientGroup.mk' K) = N.map (QuotientGroup.mk' K) := by
      rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' _).ge, bot_sup_eq]
    rw [← h']
    exact Subgroup.mem_map_of_mem _ hx
  obtain ⟨n, hn, hnx⟩ := himg
  have h1 : orderOf ((QuotientGroup.mk' K) x) ∣ 2 ^ a := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow, hxa, map_one]
  have h2 : orderOf ((QuotientGroup.mk' K) x) ∣ orderOf n := by
    rw [← hnx]
    exact orderOf_map_dvd _ _
  have h3 : orderOf ((QuotientGroup.mk' K) x) = 1 :=
    Nat.eq_one_of_dvd_coprimes ((hN n hn).pow_right a) h2 h1
  exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h3)

end Abstract

section Layer

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem layer_le_commutator {y : Y}
    (h2 : ∀ K : Subgroup Y, K.Normal → K ≤ layer Y →
      (¬ ∀ k ∈ K, ∀ e ∈ layer Y, k * e = e * k) → layer Y ≤ K)
    (hy : ¬ ∀ e ∈ layer Y, y * e = e * y) : layer Y ≤ ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆ := by
  have : (layer Y).Characteristic := layer_characteristic
  have hEn : (layer Y).Normal := inferInstance
  have hBn : (⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆).Normal := commutator_top_normal _
  have hKn : (⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆ ⊓ layer Y).Normal := inferInstance
  have hnc : ¬ ∀ k ∈ ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆ ⊓ layer Y, ∀ e ∈ layer Y, k * e = e * k := by
    intro hall
    apply hy
    have hcomm : ⁅layer Y, Subgroup.zpowers y⁆ ≤ ⁅(⊤ : Subgroup Y), Subgroup.zpowers y⁆ ⊓ layer Y := by
      refine Subgroup.commutator_le.2 fun e he c hc => ⟨Subgroup.commutator_mem_commutator trivial hc, ?_⟩
      have h3 : c * e⁻¹ * c⁻¹ ∈ layer Y := hEn.conj_mem e⁻¹ ((layer Y).inv_mem he) c
      have h4 : ⁅e, c⁆ = e * (c * e⁻¹ * c⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h4]
      exact (layer Y).mul_mem he h3
    have hdbl : ⁅⁅layer Y, Subgroup.zpowers y⁆, layer Y⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (hall k (hcomm hk) e he).symm
    have hbot := perfect_double_commutator (layer_perfect (G := Y)) hdbl
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    intro e he
    exact Subgroup.mem_centralizer_iff.mp (hbot he) y (Subgroup.mem_zpowers y)
  exact (h2 _ hKn inf_le_right hnc).trans inf_le_left

theorem not_centralizes_layer {y zb : Y} (h1 : generalizedFitting Y ≤ layer Y)
    (hcard : Nat.card ↥(center ↥(layer Y)) ≤ 2) (hzb : zb ∈ center Y) (hzb1 : zb ≠ 1) (hy1 : y ≠ 1)
    (hyz : y ≠ zb) : ¬ ∀ e ∈ layer Y, y * e = e * y := by
  intro hy
  have hyF : y ∈ generalizedFitting Y := by
    refine CFSG.centralizer_generalizedFitting_le Y ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (hy f (h1 hf)).symm
  have hzF : zb ∈ generalizedFitting Y := by
    refine CFSG.centralizer_generalizedFitting_le Y ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f _
    exact Subgroup.mem_center_iff.mp hzb f
  have hyc : (⟨y, h1 hyF⟩ : ↥(layer Y)) ∈ center ↥(layer Y) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hy g g.2).symm
  have hzc : (⟨zb, h1 hzF⟩ : ↥(layer Y)) ∈ center ↥(layer Y) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hzb g)
  let f : Fin 3 → ↥(center ↥(layer Y)) := ![1, ⟨_, hyc⟩, ⟨_, hzc⟩]
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Subtype.ext_iff]
  have := Nat.card_le_card_of_injective f hinj
  simp at this
  omega

end Layer

section Lift

variable {X : Type} [Group X] [Finite X]

theorem pLayer_le_commutator_of_bar (t : X)
    (h : layer (X ⧸ pPrimeCore 2 X) ≤
      ⁅(⊤ : Subgroup (X ⧸ pPrimeCore 2 X)), Subgroup.zpowers (QuotientGroup.mk' (pPrimeCore 2 X) t)⁆) :
    pLayer X 2 ≤ ⁅(⊤ : Subgroup X), Subgroup.zpowers t⁆ := by
  have hBn : (⁅(⊤ : Subgroup X), Subgroup.zpowers t⁆).Normal := commutator_top_normal _
  have hmapB : (⁅(⊤ : Subgroup X), Subgroup.zpowers t⁆).map (QuotientGroup.mk' (pPrimeCore 2 X)) =
      ⁅(⊤ : Subgroup (X ⧸ pPrimeCore 2 X)), Subgroup.zpowers (QuotientGroup.mk' (pPrimeCore 2 X) t)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _), MonoidHom.map_zpowers]
  have hL : (pLayer X 2).map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤
      (⁅(⊤ : Subgroup X), Subgroup.zpowers t⁆).map (QuotientGroup.mk' (pPrimeCore 2 X)) := by
    rw [CFSG.ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient (H := X) (p := 2), hmapB]
    exact h
  have hLB : pLayer X 2 ≤ ⁅(⊤ : Subgroup X), Subgroup.zpowers t⁆ ⊔ pPrimeCore 2 X := by
    have h1 : pLayer X 2 ≤ ((⁅(⊤ : Subgroup X), Subgroup.zpowers t⁆).map (QuotientGroup.mk' (pPrimeCore 2 X))).comap
        (QuotientGroup.mk' (pPrimeCore 2 X)) :=
      (Subgroup.le_comap_map _ _).trans (Subgroup.comap_mono hL)
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  have hperf : Group.IsPerfect ↥(pLayer X 2) :=
    Subgroup.isPerfect_iff.mpr (CFSG.ComponentClassification.UnbalancedCorr.pLayer_two_isPerfect X)
  exact perfect_le_of_le_sup_solvable pPrimeCore_solvable hperf hLB

end Lift

end CFSG.GH74.GLS.Stage2.Final.L26
