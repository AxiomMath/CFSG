module

public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreBalance
public import CFSG.LocalAnalysis.OddStandard.GH71.Basic
public import CFSG.LocalAnalysis.OddStandard.GH71.Frame

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  rw [mem_map_conj]
  constructor
  · intro hx
    have := (mem_normalizer_iff.mp hg _).mp hx
    simpa [mul_assoc] using this
  · intro hx
    have := (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_pPrimeCoreOf {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) :
    g ∈ normalizer (pPrimeCoreOf 2 H : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G),
      (pPrimeCoreOf 2 H).map (MulAut.conj g).toMonoidHom = pPrimeCoreOf 2 H := by
    intro g hg
    have := CoreAux.oddCoreOf_map_equiv (MulAut.conj g) H
    rw [map_conj_eq_of_mem_normalizer hg] at this
    exact this.symm
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← key g hg]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← key g hg] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : x = y := by
      have e : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      exact (mul_left_cancel (mul_right_cancel e)).symm
    rw [this]; exact hy

variable {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

theorem eq_one_of_mem_U_odd (h : Ctx71 G z S U u) {K : Subgroup G} (hK : Odd (Nat.card K))
    {x : G} (hxU : x ∈ U) (hxK : x ∈ K) : x = 1 := by
  by_contra hx1
  have hord : orderOf (⟨x, hxK⟩ : K) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact h.sq_eq_one_of_mem_U hxU) hx1
  have := orderOf_dvd_natCard (⟨x, hxK⟩ : K)
  rw [hord] at this
  exact (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr this)

theorem centralizer_le_normalizer' (U : Subgroup G) :
    centralizer (U : Set G) ≤ normalizer (U : Set G) := fun x hx =>
  mem_normalizer_of_conj_mem (fun y hy => by
    have e : x * y * x⁻¹ = y := by rw [(mem_centralizer_iff.mp hx y hy).symm]; group
    rw [e]; exact hy)

theorem pPrimeCoreOf_normalizer_U (h : Ctx71 G z S U u) :
    pPrimeCoreOf 2 (normalizer (U : Set G)) = pPrimeCoreOf 2 (centralizer (U : Set G)) := by
  set N := normalizer (U : Set G)
  set C := centralizer (U : Set G)
  have hCN : C ≤ N := centralizer_le_normalizer' U
  apply le_antisymm
  ·
    have hON : pPrimeCoreOf 2 N ≤ C := by
      intro o ho
      rw [mem_centralizer_iff]
      intro x hx
      have hoN : o ∈ N := pPrimeCoreOf_le' N ho
      have h1 : o * x * o⁻¹ * x⁻¹ ∈ U :=
        U.mul_mem ((mem_normalizer_iff.mp hoN x).mp hx) (U.inv_mem hx)
      have h2 : o * x * o⁻¹ * x⁻¹ ∈ pPrimeCoreOf 2 N := by
        have hxo : x * o⁻¹ * x⁻¹ ∈ pPrimeCoreOf 2 N :=
          (mem_normalizer_iff.mp (le_normalizer_pPrimeCoreOf' N (le_normalizer hx)) _).mp
            (inv_mem ho)
        have e : o * x * o⁻¹ * x⁻¹ = o * (x * o⁻¹ * x⁻¹) := by group
        rw [e]; exact mul_mem ho hxo
      have h3 := h.eq_one_of_mem_U_odd (odd_card_pPrimeCoreOf' N) h1 h2
      have : o * x = x * o := by
        calc o * x = o * x * o⁻¹ * x⁻¹ * (x * o) := by group
          _ = x * o := by rw [h3, one_mul]
      exact this.symm
    exact (le_inf le_rfl hON).trans (pPrimeCoreOf_inf_le hCN)
  · refine le_pPrimeCoreOf_of_odd ((pPrimeCoreOf_le' C).trans hCN) (odd_card_pPrimeCoreOf' C) ?_
    intro n hn
    exact mem_normalizer_pPrimeCoreOf (normalizer_le_normalizer_centralizer U hn)

end Ctx71

end CFSG.OddStandard.GH71
