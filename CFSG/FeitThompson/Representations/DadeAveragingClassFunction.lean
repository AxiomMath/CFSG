module

public import CFSG.FeitThompson.Definitions.DadeAveragingMap
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G}
  {χ : G → ℂ}

theorem dadeAverage_conj (hD : IsDadeData L A H) (hχ : χ ∈ classFun G) {l : G} (hl : l ∈ L)
    (x : G) : dadeAverage A H χ (l * x * l⁻¹) = dadeAverage A H χ x := by
  classical
  by_cases hx : x ∈ A
  · have hx' : l * x * l⁻¹ ∈ A := hD.conj_mem hx hl
    have hH : H (l * x * l⁻¹) = MulAut.conj l • H x := hD.conj_smul_H hx hl
    have hcard : (Nat.card ↥(H (l * x * l⁻¹)) : ℂ) = (Nat.card ↥(H x) : ℂ) := by
      rw [hH, IsDadeData.card_conj_smul_H (H := H) (a := x) l]
    have hsum : (∑ v : G, if v ∈ H (l * x * l⁻¹) then χ (v * (l * x * l⁻¹)) else 0)
        = ∑ u : G, if u ∈ H x then χ (u * x) else 0 := by
      rw [← Equiv.sum_comp (MulAut.conj l).toEquiv
        (fun v => if v ∈ H (l * x * l⁻¹) then χ (v * (l * x * l⁻¹)) else 0)]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hu : (MulAut.conj l).toEquiv u = l * u * l⁻¹ := rfl
      have hmem : (l * u * l⁻¹ ∈ H (l * x * l⁻¹)) ↔ u ∈ H x := by
        rw [hH, mem_conj_smul_iff, show l⁻¹ * (l * u * l⁻¹) * l = u by group]
      have hval : χ (l * u * l⁻¹ * (l * x * l⁻¹)) = χ (u * x) := by
        rw [show l * u * l⁻¹ * (l * x * l⁻¹) = l * (u * x) * l⁻¹ by group,
          classFun.apply_conj hχ]
      simp only [hu]
      by_cases h : u ∈ H x
      · rw [if_pos (hmem.2 h), if_pos h, hval]
      · rw [if_neg (fun hc => h (hmem.1 hc)), if_neg h]
    rw [dadeAverage_apply_of_mem' hx', dadeAverage_apply_of_mem' hx, hcard, hsum]
  · have hx' : l * x * l⁻¹ ∉ A := by
      intro hc
      have hback := hD.conj_mem hc (inv_mem hl)
      rw [show l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x by group] at hback
      exact hx hback
    rw [dadeAverage_eq_zero_of_notMem hx', dadeAverage_eq_zero_of_notMem hx]

theorem dadeAverage_restrict_mem_classFun (hD : IsDadeData L A H) (hχ : χ ∈ classFun G) :
    (fun y : L => dadeAverage A H χ (y : G)) ∈ classFun L := by
  rw [mem_classFun]
  intro x y h
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (dadeAverage_conj hD hχ c.2 (x : G)).symm

noncomputable def dadeAverageCF (hD : IsDadeData L A H) : classFun G →ₗ[ℂ] classFun L where
  toFun χ := ⟨fun y : L => dadeAverage A H (χ : G → ℂ) (y : G),
    dadeAverage_restrict_mem_classFun hD χ.2⟩
  map_add' χ ψ := by ext y; simp [dadeAverage_add]
  map_smul' c χ := by ext y; simp [dadeAverage_smul]

@[simp]
theorem dadeAverageCF_apply (hD : IsDadeData L A H) (χ : classFun G) (y : L) :
    (dadeAverageCF hD χ : L → ℂ) y = dadeAverage A H (χ : G → ℂ) (y : G) := (rfl)

theorem dadeAverage_one : dadeAverage A H (1 : G → ℂ) = A.indicator (1 : G → ℂ) := by
  funext x
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
    exact dadeAverage_apply_of_eq_on hx fun _ _ => rfl
  · rw [dadeAverage_eq_zero_of_notMem hx, Set.indicator_of_notMem hx]

end CFSG.FeitThompson
