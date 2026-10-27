module

public import CFSG.FeitThompson.Representations.InverseDadeInducedBasisExpansion
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
import Mathlib.Algebra.BigOperators.Field

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexConjugate NormalInducedSupportBasis

theorem cfInner_self_eq_sum_sum_of_eq_sum_of_ne_one {ι : Type*}
    {M : Type*} [Fintype M] [One M] (T : Finset ι) (v : ι → M → ℂ) (c n : ι → ℂ)
    (hn : ∀ i, n i ≠ 0) (hnconj : ∀ i, conj (n i) = n i)
    (hvone : ∀ i, conj (v i 1) = v i 1)
    (r : M → ℂ) (hr1 : r 1 = 0)
    (hrF : ∀ y : M, y ≠ 1 → r y = ∑ i ∈ T, conj (c i) / n i * v i y) :
    cfInner r r = ∑ i ∈ T, ∑ j ∈ T, conj (c i) * c j / (n i * n j) *
      (cfInner (v i) (v j) - v i 1 * v j 1 / (Nat.card M : ℂ)) := by
  classical
  have hcard : (Nat.card M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  set F : M → ℂ := ∑ i ∈ T, (conj (c i) / n i) • v i with hFdef
  have hFapply : ∀ y : M, F y = ∑ i ∈ T, conj (c i) / n i * v i y := by
    intro y
    rw [hFdef]
    simp [Finset.sum_apply]
  have hrF' : ∀ y : M, y ≠ 1 → r y = F y := fun y hy => by rw [hrF y hy, hFapply y]
  have key : cfInner r r = cfInner F F - F 1 * conj (F 1) / (Nat.card M : ℂ) := by
    rw [cfInner_def, cfInner_def]
    have h1 : ∑ y : M, r y * conj (r y)
        = (∑ y : M, F y * conj (F y)) - F 1 * conj (F 1) := by
      rw [← Finset.sum_erase_add Finset.univ (fun y : M => r y * conj (r y))
            (Finset.mem_univ (1 : M)),
        ← Finset.sum_erase_add Finset.univ (fun y : M => F y * conj (F y))
            (Finset.mem_univ (1 : M)), hr1,
        Finset.sum_congr rfl fun y hy => by
          rw [hrF' y (Finset.ne_of_mem_erase hy)]]
      ring
    rw [h1]
    ring
  have hFF : cfInner F F
      = ∑ i ∈ T, ∑ j ∈ T, conj (c i) * c j / (n i * n j) * cfInner (v i) (v j) := by
    rw [hFdef, cfInner_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cfInner_smul_left, cfInner_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cfInner_smul_right, map_div₀, hnconj j, Complex.conj_conj]
    have h1 := hn i
    have h2 := hn j
    field_simp
  have hF1 : F 1 = ∑ i ∈ T, conj (c i) * v i 1 / n i := by
    rw [hFapply]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hF1c : conj (F 1) = ∑ j ∈ T, c j * v j 1 / n j := by
    rw [hF1, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_div₀, map_mul, Complex.conj_conj, hvone j, hnconj j]
  have hprod : F 1 * conj (F 1) / (Nat.card M : ℂ)
      = ∑ i ∈ T, ∑ j ∈ T,
          conj (c i) * c j / (n i * n j) * (v i 1 * v j 1 / (Nat.card M : ℂ)) := by
    rw [hF1c, hF1, Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := hn i
    have h2 := hn j
    field_simp
  rw [key, hFF, hprod, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {A : Set G} {J : G → Subgroup G} {χ : G → ℂ} {N : Subgroup ↥L}

theorem cfInner_self_dadeAverage_eq_sum_sum
    [N.Normal] [Fintype (indFam N (Irr ↥N))] (hD : IsDadeData L A J)
    (hA : A = ((N.map L.subtype : Subgroup G) : Set G) \ {1})
    (hχ : χ ∈ classFun G) (ξ₀ : indFam N (Irr ↥N)) :
    cfInner (fun y : ↥L => dadeAverage A J χ (y : G))
        (fun y : ↥L => dadeAverage A J χ (y : G))
      = ∑ ξ ∈ Finset.univ.erase ξ₀, ∑ μ ∈ Finset.univ.erase ξ₀,
          conj (cfInner ((dadeMap hD (puncturedDiffDade hA ξ₀ ξ) : classFun G) : G → ℂ) χ)
              * cfInner ((dadeMap hD (puncturedDiffDade hA ξ₀ μ) : classFun G) : G → ℂ) χ
              / (cfInner (ξ : ↥L → ℂ) (ξ : ↥L → ℂ) * cfInner (μ : ↥L → ℂ) (μ : ↥L → ℂ))
            * (cfInner (ξ : ↥L → ℂ) (μ : ↥L → ℂ)
                - (ξ : ↥L → ℂ) 1 * (μ : ↥L → ℂ) 1 / (Nat.card ↥L : ℂ)) := by
  classical
  refine cfInner_self_eq_sum_sum_of_eq_sum_of_ne_one _ (fun ξ : indFam N (Irr ↥N) => (ξ : ↥L → ℂ))
    (fun ξ => cfInner ((dadeMap hD (puncturedDiffDade hA ξ₀ ξ) : classFun G) : G → ℂ) χ)
    (fun ξ => cfInner (ξ : ↥L → ℂ) (ξ : ↥L → ℂ))
    (fun ξ => cfInner_self_ne_zero_of_mem_indFam N ξ.2) (fun ξ => ?_)
    (fun ξ => conj_apply_one_of_mem_indFam N ξ.2) _ ?_ ?_
  ·
    obtain ⟨m, -, hm⟩ := exists_cfInner_self_eq_of_mem_indFam N ξ.2
    rw [hm, Complex.conj_natCast]
  ·
    exact dadeAverage_eq_zero_of_notMem fun h => hD.ne_one h rfl
  ·
    intro y hy
    by_cases hyN : y ∈ N
    · rw [dadeAverage_eq_sum_conj_cfInner_dadeMap_puncturedDiff' hD hA hχ ξ₀ hyN hy]
      exact Finset.sum_congr rfl fun ξ _ => by ring
    ·
      rw [dadeAverage_eq_zero_of_notMem
        (fun h => hyN ((coe_mem_iff_of_eq_sdiff hA y).1 h).1)]
      refine (Finset.sum_eq_zero fun ξ _ => ?_).symm
      rw [eq_zero_of_mem_indFam_of_notMem N ξ.2 hyN, mul_zero]

end CFSG.FeitThompson
