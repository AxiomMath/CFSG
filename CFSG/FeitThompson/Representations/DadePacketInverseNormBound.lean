module

import CFSG.FeitThompson.Representations.NormInequalityDisjointDadeSupports
public import CFSG.FeitThompson.Definitions.DadeAveragingMap
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
public import CFSG.FeitThompson.Definitions.TotalDadeSupport

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexOrder

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {A : Set G} {H : G → Subgroup G}

theorem cfInner_self_dadeAverage_le_add_of_one_le_norm_sq (hD : IsDadeData L A H) (E : Set G)
    (χ : classFun G) (hχ : cfInner (χ : G → ℂ) (χ : G → ℂ) = 1)
    (hone : ∀ g : G, g ∉ totalDadeSupport A H ∪ E → 1 ≤ ‖(χ : G → ℂ) g‖ ^ 2) :
    cfInner (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
        (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
      ≤ (A.ncard : ℂ) / (Nat.card ↥L : ℂ) + (E.ncard : ℂ) / (Nat.card G : ℂ) := by
  classical
  set F : Finset G := (dadeCoverComplement_finite (fun _ : Unit => A) (fun _ => H)).toFinset with hF
  set Ef : Finset G := (Set.toFinite E).toFinset with hEf
  set S : ℝ := ∑ g ∈ F, ‖(χ : G → ℂ) g‖ ^ 2 with hS
  have hmemF : ∀ g : G, g ∈ F ↔ g ∉ totalDadeSupport A H := by
    intro g
    simp [hF, mem_dadeCoverComplement_iff]
  have key : (F.card : ℝ) - S ≤ (E.ncard : ℝ) := by
    have h1 : ((F \ Ef).card : ℝ) ≤ ∑ g ∈ F \ Ef, ‖(χ : G → ℂ) g‖ ^ 2 := by
      have := Finset.card_nsmul_le_sum (F \ Ef) (fun g => ‖(χ : G → ℂ) g‖ ^ 2) 1
        (fun g hg => hone g (by
          simp only [Finset.mem_sdiff, hEf, Set.Finite.mem_toFinset] at hg
          exact fun hmem => hmem.elim (fun hd => (hmemF g).1 hg.1 hd) hg.2))
      simpa using this
    have h2 : ∑ g ∈ F \ Ef, ‖(χ : G → ℂ) g‖ ^ 2 ≤ S :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun g _ _ => by positivity
    have h3 : (F.card : ℝ) ≤ ((F \ Ef).card : ℝ) + (Ef.card : ℝ) := by
      exact_mod_cast Finset.card_le_card_sdiff_add_card
    have h4 : (Ef.card : ℝ) = (E.ncard : ℝ) := by
      rw [hEf, ← Set.ncard_eq_toFinset_card E (Set.toFinite E)]
    linarith
  have hdisj : Pairwise fun i j : Unit =>
      Disjoint (totalDadeSupport ((fun _ => A) i) ((fun _ => H) i))
        (totalDadeSupport ((fun _ => A) j) ((fun _ => H) j)) := Subsingleton.pairwise
  have hcov := dadeCover_inequality (I := Unit) (L := fun _ => L) (A := fun _ => A)
    (H := fun _ => H) (fun _ => hD) hdisj χ hχ
  simp only [Finset.univ_unique, Finset.sum_singleton] at hcov
  rw [← hF, show ((dadeCoverComplement (fun _ : Unit => A) (fun _ => H)).ncard : ℂ)
      = (F.card : ℂ) by rw [hF, ← Set.ncard_eq_toFinset_card _ (dadeCoverComplement_finite _ _)],
    show ∑ g ∈ F, (‖(χ : G → ℂ) g‖ : ℂ) ^ 2 = ((S : ℝ) : ℂ) by rw [hS]; push_cast; ring] at hcov
  set X : ℂ := (((S : ℝ) : ℂ) - (F.card : ℂ)) / (Nat.card G : ℂ) with hX
  set Y : ℂ := cfInner (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
    (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G)) with hY
  set Z : ℂ := (A.ncard : ℂ) / (Nat.card ↥L : ℂ) with hZ
  have hGpos : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hfrac : -X ≤ (E.ncard : ℂ) / (Nat.card G : ℂ) := by
    have hR : ((F.card : ℝ) - S) / (Nat.card G : ℝ) ≤ (E.ncard : ℝ) / (Nat.card G : ℝ) := by
      gcongr
    calc -X = (((((F.card : ℝ) - S) / (Nat.card G : ℝ) : ℝ)) : ℂ) := by rw [hX]; push_cast; ring
      _ ≤ ((((E.ncard : ℝ) / (Nat.card G : ℝ) : ℝ)) : ℂ) := Complex.real_le_real.2 hR
      _ = (E.ncard : ℂ) / (Nat.card G : ℂ) := by push_cast; ring
  rw [show X + (Y - Z) = Y - (Z + -X) from by ring, sub_nonpos] at hcov
  exact hcov.trans (add_le_add le_rfl hfrac)

theorem cfInner_self_dadeAverage_le_of_one_le_norm_sq (hD : IsDadeData L A H) (χ : classFun G)
    (hχ : cfInner (χ : G → ℂ) (χ : G → ℂ) = 1)
    (hone : ∀ g : G, g ∉ totalDadeSupport A H → 1 ≤ ‖(χ : G → ℂ) g‖ ^ 2) :
    cfInner (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
        (fun y : ↥L => dadeAverage A H (χ : G → ℂ) (y : G))
      ≤ (A.ncard : ℂ) / (Nat.card ↥L : ℂ) := by
  have h := cfInner_self_dadeAverage_le_add_of_one_le_norm_sq hD ∅ χ hχ
    (by simpa using hone)
  simpa using h

end CFSG.FeitThompson

end
