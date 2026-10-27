module

public import CFSG.GH74.Tits83.DesignC.Commutator

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

section InductionB

variable {G G' : Type u} [Group G] [Group G']
variable {U : ℤ → Subgroup G} {U' : ℤ → Subgroup G'}
variable (c : OctCoord U) (c' : OctCoord U') (θ : c.K ≃+* c'.K)

theorem Delta_commutator_1_5 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 1, Delta c c' θ 5⁆ ≤ DeltaWin c c' θ 1 5 := by
  have hA : Delta c c' θ 1 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (5) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 1) (j := 5) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_1_2 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 2) (j' := 5) c c' θ (by norm_num))
    · exact (Delta_commutator_1_3 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 3) (j' := 5) c c' θ (by norm_num))
    · exact (Delta_commutator_1_4 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 4) (j' := 5) c c' θ (by norm_num))
  have hB : Delta c c' θ 5 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (5) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 1) (j := 5) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_2_5 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 2) (j := 5) c c' θ (by norm_num))
    · exact (Delta_commutator_3_5 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 3) (j := 5) c c' θ (by norm_num))
    · exact (Delta_commutator_4_5 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 4) (j := 5) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 1 5
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_2_6 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 2, Delta c c' θ 6⁆ ≤ DeltaWin c c' θ 2 6 := by
  have hA : Delta c c' θ 2 ≤
      Subgroup.normalizer (DeltaWin c c' θ 2 (6) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 2) (j := 6) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_2_3 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 3) (j' := 6) c c' θ (by norm_num))
    · exact (Delta_commutator_2_4 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 4) (j' := 6) c c' θ (by norm_num))
    · exact (Delta_commutator_2_5 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 5) (j' := 6) c c' θ (by norm_num))
  have hB : Delta c c' θ 6 ≤
      Subgroup.normalizer (DeltaWin c c' θ 2 (6) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 2) (j := 6) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_3_6 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 3) (j := 6) c c' θ (by norm_num))
    · exact (Delta_commutator_4_6 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 4) (j := 6) c c' θ (by norm_num))
    · exact (Delta_commutator_5_6 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 5) (j := 6) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 2 6
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_3_7 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 3, Delta c c' θ 7⁆ ≤ DeltaWin c c' θ 3 7 := by
  have hA : Delta c c' θ 3 ≤
      Subgroup.normalizer (DeltaWin c c' θ 3 (7) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 3) (j := 7) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_3_4 c c' θ hθ).trans
        (DeltaWin_mono (i := 3) (j := 4) (j' := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_3_5 c c' θ hθ).trans
        (DeltaWin_mono (i := 3) (j := 5) (j' := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_3_6 c c' θ hθ).trans
        (DeltaWin_mono (i := 3) (j := 6) (j' := 7) c c' θ (by norm_num))
  have hB : Delta c c' θ 7 ≤
      Subgroup.normalizer (DeltaWin c c' θ 3 (7) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 3) (j := 7) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_4_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 3) (i' := 4) (j := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_5_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 3) (i' := 5) (j := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_6_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 3) (i' := 6) (j := 7) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 3 7
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_4_8 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 4, Delta c c' θ 8⁆ ≤ DeltaWin c c' θ 4 8 := by
  have hA : Delta c c' θ 4 ≤
      Subgroup.normalizer (DeltaWin c c' θ 4 (8) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 4) (j := 8) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_4_5 c c' θ hθ).trans
        (DeltaWin_mono (i := 4) (j := 5) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_4_6 c c' θ hθ).trans
        (DeltaWin_mono (i := 4) (j := 6) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_4_7 c c' θ hθ).trans
        (DeltaWin_mono (i := 4) (j := 7) (j' := 8) c c' θ (by norm_num))
  have hB : Delta c c' θ 8 ≤
      Subgroup.normalizer (DeltaWin c c' θ 4 (8) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 4) (j := 8) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_5_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 4) (i' := 5) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_6_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 4) (i' := 6) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_7_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 4) (i' := 7) (j := 8) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 4 8
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_1_6 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 1, Delta c c' θ 6⁆ ≤ DeltaWin c c' θ 1 6 := by
  have hA : Delta c c' θ 1 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (6) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 1) (j := 6) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_1_2 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 2) (j' := 6) c c' θ (by norm_num))
    · exact (Delta_commutator_1_3 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 3) (j' := 6) c c' θ (by norm_num))
    · exact (Delta_commutator_1_4 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 4) (j' := 6) c c' θ (by norm_num))
    · exact (Delta_commutator_1_5 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 5) (j' := 6) c c' θ (by norm_num))
  have hB : Delta c c' θ 6 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (6) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 1) (j := 6) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_2_6 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 2) (j := 6) c c' θ (by norm_num))
    · exact (Delta_commutator_3_6 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 3) (j := 6) c c' θ (by norm_num))
    · exact (Delta_commutator_4_6 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 4) (j := 6) c c' θ (by norm_num))
    · exact (Delta_commutator_5_6 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 5) (j := 6) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 1 6
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_2_7 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 2, Delta c c' θ 7⁆ ≤ DeltaWin c c' θ 2 7 := by
  have hA : Delta c c' θ 2 ≤
      Subgroup.normalizer (DeltaWin c c' θ 2 (7) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 2) (j := 7) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_2_3 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 3) (j' := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_2_4 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 4) (j' := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_2_5 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 5) (j' := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_2_6 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 6) (j' := 7) c c' θ (by norm_num))
  have hB : Delta c c' θ 7 ≤
      Subgroup.normalizer (DeltaWin c c' θ 2 (7) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 2) (j := 7) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_3_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 3) (j := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_4_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 4) (j := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_5_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 5) (j := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_6_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 6) (j := 7) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 2 7
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_3_8 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 3, Delta c c' θ 8⁆ ≤ DeltaWin c c' θ 3 8 := by
  have hA : Delta c c' θ 3 ≤
      Subgroup.normalizer (DeltaWin c c' θ 3 (8) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 3) (j := 8) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_3_4 c c' θ hθ).trans
        (DeltaWin_mono (i := 3) (j := 4) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_3_5 c c' θ hθ).trans
        (DeltaWin_mono (i := 3) (j := 5) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_3_6 c c' θ hθ).trans
        (DeltaWin_mono (i := 3) (j := 6) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_3_7 c c' θ hθ).trans
        (DeltaWin_mono (i := 3) (j := 7) (j' := 8) c c' θ (by norm_num))
  have hB : Delta c c' θ 8 ≤
      Subgroup.normalizer (DeltaWin c c' θ 3 (8) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 3) (j := 8) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_4_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 3) (i' := 4) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_5_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 3) (i' := 5) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_6_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 3) (i' := 6) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_7_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 3) (i' := 7) (j := 8) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 3 8
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_1_7 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 1, Delta c c' θ 7⁆ ≤ DeltaWin c c' θ 1 7 := by
  have hA : Delta c c' θ 1 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (7) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 1) (j := 7) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_1_2 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 2) (j' := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_1_3 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 3) (j' := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_1_4 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 4) (j' := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_1_5 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 5) (j' := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_1_6 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 6) (j' := 7) c c' θ (by norm_num))
  have hB : Delta c c' θ 7 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (7) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 1) (j := 7) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_2_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 2) (j := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_3_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 3) (j := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_4_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 4) (j := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_5_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 5) (j := 7) c c' θ (by norm_num))
    · exact (Delta_commutator_6_7 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 6) (j := 7) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 1 7
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_2_8 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 2, Delta c c' θ 8⁆ ≤ DeltaWin c c' θ 2 8 := by
  have hA : Delta c c' θ 2 ≤
      Subgroup.normalizer (DeltaWin c c' θ 2 (8) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 2) (j := 8) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_2_3 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 3) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_2_4 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 4) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_2_5 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 5) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_2_6 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 6) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_2_7 c c' θ hθ).trans
        (DeltaWin_mono (i := 2) (j := 7) (j' := 8) c c' θ (by norm_num))
  have hB : Delta c c' θ 8 ≤
      Subgroup.normalizer (DeltaWin c c' θ 2 (8) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 2) (j := 8) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_3_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 3) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_4_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 4) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_5_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 5) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_6_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 6) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_7_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 2) (i' := 7) (j := 8) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 2 8
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_1_8 (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) :
    ⁅Delta c c' θ 1, Delta c c' θ 8⁆ ≤ DeltaWin c c' θ 1 8 := by
  have hA : Delta c c' θ 1 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (8) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin (i := 1) (j := 8) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_1_2 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 2) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_1_3 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 3) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_1_4 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 4) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_1_5 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 5) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_1_6 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 6) (j' := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_1_7 c c' θ hθ).trans
        (DeltaWin_mono (i := 1) (j := 7) (j' := 8) c c' θ (by norm_num))
  have hB : Delta c c' θ 8 ≤
      Subgroup.normalizer (DeltaWin c c' θ 1 (8) : Set (G × G')) := by
    refine Delta_le_normalizer_DeltaWin_right (i := 1) (j := 8) c c' θ fun k hk => ?_
    have hk1 := (mem_intList_iff.1 hk).1
    have hk2 := (mem_intList_iff.1 hk).2
    interval_cases k
    · exact (Delta_commutator_2_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 2) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_3_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 3) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_4_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 4) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_5_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 5) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_6_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 6) (j := 8) c c' θ (by norm_num))
    · exact (Delta_commutator_7_8 c c' θ hθ).trans
        (DeltaWin_mono_left (i := 1) (i' := 7) (j := 8) c c' θ (by norm_num))
  exact TauCeti.commutator_closure_closure_le hA hB
    (fun x hx y hy => gen_commutator_mem c c' θ hθ 1 8
      (by norm_num) (by norm_num) (by norm_num) hx hy)

theorem Delta_commutator_le (hθ : ∀ t, θ (c.σ t) = c'.σ (θ t)) (i j : ℤ)
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ 8) :
    ⁅Delta c c' θ i, Delta c c' θ j⁆ ≤ DeltaWin c c' θ i j := by
  have hi8 : i ≤ 8 := by omega
  interval_cases i
  · interval_cases j
    · exact Delta_commutator_1_2 c c' θ hθ
    · exact Delta_commutator_1_3 c c' θ hθ
    · exact Delta_commutator_1_4 c c' θ hθ
    · exact Delta_commutator_1_5 c c' θ hθ
    · exact Delta_commutator_1_6 c c' θ hθ
    · exact Delta_commutator_1_7 c c' θ hθ
    · exact Delta_commutator_1_8 c c' θ hθ
  · interval_cases j
    · exact Delta_commutator_2_3 c c' θ hθ
    · exact Delta_commutator_2_4 c c' θ hθ
    · exact Delta_commutator_2_5 c c' θ hθ
    · exact Delta_commutator_2_6 c c' θ hθ
    · exact Delta_commutator_2_7 c c' θ hθ
    · exact Delta_commutator_2_8 c c' θ hθ
  · interval_cases j
    · exact Delta_commutator_3_4 c c' θ hθ
    · exact Delta_commutator_3_5 c c' θ hθ
    · exact Delta_commutator_3_6 c c' θ hθ
    · exact Delta_commutator_3_7 c c' θ hθ
    · exact Delta_commutator_3_8 c c' θ hθ
  · interval_cases j
    · exact Delta_commutator_4_5 c c' θ hθ
    · exact Delta_commutator_4_6 c c' θ hθ
    · exact Delta_commutator_4_7 c c' θ hθ
    · exact Delta_commutator_4_8 c c' θ hθ
  · interval_cases j
    · exact Delta_commutator_5_6 c c' θ hθ
    · exact Delta_commutator_5_7 c c' θ hθ
    · exact Delta_commutator_5_8 c c' θ hθ
  · interval_cases j
    · exact Delta_commutator_6_7 c c' θ hθ
    · exact Delta_commutator_6_8 c c' θ hθ
  · interval_cases j
    · exact Delta_commutator_7_8 c c' θ hθ
  · exfalso; omega


end InductionB

end CFSG.GH74.Tits83
