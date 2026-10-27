module

public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
import all CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOrthogonalAbelianization

public noncomputable section

open Matrix QuadraticMap
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open scoped commutatorElement

namespace CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private def frameU1 (F : FrameData Q) : Submodule K V :=
  Submodule.span K (Set.range (fun i : Fin 2 => if i = 0 then F.e 0 else F.e 1))

private def frameU2 (F : FrameData Q) : Submodule K V :=
  Submodule.span K (Set.range (fun i : Fin 2 => if i = 0 then F.e 2 else F.e 3))

def frameW1 (F : FrameData Q) : Submodule K V :=
  Submodule.span K (Set.range (fun i : Fin 3 =>
    if i = 0 then F.e 0 else if i = 1 then F.e 1 else F.e 4))

def frameW2 (F : FrameData Q) : Submodule K V :=
  Submodule.span K (Set.range (fun i : Fin 3 =>
    if i = 0 then F.e 2 else if i = 1 then F.e 3 else F.e 4))

variable (F : FrameData Q)

private theorem frameU1_e0_mem : F.e 0 ∈ frameU1 F :=
  Submodule.subset_span ⟨0, by simp⟩

private theorem frameU1_e1_mem : F.e 1 ∈ frameU1 F :=
  Submodule.subset_span ⟨1, by simp⟩

private theorem frameU2_e2_mem : F.e 2 ∈ frameU2 F :=
  Submodule.subset_span ⟨0, by simp⟩

private theorem frameU2_e3_mem : F.e 3 ∈ frameU2 F :=
  Submodule.subset_span ⟨1, by simp⟩

private theorem frameW1_e0_mem : F.e 0 ∈ frameW1 F :=
  Submodule.subset_span ⟨0, by simp⟩

private theorem frameW1_e1_mem : F.e 1 ∈ frameW1 F :=
  Submodule.subset_span ⟨1, by simp⟩

private theorem frameW1_e4_mem : F.e 4 ∈ frameW1 F :=
  Submodule.subset_span ⟨2, by simp⟩

private theorem frameW2_e2_mem : F.e 2 ∈ frameW2 F :=
  Submodule.subset_span ⟨0, by simp⟩

private theorem frameW2_e3_mem : F.e 3 ∈ frameW2 F :=
  Submodule.subset_span ⟨1, by simp⟩

private theorem frameW2_e4_mem : F.e 4 ∈ frameW2 F :=
  Submodule.subset_span ⟨2, by simp⟩

private theorem frameU1_le_frameW1 : frameU1 F ≤ frameW1 F := by
  rw [frameU1, frameW1, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact frameW1_e0_mem F
  · exact frameW1_e1_mem F

private theorem frameU2_le_frameW2 : frameU2 F ≤ frameW2 F := by
  rw [frameU2, frameW2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact frameW2_e2_mem F
  · exact frameW2_e3_mem F

private theorem span_e4_le_frameW1 : Submodule.span K {F.e 4} ≤ frameW1 F :=
  Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (frameW1_e4_mem F))

private theorem span_e4_le_frameW2 : Submodule.span K {F.e 4} ≤ frameW2 F :=
  Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (frameW2_e4_mem F))

private theorem frameW1_eq_sup : frameW1 F = frameU1 F ⊔ Submodule.span K {F.e 4} := by
  apply le_antisymm
  · rw [frameW1, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.mem_sup_left (frameU1_e0_mem F)
    · exact Submodule.mem_sup_left (frameU1_e1_mem F)
    · exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  · exact sup_le (frameU1_le_frameW1 F) (span_e4_le_frameW1 F)

private theorem frameW2_eq_sup : frameW2 F = frameU2 F ⊔ Submodule.span K {F.e 4} := by
  apply le_antisymm
  · rw [frameW2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.mem_sup_left (frameU2_e2_mem F)
    · exact Submodule.mem_sup_left (frameU2_e3_mem F)
    · exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  · exact sup_le (frameU2_le_frameW2 F) (span_e4_le_frameW2 F)

private theorem t_fixes_frameW2 (F : FrameData Q) {v : V} (hv : v ∈ frameW2 F) :
    F.t v = v := by
  rw [frameW2] at hv
  refine Submodule.span_induction (p := fun x _ => F.t x = x) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp
  · simp
  · intro a b ha hb hta htb
    rw [map_add, hta, htb]
  · intro c a ha hta
    rw [map_smul, hta]

private theorem t_negates_frameU1 (F : FrameData Q) {u : V} (hu : u ∈ frameU1 F) :
    F.t u = -u := by
  rw [frameU1] at hu
  refine Submodule.span_induction (p := fun x _ => F.t x = -x) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp
  · simp
  · intro a b ha hb hta htb
    rw [map_add, hta, htb, neg_add]
  · intro c a ha hta
    rw [map_smul, hta, smul_neg]

private theorem polar_frameU1_frameU2 {u₁ : V} (hu₁ : u₁ ∈ frameU1 F) {u₂ : V}
    (hu₂ : u₂ ∈ frameU2 F) : polar Q u₁ u₂ = 0 := by
  have h : ∀ x ∈ frameU1 F, ∀ y ∈ frameU2 F, polar Q x y = 0 := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => ∀ y ∈ frameU2 F, polar Q x y = 0)
      ?_ ?_ ?_ ?_ hx
    · intro x hx y hy
      obtain ⟨i, rfl⟩ := hx
      refine Submodule.span_induction (p := fun z _ => polar Q _ z = 0) ?_ ?_ ?_ ?_ hy
      · intro z hz
        obtain ⟨j, rfl⟩ := hz
        fin_cases i <;> fin_cases j <;>
          simp [F.orth 0 1 (by norm_num), F.orth 0 2 (by norm_num),
            F.orth 0 3 (by norm_num), F.orth 1 0 (by norm_num),
            F.orth 1 2 (by norm_num), F.orth 1 3 (by norm_num),
            F.orth 2 0 (by norm_num), F.orth 2 1 (by norm_num),
            F.orth 3 0 (by norm_num), F.orth 3 1 (by norm_num)]
      · simp
      · intro a b _ _ ha hb
        rw [polar_add_right, ha, hb, add_zero]
      · intro c a _ ha
        rw [polar_smul_right, ha, smul_zero]
    · intro y _; simp
    · intro a b _ _ ha hb y hy
      rw [polar_add_left, ha y hy, hb y hy, add_zero]
    · intro c a _ ha y hy
      rw [polar_smul_left, ha y hy, smul_zero]
  exact h u₁ hu₁ u₂ hu₂

private theorem polar_frameU1_e4 {u : V} (hu : u ∈ frameU1 F) : polar Q u (F.e 4) = 0 := by
  refine Submodule.span_induction (p := fun x _ => polar Q x (F.e 4) = 0) ?_ ?_ ?_ ?_ hu
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    fin_cases i <;>
      simp [F.orth 0 4 (by norm_num), F.orth 1 4 (by norm_num)]
  · simp
  · intro a b _ _ ha hb
    rw [polar_add_left, ha, hb, add_zero]
  · intro c a _ ha
    rw [polar_smul_left, ha, smul_zero]

private theorem polar_frameU2_e4 {u : V} (hu : u ∈ frameU2 F) : polar Q u (F.e 4) = 0 := by
  refine Submodule.span_induction (p := fun x _ => polar Q x (F.e 4) = 0) ?_ ?_ ?_ ?_ hu
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    fin_cases i <;>
      simp [F.orth 2 4 (by norm_num), F.orth 3 4 (by norm_num)]
  · simp
  · intro a b _ _ ha hb
    rw [polar_add_left, ha, hb, add_zero]
  · intro c a _ ha
    rw [polar_smul_left, ha, smul_zero]

private theorem frameU2_le_orthPerp_frameW1 :
    frameU2 F ≤ CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameW1 F) := by
  intro u₂ hu₂
  rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp]
  intro w hw
  refine Submodule.span_induction (p := fun x _ => polar Q x u₂ = 0) ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    fin_cases i
    · simpa using polar_frameU1_frameU2 F (frameU1_e0_mem F) hu₂
    · simpa using polar_frameU1_frameU2 F (frameU1_e1_mem F) hu₂
    · simpa [polar_comm] using polar_frameU2_e4 F hu₂
  · simp
  · intro a b _ _ ha hb
    rw [polar_add_left, ha, hb, add_zero]
  · intro c a _ ha
    rw [polar_smul_left, ha, smul_zero]

private theorem frameU1_le_orthPerp_frameW2 :
    frameU1 F ≤ CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameW2 F) := by
  intro u₁ hu₁
  rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp]
  intro w hw
  refine Submodule.span_induction (p := fun x _ => polar Q x u₁ = 0) ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    fin_cases i
    · simpa [polar_comm] using polar_frameU1_frameU2 F hu₁ (frameU2_e2_mem F)
    · simpa [polar_comm] using polar_frameU1_frameU2 F hu₁ (frameU2_e3_mem F)
    · simpa [polar_comm] using polar_frameU1_e4 F hu₁
  · simp
  · intro a b _ _ ha hb
    rw [polar_add_left, ha, hb, add_zero]
  · intro c a _ ha
    rw [polar_smul_left, ha, smul_zero]

private theorem frameW2_le_orthPerp_frameU1 :
    frameW2 F ≤ CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameU1 F) := by
  intro w hw
  rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp]
  intro u hu
  rw [polar_comm]
  exact (CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp.mp
    (frameU1_le_orthPerp_frameW2 F hu)) w hw

private theorem frameW1_le_orthPerp_frameU2 :
    frameW1 F ≤ CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameU2 F) := by
  intro w hw
  rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp]
  intro u hu
  rw [polar_comm]
  exact (CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp.mp
    (frameU2_le_orthPerp_frameW1 F hu)) w hw

private theorem frameU1_polar_nondegenerate :
    (Q.comp (frameU1 F).subtype).polarBilin.Nondegenerate := by
  rw [CFSG.RankThree.PartOne.KCOrthogonal.polarBilin_comp_subtype]
  refine (CFSG.RankThree.Classical.nondegenerate_restrict_span F.two_ne_zero Q
    (f := fun i : Fin 2 => if i = 0 then F.e 0 else F.e 1) ?_ ?_).2
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [F.orth 0 1 (by norm_num), F.orth 1 0 (by norm_num)]
  · intro i
    fin_cases i <;> simp [F.norm]

private theorem frameU2_polar_nondegenerate :
    (Q.comp (frameU2 F).subtype).polarBilin.Nondegenerate := by
  rw [CFSG.RankThree.PartOne.KCOrthogonal.polarBilin_comp_subtype]
  refine (CFSG.RankThree.Classical.nondegenerate_restrict_span F.two_ne_zero Q
    (f := fun i : Fin 2 => if i = 0 then F.e 2 else F.e 3) ?_ ?_).2
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [F.orth 2 3 (by norm_num), F.orth 3 2 (by norm_num)]
  · intro i
    fin_cases i <;> simp [F.norm]

private theorem frameW1_polar_nondegenerate :
    (Q.comp (frameW1 F).subtype).polarBilin.Nondegenerate := by
  rw [CFSG.RankThree.PartOne.KCOrthogonal.polarBilin_comp_subtype]
  refine (CFSG.RankThree.Classical.nondegenerate_restrict_span F.two_ne_zero Q
    (f := fun i : Fin 3 => if i = 0 then F.e 0 else if i = 1 then F.e 1 else F.e 4)
    ?_ ?_).2
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [F.orth 0 1 (by norm_num), F.orth 0 4 (by norm_num),
        F.orth 1 0 (by norm_num), F.orth 1 4 (by norm_num),
        F.orth 4 0 (by norm_num), F.orth 4 1 (by norm_num)]
  · intro i
    fin_cases i <;> simp [F.norm, F.last]

private theorem frameW2_polar_nondegenerate :
    (Q.comp (frameW2 F).subtype).polarBilin.Nondegenerate := by
  rw [CFSG.RankThree.PartOne.KCOrthogonal.polarBilin_comp_subtype]
  refine (CFSG.RankThree.Classical.nondegenerate_restrict_span F.two_ne_zero Q
    (f := fun i : Fin 3 => if i = 0 then F.e 2 else if i = 1 then F.e 3 else F.e 4)
    ?_ ?_).2
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [F.orth 2 3 (by norm_num), F.orth 2 4 (by norm_num),
        F.orth 3 2 (by norm_num), F.orth 3 4 (by norm_num),
        F.orth 4 2 (by norm_num), F.orth 4 3 (by norm_num)]
  · intro i
    fin_cases i <;> simp [F.norm, F.last]

private theorem frameU1_isCompl :
    IsCompl (frameU1 F)
      (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameU1 F)) :=
  CFSG.RankThree.PartOne.KCOrthogonal.isCompl_orthPerp (frameU1_polar_nondegenerate F)

private theorem frameU2_isCompl :
    IsCompl (frameU2 F)
      (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameU2 F)) :=
  CFSG.RankThree.PartOne.KCOrthogonal.isCompl_orthPerp (frameU2_polar_nondegenerate F)

private theorem frameW1_isCompl :
    IsCompl (frameW1 F)
      (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameW1 F)) :=
  CFSG.RankThree.PartOne.KCOrthogonal.isCompl_orthPerp (frameW1_polar_nondegenerate F)

private theorem frameW2_isCompl :
    IsCompl (frameW2 F)
      (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameW2 F)) :=
  CFSG.RankThree.PartOne.KCOrthogonal.isCompl_orthPerp (frameW2_polar_nondegenerate F)

private theorem sq_roots_card_le_two [Fintype K] [DecidableEq K] (d : K) :
    (Finset.univ.filter (fun t : K => t ^ 2 = d)).card ≤ 2 := by
  classical
  by_cases h : ∃ t : K, t ^ 2 = d
  · obtain ⟨t0, ht0⟩ := h
    have hsub : Finset.univ.filter (fun t : K => t ^ 2 = d) ⊆ {t0, -t0} := by
      intro t ht
      rw [Finset.mem_filter] at ht
      have hzero : (t - t0) * (t + t0) = 0 := by
        linear_combination ht.2 - ht0
      rcases mul_eq_zero.mp hzero with h1 | h1
      · rw [Finset.mem_insert, Finset.mem_singleton]
        left
        linear_combination h1
      · rw [Finset.mem_insert, Finset.mem_singleton]
        right
        linear_combination h1
    calc (Finset.univ.filter (fun t : K => t ^ 2 = d)).card ≤ ({t0, -t0} : Finset K).card :=
          Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  · have hempty : Finset.univ.filter (fun t : K => t ^ 2 = d) = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨t, ht⟩
      exact h ⟨t, (Finset.mem_filter.mp ht).2⟩
    rw [hempty]
    simp

private theorem not_both_sq_neg_one [Fintype K] [DecidableEq K] {c : K} (hc : c ≠ 0)
    (hneg : ¬ IsSquare (-1 : K)) :
    (Finset.univ.filter (fun t : K => t ^ 2 = c) = ∅) ∨
      (Finset.univ.filter (fun t : K => t ^ 2 = -c) = ∅) := by
  classical
  by_contra h
  push Not at h
  obtain ⟨t1, ht1⟩ := h.1
  obtain ⟨t2, ht2⟩ := h.2
  have ht1' : t1 ^ 2 = c := (Finset.mem_filter.mp ht1).2
  have ht2' : t2 ^ 2 = -c := (Finset.mem_filter.mp ht2).2
  have ht1ne : t1 ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at ht1'
    exact hc ht1'.symm
  apply hneg
  refine ⟨t2 / t1, ?_⟩
  field_simp [ht1ne]
  rw [ht1', ht2']

private theorem exists_scalar_choice_aux [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (hq5 : 5 ≤ Nat.card K) (c : K) :
    ∃ a b : K, b ^ 2 - a ^ 2 = c ∧ b ≠ 0 ∧ (a ≠ 0 ∨ IsSquare (-1 : K)) := by
  classical
  have hfive : 5 ≤ Fintype.card K := by simpa [Nat.card_eq_fintype_card] using hq5
  by_cases hc : c = 0
  · refine ⟨1, 1, ?_, one_ne_zero, Or.inl one_ne_zero⟩
    simp [hc]
  · by_cases hneg : IsSquare (-1 : K)
    · let bad : Finset K := {0} ∪ Finset.univ.filter (fun t : K => t ^ 2 = -c)
      have hbad : bad.card ≤ 3 := by
        calc bad.card ≤ ({0} : Finset K).card +
              (Finset.univ.filter (fun t : K => t ^ 2 = -c)).card := Finset.card_union_le _ _
          _ ≤ 1 + 2 := by
            gcongr
            · simp
            · exact sq_roots_card_le_two (-c)
          _ = 3 := by norm_num
      have hlt : bad.card < (Finset.univ : Finset K).card := by
        rw [Finset.card_univ]
        omega
      obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      have ht0 : t ≠ 0 := by
        intro h
        exact ht (by simp [bad, h])
      have htneg : t ^ 2 ≠ -c := by
        intro h
        exact ht (by simp [bad, h])
      let a : K := (t - c / t) / 2
      let b : K := (t + c / t) / 2
      refine ⟨a, b, ?_, ?_, Or.inr hneg⟩
      · dsimp [a, b]
        field_simp [ht0]
        ring
      · have hbne : t + c / t ≠ 0 := by
          intro hsum
          have hsq : t ^ 2 = -c := by
            field_simp [ht0] at hsum
            linear_combination hsum
          exact htneg hsq
        simpa [b] using div_ne_zero hbne h2
    · let bad : Finset K := ({0} ∪ Finset.univ.filter (fun t : K => t ^ 2 = c)) ∪
          Finset.univ.filter (fun t : K => t ^ 2 = -c)
      have hbad : bad.card ≤ 3 := by
        rcases not_both_sq_neg_one hc hneg with hc0 | hc0
        · have h2' : (Finset.univ.filter (fun t : K => t ^ 2 = c)).card = 0 := by
            rw [hc0]; simp
          have h1 : (({0} : Finset K) ∪
              Finset.univ.filter (fun t : K => t ^ 2 = c)).card ≤
              ({0} : Finset K).card +
                (Finset.univ.filter (fun t : K => t ^ 2 = c)).card :=
            Finset.card_union_le _ _
          have h3 : (Finset.univ.filter (fun t : K => t ^ 2 = -c)).card ≤ 2 :=
            sq_roots_card_le_two (-c)
          calc bad.card ≤ (({0} : Finset K) ∪
                Finset.univ.filter (fun t : K => t ^ 2 = c)).card +
                (Finset.univ.filter (fun t : K => t ^ 2 = -c)).card :=
                  Finset.card_union_le _ _
            _ ≤ (({0} : Finset K).card + 0) + 2 := by
                  have h0 : ({0} : Finset K).card = 1 := Finset.card_singleton 0
                  omega
            _ = 3 := by norm_num
        · have h2' : (Finset.univ.filter (fun t : K => t ^ 2 = -c)).card = 0 := by
            rw [hc0]; simp
          have h1 : (({0} : Finset K) ∪
              Finset.univ.filter (fun t : K => t ^ 2 = c)).card ≤
              ({0} : Finset K).card +
                (Finset.univ.filter (fun t : K => t ^ 2 = c)).card :=
            Finset.card_union_le _ _
          have h3 : (Finset.univ.filter (fun t : K => t ^ 2 = c)).card ≤ 2 :=
            sq_roots_card_le_two c
          calc bad.card ≤ (({0} : Finset K) ∪
                Finset.univ.filter (fun t : K => t ^ 2 = c)).card +
                (Finset.univ.filter (fun t : K => t ^ 2 = -c)).card :=
                  Finset.card_union_le _ _
            _ = (({0} : Finset K) ∪
                Finset.univ.filter (fun t : K => t ^ 2 = c)).card + 0 := by rw [h2']
            _ ≤ (({0} : Finset K).card +
                (Finset.univ.filter (fun t : K => t ^ 2 = c)).card) + 0 := by
                  simpa using h1
            _ ≤ 1 + 2 + 0 := by
                  have h0 : ({0} : Finset K).card = 1 := Finset.card_singleton 0
                  omega
            _ = 3 := by norm_num
      have hlt : bad.card < (Finset.univ : Finset K).card := by
        rw [Finset.card_univ]
        omega
      obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      have ht0 : t ≠ 0 := by
        intro h
        exact ht (by simp [bad, h])
      have htc : t ^ 2 ≠ c := by
        intro h
        exact ht (by simp [bad, h])
      have htneg : t ^ 2 ≠ -c := by
        intro h
        exact ht (by simp [bad, h])
      let a : K := (t - c / t) / 2
      let b : K := (t + c / t) / 2
      refine ⟨a, b, ?_, ?_, Or.inl ?_⟩
      · dsimp [a, b]
        field_simp [ht0]
        ring
      · have hbne : t + c / t ≠ 0 := by
          intro hsum
          have hsq : t ^ 2 = -c := by
            field_simp [ht0] at hsum
            linear_combination hsum
          exact htneg hsq
        simpa [b] using div_ne_zero hbne h2
      · intro ha0
        have hdiff : t - c / t = 0 := by
          have h := ha0
          dsimp [a] at h
          by_contra hne
          exact (div_ne_zero hne h2) h
        have hsq : t ^ 2 = c := by
          field_simp [ht0] at hdiff
          linear_combination hdiff
        exact htc hsq

private theorem exists_scalar_choice [Finite K] (h2 : (2 : K) ≠ 0)
    (hq5 : 5 ≤ Nat.card K) (c : K) :
    ∃ a b : K, b ^ 2 - a ^ 2 = c ∧ b ≠ 0 ∧ (a ≠ 0 ∨ IsSquare (-1 : K)) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  exact exists_scalar_choice_aux h2 hq5 c

private theorem mem_map_extendHom_of_preserves {R : Submodule K V}
    (hR : IsCompl R (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q R))
    {b : V ≃ₗ[K] V} (hbO : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hbR : ∀ r ∈ R, b r ∈ R)
    (hbP : ∀ w ∈ CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q R, b w = w) :
    b ∈ Subgroup.map (CFSG.RankThree.PartOne.KCOrthogonal.extendHom hR)
      (⊤ : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype))) := by
  let f : R →ₗ[K] R := LinearMap.restrict (b : V →ₗ[K] V) hbR
  have hf_inj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact b.injective (congrArg Subtype.val h)
  have hf_surj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (rfl : Module.finrank K R =
      Module.finrank K R)).mp hf_inj
  let g : R ≃ₗ[K] R := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hgapply : ∀ r : R, ((g r : R) : V) = b (r : V) := by
    intro r
    change ((f r : R) : V) = b (r : V)
    rfl
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro r
    change Q ((g r : R) : V) = Q (r : V)
    rw [hgapply r]
    exact map_of_mem hbO (r : V)
  let gO : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype)) := ⟨g, hgO⟩
  refine Subgroup.mem_map.mpr ⟨gO, Subgroup.mem_top gO, ?_⟩
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, w, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_add_of_isCompl hR v
  calc CFSG.RankThree.PartOne.KCOrthogonal.extendHom hR gO ((u : V) + w)
      = (((gO : R ≃ₗ[K] R) u : R) : V) + w :=
        CFSG.RankThree.PartOne.KCOrthogonal.extendHom_apply hR gO u w
    _ = ((g u : R) : V) + w := rfl
    _ = b ((u : V) + w) := by rw [map_add, hgapply u, hbP w w.2]

private noncomputable def orthImage {R : Submodule K V}
    (hR : IsCompl R (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q R)) :
    Subgroup (V ≃ₗ[K] V) :=
  (TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype)).map
    (CFSG.LocalAnalysis.ComponentInitial.orthExtend hR)

private theorem mem_orthImage {R : Submodule K V}
    {hR : IsCompl R (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q R)} {b : V ≃ₗ[K] V} :
    b ∈ orthImage hR ↔ ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype),
      CFSG.LocalAnalysis.ComponentInitial.orthExtend hR g = b :=
  Iff.rfl

private theorem orthImage_extendHom {R : Submodule K V}
    {hR : IsCompl R (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q R)}
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype))) :
    CFSG.RankThree.PartOne.KCOrthogonal.extendHom hR g ∈ orthImage hR :=
  ⟨g, g.2, rfl⟩

private theorem map_extendHom_top {R : Submodule K V}
    (hR : IsCompl R (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q R)) :
    Subgroup.map (CFSG.RankThree.PartOne.KCOrthogonal.extendHom hR)
      (⊤ : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype))) =
      orthImage hR := by
  rw [show CFSG.RankThree.PartOne.KCOrthogonal.extendHom hR =
    (CFSG.LocalAnalysis.ComponentInitial.orthExtend hR).comp
      (TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype)).subtype from rfl]
  rw [orthImage, ← Subgroup.map_map]
  congr 1
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

private theorem orthImage_le_orthogonalGroup {R : Submodule K V}
    {hR : IsCompl R (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q R)} :
    orthImage hR ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rintro b ⟨g, hg, rfl⟩
  exact (CFSG.LocalAnalysis.ComponentInitial.orthogonal_complement_elementary_embedding Q hR
    CFSG.RankThree.PartOne.KCOrthogonal.orth_orthPerp).2.1 g hg

private theorem orthImage_fix {R : Submodule K V}
    {hR : IsCompl R (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q R)} {b : V ≃ₗ[K] V}
    (hb : b ∈ orthImage hR) {w : V}
    (hw : w ∈ CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q R) : b w = w := by
  obtain ⟨g, hg, rfl⟩ := mem_orthImage.mp hb
  rw [show CFSG.LocalAnalysis.ComponentInitial.orthExtend hR g =
    CFSG.RankThree.PartOne.KCOrthogonal.extendHom hR ⟨g, hg⟩ from rfl,
    CFSG.RankThree.PartOne.KCOrthogonal.extendHom_fix hR ⟨g, hg⟩ hw]

private theorem orthImage_maps {R : Submodule K V}
    {hR : IsCompl R (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q R)} {b : V ≃ₗ[K] V}
    (hb : b ∈ orthImage hR) {r : V} (hr : r ∈ R) : b r ∈ R := by
  obtain ⟨g, hg, rfl⟩ := mem_orthImage.mp hb
  rw [show CFSG.LocalAnalysis.ComponentInitial.orthExtend hR g =
    CFSG.RankThree.PartOne.KCOrthogonal.extendHom hR ⟨g, hg⟩ from rfl,
    CFSG.RankThree.PartOne.KCOrthogonal.extendHom_apply_mem hR ⟨g, hg⟩ ⟨r, hr⟩]
  simpa using (g ⟨r, hr⟩).2

private theorem orthDerived_le_orthogonalGroup (R : Submodule K V) :
    CFSG.RankThree.Classical2.orthDerived (Q.comp R.subtype) ≤
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype) := by
  rw [CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_eq_map_commutator]
  rintro x ⟨y, -, rfl⟩
  exact y.2

private theorem supportedOrthDerived_le_orthImage {R : Submodule K V}
    (hR : IsCompl R (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q R)) :
    CFSG.RankThree.PartOne.KCOrthogonal.supportedOrthDerived Q R ≤ orthImage hR := by
  rw [CFSG.RankThree.PartOne.KCOrthogonal.supportedOrthDerived_eq_map hR]
  exact Subgroup.map_mono (orthDerived_le_orthogonalGroup R)

private theorem commutator_orthImage_eq_supported {R : Submodule K V}
    (hR : IsCompl R (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q R)) :
    ⁅orthImage hR, orthImage hR⁆ =
      CFSG.RankThree.PartOne.KCOrthogonal.supportedOrthDerived Q R := by
  rw [orthImage, ← Subgroup.map_commutator]
  change Subgroup.map (CFSG.LocalAnalysis.ComponentInitial.orthExtend hR)
    (CFSG.RankThree.Classical2.orthDerived (Q.comp R.subtype)) =
      CFSG.RankThree.PartOne.KCOrthogonal.supportedOrthDerived Q R
  rw [CFSG.RankThree.PartOne.KCOrthogonal.supportedOrthDerived_eq_map hR]

private theorem reflect_maps_of_mem {R : Submodule K V} {u : V} (hu : u ∈ R) :
    ∀ x ∈ R, reflect Q u x ∈ R := by
  intro x hx
  by_cases hQu : Q u = 0
  · rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hQu]
    exact hx
  · rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hQu]
    exact Submodule.sub_mem R hx (Submodule.smul_mem R _ hu)

private theorem extendHom_reflect {R : Submodule K V}
    (hR : IsCompl R (CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q R)) {u : V} (hu : u ∈ R) :
    CFSG.RankThree.PartOne.KCOrthogonal.extendHom hR
      ⟨reflect (Q.comp R.subtype) ⟨u, hu⟩,
        CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup (Q.comp R.subtype) _⟩ =
      reflect Q u := by
  let gO : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype)) :=
    ⟨reflect (Q.comp R.subtype) ⟨u, hu⟩,
      CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup (Q.comp R.subtype) _⟩
  have hgapply : ∀ r : R, ((gO : R ≃ₗ[K] R) r : V) = reflect Q u (r : V) := by
    intro r
    by_cases hQu : Q u = 0
    · have hQu' : (Q.comp R.subtype) ⟨u, hu⟩ = 0 := hQu
      have hg : (gO : R ≃ₗ[K] R) = 1 := by
        change reflect (Q.comp R.subtype) ⟨u, hu⟩ = 1
        exact CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hQu'
      rw [hg]
      simp [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hQu]
    · have hQu' : (Q.comp R.subtype) ⟨u, hu⟩ ≠ 0 := hQu
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hQu',
        CFSG.ClassicalGroups.Orthogonal.reflect_apply hQu]
      have hpolar : polar (Q.comp R.subtype) ⟨u, hu⟩ r = polar Q u (r : V) := rfl
      rw [hpolar]
      simp
  apply LinearEquiv.ext
  intro v
  obtain ⟨r, w, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_add_of_isCompl hR v
  rw [map_add, map_add, CFSG.RankThree.PartOne.KCOrthogonal.extendHom_apply_mem hR gO r,
    CFSG.RankThree.PartOne.KCOrthogonal.extendHom_fix hR gO w.2, hgapply r,
    CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
      (CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp.mp w.2 u hu)]

private noncomputable def frameO1 (F : FrameData Q) : Subgroup (V ≃ₗ[K] V) :=
  orthImage (Q := Q) (frameW1_isCompl F)

private noncomputable def frameO2 (F : FrameData Q) : Subgroup (V ≃ₗ[K] V) :=
  orthImage (Q := Q) (frameW2_isCompl F)

private noncomputable def frameB1 (F : FrameData Q) : Subgroup (V ≃ₗ[K] V) :=
  orthImage (Q := Q) (frameU1_isCompl F)

private noncomputable def frameB2 (F : FrameData Q) : Subgroup (V ≃ₗ[K] V) :=
  orthImage (Q := Q) (frameU2_isCompl F)

@[expose] noncomputable def frameX1 (F : FrameData Q) : Subgroup (V ≃ₗ[K] V) :=
  CFSG.RankThree.PartOne.KCOrthogonal.supportedOrthDerived Q (frameW1 F)

@[expose] noncomputable def frameX2 (F : FrameData Q) : Subgroup (V ≃ₗ[K] V) :=
  CFSG.RankThree.PartOne.KCOrthogonal.supportedOrthDerived Q (frameW2 F)

private theorem frameB1_le_frameO1 (F : FrameData Q) : frameB1 F ≤ frameO1 F := by
  intro b hb
  have h := mem_map_extendHom_of_preserves (R := frameW1 F) (frameW1_isCompl F)
    (orthImage_le_orthogonalGroup (R := frameU1 F) hb) ?_ ?_
  · rwa [map_extendHom_top (frameW1_isCompl F)] at h
  · intro r hr
    have hbe4 : b (F.e 4) = F.e 4 :=
      orthImage_fix (R := frameU1 F) hb (frameW2_le_orthPerp_frameU1 F (frameW2_e4_mem F))
    rw [frameW1_eq_sup] at hr ⊢
    rcases Submodule.mem_sup.mp hr with ⟨u, hu, z, hz, rfl⟩
    rcases Submodule.mem_span_singleton.mp hz with ⟨c, rfl⟩
    rw [map_add, map_smul, hbe4]
    exact Submodule.mem_sup.mpr ⟨b u, orthImage_maps (R := frameU1 F) hb hu,
      c • F.e 4, Submodule.smul_mem _ c (Submodule.subset_span rfl), rfl⟩
  · intro w hw
    exact orthImage_fix (R := frameU1 F) hb (CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp.mpr
      fun u hu => CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp.mp hw u
        (frameU1_le_frameW1 F hu))

private theorem frameB2_le_frameO2 (F : FrameData Q) : frameB2 F ≤ frameO2 F := by
  intro b hb
  have h := mem_map_extendHom_of_preserves (R := frameW2 F) (frameW2_isCompl F)
    (orthImage_le_orthogonalGroup (R := frameU2 F) hb) ?_ ?_
  · rwa [map_extendHom_top (frameW2_isCompl F)] at h
  · intro r hr
    have hbe4 : b (F.e 4) = F.e 4 :=
      orthImage_fix (R := frameU2 F) hb (frameW1_le_orthPerp_frameU2 F (frameW1_e4_mem F))
    rw [frameW2_eq_sup] at hr ⊢
    rcases Submodule.mem_sup.mp hr with ⟨u, hu, z, hz, rfl⟩
    rcases Submodule.mem_span_singleton.mp hz with ⟨c, rfl⟩
    rw [map_add, map_smul, hbe4]
    exact Submodule.mem_sup.mpr ⟨b u, orthImage_maps (R := frameU2 F) hb hu,
      c • F.e 4, Submodule.smul_mem _ c (Submodule.subset_span rfl), rfl⟩
  · intro w hw
    exact orthImage_fix (R := frameU2 F) hb (CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp.mpr
      fun u hu => CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp.mp hw u
        (frameU2_le_frameW2 F hu))

private theorem frameX1_le_frameO1 (F : FrameData Q) : frameX1 F ≤ frameO1 F :=
  supportedOrthDerived_le_orthImage (frameW1_isCompl F)

private theorem frameX2_le_frameO2 (F : FrameData Q) : frameX2 F ≤ frameO2 F :=
  supportedOrthDerived_le_orthImage (frameW2_isCompl F)

private theorem commutator_frameO1_eq_frameX1 (F : FrameData Q) :
    ⁅frameO1 F, frameO1 F⁆ = frameX1 F :=
  commutator_orthImage_eq_supported (frameW1_isCompl F)

private theorem commutator_frameO2_eq_frameX2 (F : FrameData Q) :
    ⁅frameO2 F, frameO2 F⁆ = frameX2 F :=
  commutator_orthImage_eq_supported (frameW2_isCompl F)

private theorem exists_mem_frameU1_norm (F : FrameData Q) (c : K) :
    ∃ u ∈ frameU1 F, Q u = c := by
  have hchar : ringChar K ≠ 2 := by
    intro h
    have hzero : (ringChar K : K) = 0 := CharP.cast_eq_zero K (ringChar K)
    rw [h] at hzero
    exact F.two_ne_zero hzero
  obtain ⟨a, b, hab⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_odd_field_two_squares hchar c
  refine ⟨a • F.e 0 + b • F.e 1, ?_, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ a (frameU1_e0_mem F))
      (Submodule.smul_mem _ b (frameU1_e1_mem F))
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul,
      F.norm 0 (by norm_num), F.norm 1 (by norm_num)]
    simp [F.orth]
    simpa [pow_two] using hab

private theorem exists_mem_frameU2_norm (F : FrameData Q) (c : K) :
    ∃ u ∈ frameU2 F, Q u = c := by
  have hchar : ringChar K ≠ 2 := by
    intro h
    have hzero : (ringChar K : K) = 0 := CharP.cast_eq_zero K (ringChar K)
    rw [h] at hzero
    exact F.two_ne_zero hzero
  obtain ⟨a, b, hab⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_odd_field_two_squares hchar c
  refine ⟨a • F.e 2 + b • F.e 3, ?_, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ a (frameU2_e2_mem F))
      (Submodule.smul_mem _ b (frameU2_e3_mem F))
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul,
      F.norm 2 (by norm_num), F.norm 3 (by norm_num)]
    simp [F.orth]
    simpa [pow_two] using hab

private theorem frameW1_reflect_mem_sup (F : FrameData Q) (v : ↥(frameW1 F)) :
    CFSG.LocalAnalysis.ComponentInitial.orthExtend (frameW1_isCompl F)
      (reflect (Q.comp (frameW1 F).subtype) v) ∈ frameX1 F ⊔ frameB1 F := by
  set svO : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW1 F).subtype)) :=
    ⟨reflect (Q.comp (frameW1 F).subtype) v,
      CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup (Q.comp (frameW1 F).subtype) v⟩
  by_cases hQv : (Q.comp (frameW1 F).subtype) v = 0
  · have hsv : svO = 1 := by
      apply Subtype.ext
      exact CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hQv
    rw [show CFSG.LocalAnalysis.ComponentInitial.orthExtend (frameW1_isCompl F)
      (reflect (Q.comp (frameW1 F).subtype) v) =
        CFSG.RankThree.PartOne.KCOrthogonal.extendHom (frameW1_isCompl F) svO from rfl,
      hsv, map_one]
    exact Subgroup.one_mem _
  · have hQv' : Q (v : V) ≠ 0 := hQv
    obtain ⟨u, hu, hQu⟩ := exists_mem_frameU1_norm F (Q (v : V))
    have huW1 : u ∈ frameW1 F := frameU1_le_frameW1 F hu
    set suO : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW1 F).subtype)) :=
      ⟨reflect (Q.comp (frameW1 F).subtype) ⟨u, huW1⟩,
        CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup
          (Q.comp (frameW1 F).subtype) ⟨u, huW1⟩⟩
    have hQu' : (Q.comp (frameW1 F).subtype) ⟨u, huW1⟩ ≠ 0 := by
      simpa [hQu] using hQv
    have hsq : IsSquare ((Q.comp (frameW1 F).subtype) v *
        (Q.comp (frameW1 F).subtype) ⟨u, huW1⟩) := by
      refine ⟨Q (v : V), ?_⟩
      change Q (v : V) * Q u = Q (v : V) * Q (v : V)
      rw [hQu]
    have hclass := CFSG.LocalAnalysis.ComponentInitial.reflectClass_eq_of_isSquare
      (Q := Q.comp (frameW1 F).subtype) F.two_ne_zero hQv hQu' hsq
    have hclass' : Abelianization.of svO = Abelianization.of suO := by
      simpa [CFSG.LocalAnalysis.ComponentInitial.reflectClass, svO, suO] using hclass
    have hsu_sq : suO * suO = 1 := by
      apply Subtype.ext
      exact CFSG.ClassicalGroups.Orthogonal.reflect_mul_self (Q.comp (frameW1 F).subtype) _
    have hcommem : svO * suO ∈ commutator
        (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW1 F).subtype)) := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul]
      have hsq2 : Abelianization.of suO * Abelianization.of suO = 1 := by
        have h := CFSG.LocalAnalysis.ComponentInitial.reflectClass_sq
          (Q := Q.comp (frameW1 F).subtype) ⟨u, huW1⟩
        simpa [CFSG.LocalAnalysis.ComponentInitial.reflectClass, suO, pow_two] using h
      calc Abelianization.of svO * Abelianization.of suO
          = Abelianization.of suO * Abelianization.of suO := by rw [hclass']
        _ = 1 := hsq2
    have hmemOrth : ((svO * suO : _) : frameW1 F ≃ₗ[K] frameW1 F) ∈
        CFSG.RankThree.Classical2.orthDerived (Q.comp (frameW1 F).subtype) := by
      change ((svO * suO : _) : frameW1 F ≃ₗ[K] frameW1 F) ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW1 F).subtype),
          TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW1 F).subtype)⁆
      rw [← Subgroup.map_subtype_commutator]
      exact Subgroup.mem_map.mpr ⟨svO * suO, hcommem, rfl⟩
    have hX : CFSG.RankThree.PartOne.KCOrthogonal.extendHom (frameW1_isCompl F)
        (svO * suO) ∈ frameX1 F := by
      rw [frameX1, CFSG.RankThree.PartOne.KCOrthogonal.supportedOrthDerived_eq_map
        (frameW1_isCompl F)]
      exact Subgroup.mem_map.mpr ⟨((svO * suO : _) : frameW1 F ≃ₗ[K] frameW1 F),
        hmemOrth, rfl⟩
    have hB : CFSG.RankThree.PartOne.KCOrthogonal.extendHom (frameW1_isCompl F) suO ∈
        frameB1 F := by
      rw [extendHom_reflect (frameW1_isCompl F) huW1,
        ← extendHom_reflect (frameU1_isCompl F) hu]
      exact orthImage_extendHom (hR := frameU1_isCompl F) _
    have hsv_eq : svO = (svO * suO) * suO := by
      rw [mul_assoc, hsu_sq, mul_one]
    rw [show CFSG.LocalAnalysis.ComponentInitial.orthExtend (frameW1_isCompl F)
      (reflect (Q.comp (frameW1 F).subtype) v) =
        CFSG.RankThree.PartOne.KCOrthogonal.extendHom (frameW1_isCompl F) svO from rfl,
      hsv_eq, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hX) (Subgroup.mem_sup_right hB)

private theorem frameO1_le_sup_frameX1_frameB1 (F : FrameData Q) :
    frameO1 F ≤ frameX1 F ⊔ frameB1 F := by
  have hgen := CFSG.ClassicalGroups.Orthogonal.orthogonalGroup_le_closure_reflect
    (Q := Q.comp (frameW1 F).subtype) (V := frameW1 F) F.two_ne_zero
    (frameW1_polar_nondegenerate F)
  calc frameO1 F
      = (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW1 F).subtype)).map
          (CFSG.LocalAnalysis.ComponentInitial.orthExtend (frameW1_isCompl F)) := rfl
    _ ≤ (Subgroup.closure (Set.range (reflect (Q.comp (frameW1 F).subtype)))).map
          (CFSG.LocalAnalysis.ComponentInitial.orthExtend (frameW1_isCompl F)) :=
        Subgroup.map_mono hgen
    _ = Subgroup.closure ((CFSG.LocalAnalysis.ComponentInitial.orthExtend
          (frameW1_isCompl F)) '' Set.range (reflect (Q.comp (frameW1 F).subtype))) := by
        rw [MonoidHom.map_closure]
    _ ≤ frameX1 F ⊔ frameB1 F := by
        rw [Subgroup.closure_le]
        rintro _ ⟨x, ⟨v, rfl⟩, rfl⟩
        exact frameW1_reflect_mem_sup F v

private theorem frameW2_reflect_mem_sup (F : FrameData Q) (v : ↥(frameW2 F)) :
    CFSG.LocalAnalysis.ComponentInitial.orthExtend (frameW2_isCompl F)
      (reflect (Q.comp (frameW2 F).subtype) v) ∈ frameX2 F ⊔ frameB2 F := by
  set svO : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW2 F).subtype)) :=
    ⟨reflect (Q.comp (frameW2 F).subtype) v,
      CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup (Q.comp (frameW2 F).subtype) v⟩
  by_cases hQv : (Q.comp (frameW2 F).subtype) v = 0
  · have hsv : svO = 1 := by
      apply Subtype.ext
      exact CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hQv
    rw [show CFSG.LocalAnalysis.ComponentInitial.orthExtend (frameW2_isCompl F)
      (reflect (Q.comp (frameW2 F).subtype) v) =
        CFSG.RankThree.PartOne.KCOrthogonal.extendHom (frameW2_isCompl F) svO from rfl,
      hsv, map_one]
    exact Subgroup.one_mem _
  · have hQv' : Q (v : V) ≠ 0 := hQv
    obtain ⟨u, hu, hQu⟩ := exists_mem_frameU2_norm F (Q (v : V))
    have huW2 : u ∈ frameW2 F := frameU2_le_frameW2 F hu
    set suO : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW2 F).subtype)) :=
      ⟨reflect (Q.comp (frameW2 F).subtype) ⟨u, huW2⟩,
        CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup
          (Q.comp (frameW2 F).subtype) ⟨u, huW2⟩⟩
    have hQu' : (Q.comp (frameW2 F).subtype) ⟨u, huW2⟩ ≠ 0 := by
      simpa [hQu] using hQv
    have hsq : IsSquare ((Q.comp (frameW2 F).subtype) v *
        (Q.comp (frameW2 F).subtype) ⟨u, huW2⟩) := by
      refine ⟨Q (v : V), ?_⟩
      change Q (v : V) * Q u = Q (v : V) * Q (v : V)
      rw [hQu]
    have hclass := CFSG.LocalAnalysis.ComponentInitial.reflectClass_eq_of_isSquare
      (Q := Q.comp (frameW2 F).subtype) F.two_ne_zero hQv hQu' hsq
    have hclass' : Abelianization.of svO = Abelianization.of suO := by
      simpa [CFSG.LocalAnalysis.ComponentInitial.reflectClass, svO, suO] using hclass
    have hsu_sq : suO * suO = 1 := by
      apply Subtype.ext
      exact CFSG.ClassicalGroups.Orthogonal.reflect_mul_self (Q.comp (frameW2 F).subtype) _
    have hcommem : svO * suO ∈ commutator
        (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW2 F).subtype)) := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul]
      have hsq2 : Abelianization.of suO * Abelianization.of suO = 1 := by
        have h := CFSG.LocalAnalysis.ComponentInitial.reflectClass_sq
          (Q := Q.comp (frameW2 F).subtype) ⟨u, huW2⟩
        simpa [CFSG.LocalAnalysis.ComponentInitial.reflectClass, suO, pow_two] using h
      calc Abelianization.of svO * Abelianization.of suO
          = Abelianization.of suO * Abelianization.of suO := by rw [hclass']
        _ = 1 := hsq2
    have hmemOrth : ((svO * suO : _) : frameW2 F ≃ₗ[K] frameW2 F) ∈
        CFSG.RankThree.Classical2.orthDerived (Q.comp (frameW2 F).subtype) := by
      change ((svO * suO : _) : frameW2 F ≃ₗ[K] frameW2 F) ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW2 F).subtype),
          TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW2 F).subtype)⁆
      rw [← Subgroup.map_subtype_commutator]
      exact Subgroup.mem_map.mpr ⟨svO * suO, hcommem, rfl⟩
    have hX : CFSG.RankThree.PartOne.KCOrthogonal.extendHom (frameW2_isCompl F)
        (svO * suO) ∈ frameX2 F := by
      rw [frameX2, CFSG.RankThree.PartOne.KCOrthogonal.supportedOrthDerived_eq_map
        (frameW2_isCompl F)]
      exact Subgroup.mem_map.mpr ⟨((svO * suO : _) : frameW2 F ≃ₗ[K] frameW2 F),
        hmemOrth, rfl⟩
    have hB : CFSG.RankThree.PartOne.KCOrthogonal.extendHom (frameW2_isCompl F) suO ∈
        frameB2 F := by
      rw [extendHom_reflect (frameW2_isCompl F) huW2,
        ← extendHom_reflect (frameU2_isCompl F) hu]
      exact orthImage_extendHom (hR := frameU2_isCompl F) _
    have hsv_eq : svO = (svO * suO) * suO := by
      rw [mul_assoc, hsu_sq, mul_one]
    rw [show CFSG.LocalAnalysis.ComponentInitial.orthExtend (frameW2_isCompl F)
      (reflect (Q.comp (frameW2 F).subtype) v) =
        CFSG.RankThree.PartOne.KCOrthogonal.extendHom (frameW2_isCompl F) svO from rfl,
      hsv_eq, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hX) (Subgroup.mem_sup_right hB)

private theorem frameO2_le_sup_frameX2_frameB2 (F : FrameData Q) :
    frameO2 F ≤ frameX2 F ⊔ frameB2 F := by
  have hgen := CFSG.ClassicalGroups.Orthogonal.orthogonalGroup_le_closure_reflect
    (Q := Q.comp (frameW2 F).subtype) (V := frameW2 F) F.two_ne_zero
    (frameW2_polar_nondegenerate F)
  calc frameO2 F
      = (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW2 F).subtype)).map
          (CFSG.LocalAnalysis.ComponentInitial.orthExtend (frameW2_isCompl F)) := rfl
    _ ≤ (Subgroup.closure (Set.range (reflect (Q.comp (frameW2 F).subtype)))).map
          (CFSG.LocalAnalysis.ComponentInitial.orthExtend (frameW2_isCompl F)) :=
        Subgroup.map_mono hgen
    _ = Subgroup.closure ((CFSG.LocalAnalysis.ComponentInitial.orthExtend
          (frameW2_isCompl F)) '' Set.range (reflect (Q.comp (frameW2 F).subtype))) := by
        rw [MonoidHom.map_closure]
    _ ≤ frameX2 F ⊔ frameB2 F := by
        rw [Subgroup.closure_le]
        rintro _ ⟨x, ⟨v, rfl⟩, rfl⟩
        exact frameW2_reflect_mem_sup F v

private theorem frameW2_singular_nonzero (F : FrameData Q) (hneg : IsSquare (-1 : K)) :
    ∃ u ∈ frameU2 F, Q u = 0 ∧ u ≠ 0 := by
  obtain ⟨i, hi⟩ := hneg
  refine ⟨F.e 2 + i • F.e 3, ?_, ?_, ?_⟩
  · exact Submodule.add_mem _ (frameU2_e2_mem F) (Submodule.smul_mem _ i (frameU2_e3_mem F))
  · have hQ2 : Q (F.e 2) = 1 := F.norm 2 (by norm_num)
    have hQ3 : Q (F.e 3) = 1 := F.norm 3 (by norm_num)
    have hp : polar Q (F.e 2) (F.e 3) = 0 := F.orth 2 3 (by norm_num)
    have hQ3' : Q (i • F.e 3) = i * i := by
      rw [QuadraticMap.map_smul, hQ3]
      ring
    have hp' : polar Q (F.e 2) (i • F.e 3) = 0 := by
      rw [QuadraticMap.polar_smul_right, hp]
      simp
    rw [QuadraticMap.map_add Q, hQ2, hQ3', hp', add_zero]
    rw [← hi]
    ring
  · intro hu
    have hcoord := congrArg (fun w : V => F.coord w 2) hu
    simp [F.coord_e, map_add, map_smul, Pi.single] at hcoord

private theorem frame_decompose (F : FrameData Q) (v : V) :
    ∃ u1 ∈ frameU1 F, ∃ u2 ∈ frameU2 F, ∃ a : K, v = u1 + u2 + a • F.e 4 := by
  let c := F.coord v
  let u1 : V := c 0 • F.e 0 + c 1 • F.e 1
  let u2 : V := c 2 • F.e 2 + c 3 • F.e 3
  let a : K := c 4
  refine ⟨u1, ?_, u2, ?_, a, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ (c 0) (frameU1_e0_mem F))
      (Submodule.smul_mem _ (c 1) (frameU1_e1_mem F))
  · exact Submodule.add_mem _ (Submodule.smul_mem _ (c 2) (frameU2_e2_mem F))
      (Submodule.smul_mem _ (c 3) (frameU2_e3_mem F))
  · apply F.coord.injective
    ext i
    fin_cases i <;>
      simp [u1, u2, a, F.coord_e, map_add, map_smul, Pi.single] <;> rfl

private theorem coord_frameU2_four (F : FrameData Q) {u : V} (hu : u ∈ frameU2 F) :
    F.coord u 4 = 0 := by
  refine Submodule.span_induction (p := fun x _ => F.coord x 4 = 0) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [F.coord_e, Pi.single]
  · simp
  · intro a b _ _ ha hb
    rw [map_add]
    show (F.coord a) 4 + (F.coord b) 4 = 0
    rw [ha, hb, add_zero]
  · intro c a _ ha
    rw [map_smul]
    show c * (F.coord a) 4 = 0
    rw [ha, mul_zero]

private theorem frameU2_add_smul_e4_ne_zero (F : FrameData Q) {u : V}
    (hu : u ∈ frameU2 F) {a : K} (ha : a ≠ 0) : u + a • F.e 4 ≠ 0 := by
  intro hzero
  have hcoord := congrArg (fun w : V => F.coord w 4) hzero
  simp [map_add, map_smul, coord_frameU2_four F hu, F.coord_e] at hcoord
  exact ha hcoord

private theorem Q_add_smul_e4_frameU1 (F : FrameData Q) {u : V}
    (hu : u ∈ frameU1 F) (a : K) :
    Q (u + a • F.e 4) = Q u + a ^ 2 * Q (F.e 4) := by
  have hp : polar Q u (a • F.e 4) = 0 := by
    rw [QuadraticMap.polar_smul_right, polar_frameU1_e4 F hu]
    simp
  have hq : Q (a • F.e 4) = a ^ 2 * Q (F.e 4) := by
    rw [QuadraticMap.map_smul]
    ring
  rw [QuadraticMap.map_add Q, hp, hq]
  ring

private theorem Q_add_smul_e4_frameU2 (F : FrameData Q) {u : V}
    (hu : u ∈ frameU2 F) (a : K) :
    Q (u + a • F.e 4) = Q u + a ^ 2 * Q (F.e 4) := by
  have hp : polar Q u (a • F.e 4) = 0 := by
    rw [QuadraticMap.polar_smul_right, polar_frameU2_e4 F hu]
    simp
  have hq : Q (a • F.e 4) = a ^ 2 * Q (F.e 4) := by
    rw [QuadraticMap.map_smul]
    ring
  rw [QuadraticMap.map_add Q, hp, hq]
  ring

private theorem frame_move_to_W2_of_ne_zero (F : FrameData Q) (hq5 : 5 ≤ Nat.card K)
    {u1 u2 : V} (hu1 : u1 ∈ frameU1 F) (hu2 : u2 ∈ frameU2 F) (a0 : K)
    (hw2ne : u2 + a0 • F.e 4 ≠ 0) :
    ∃ g ∈ frameO1 F ⊔ frameO2 F, g (u1 + u2 + a0 • F.e 4) ∈ frameW2 F := by
  have hdelta : Q (F.e 4) ≠ 0 := F.last
  let delta : K := Q (F.e 4)
  let c : K := Q u1 / delta
  obtain ⟨a, b, hab, hb, ha_or_sq⟩ := exists_scalar_choice F.two_ne_zero hq5 c
  let w2 : V := u2 + a0 • F.e 4
  have hw2W2 : w2 ∈ frameW2 F := by
    rw [frameW2_eq_sup]
    exact Submodule.mem_sup.mpr ⟨u2, hu2, a0 • F.e 4,
      Submodule.smul_mem _ a0 (Submodule.subset_span rfl), rfl⟩
  have hQw2 : Q w2 = Q u2 + a0 ^ 2 * delta :=
    Q_add_smul_e4_frameU2 F hu2 a0
  have hu2'ex : ∃ u2' ∈ frameU2 F, Q u2' = Q w2 - delta * a ^ 2 ∧
      u2' + a • F.e 4 ≠ 0 := by
    by_cases ha : a = 0
    · subst ha
      by_cases hz : Q w2 = 0
      · rcases ha_or_sq with ha0 | hsq
        · exact absurd rfl ha0
        · obtain ⟨u2', hu2', hQu2', hne⟩ := frameW2_singular_nonzero F hsq
          refine ⟨u2', hu2', ?_, ?_⟩
          · simpa [hz] using hQu2'
          · simpa using hne
      · obtain ⟨u2', hu2', hQu2'⟩ := exists_mem_frameU2_norm F (Q w2)
        refine ⟨u2', hu2', by simpa using hQu2', ?_⟩
        intro hzero
        have hzero' : u2' = 0 := by simpa using hzero
        exact hz (by rw [← hQu2', hzero']; simp)
    · obtain ⟨u2', hu2', hQu2'⟩ := exists_mem_frameU2_norm F (Q w2 - delta * a ^ 2)
      exact ⟨u2', hu2', hQu2', frameU2_add_smul_e4_ne_zero F hu2' ha⟩
  obtain ⟨u2', hu2', hQu2', hw2'ne⟩ := hu2'ex
  let w2' : V := u2' + a • F.e 4
  have hw2'W2 : w2' ∈ frameW2 F := by
    rw [frameW2_eq_sup]
    exact Submodule.mem_sup.mpr ⟨u2', hu2', a • F.e 4,
      Submodule.smul_mem _ a (Submodule.subset_span rfl), rfl⟩
  have hQw2' : Q w2' = Q w2 := by
    change Q (u2' + a • F.e 4) = Q w2
    rw [Q_add_smul_e4_frameU2 F hu2' a, hQu2']
    ring
  have hg2ex : ∃ g2 ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW2 F).subtype),
      g2 ⟨w2, hw2W2⟩ = ⟨w2', hw2'W2⟩ := by
    by_cases hz : Q w2 = 0
    · have hz' : Q w2' = 0 := by rw [hQw2']; exact hz
      exact CFSG.ClassicalInvolution.exists_mem_orthogonalGroup_apply_eq_of_nondegenerate
        (Q := Q.comp (frameW2 F).subtype) (frameW2_polar_nondegenerate F)
        (by simpa using hz) (by simpa using hz')
        (fun h => hw2ne (congrArg Subtype.val h))
        (fun h => hw2'ne (congrArg Subtype.val h))
    · have hz' : Q w2' ≠ 0 := by rwa [hQw2']
      exact CFSG.LocalAnalysis.ComponentInitial.exists_mem_orthogonalGroup_apply_eq
        (Q := Q.comp (frameW2 F).subtype) F.two_ne_zero
        (by simpa using hQw2'.symm) (by simpa using hz')
  obtain ⟨g2, hg2, hg2apply⟩ := hg2ex
  have hdelta' : delta ≠ 0 := hdelta
  have hc_eq : Q u1 = delta * c := by
    dsimp [c]
    field_simp [hdelta']
  have hb2 : b ^ 2 = a ^ 2 + c := by
    linear_combination hab
  have hQ1 : Q (u1 + a • F.e 4) = delta * b ^ 2 := by
    rw [Q_add_smul_e4_frameU1 F hu1 a, hc_eq, hb2]
    ring
  have hQ2b : Q (b • F.e 4) = delta * b ^ 2 := by
    rw [QuadraticMap.map_smul]
    ring
  have hQ1ne : Q (u1 + a • F.e 4) ≠ 0 := by
    rw [hQ1]
    exact mul_ne_zero hdelta (pow_ne_zero 2 hb)
  have hQ2bne : Q (b • F.e 4) ≠ 0 := by
    rw [hQ2b]
    exact mul_ne_zero hdelta (pow_ne_zero 2 hb)
  have hg1ex : ∃ g1 ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW1 F).subtype),
      g1 ⟨u1 + a • F.e 4,
        (frameW1_eq_sup F ▸ Submodule.mem_sup.mpr ⟨u1, hu1, a • F.e 4,
          Submodule.smul_mem _ a (Submodule.subset_span rfl), rfl⟩)⟩ =
        ⟨b • F.e 4, frameW1_eq_sup F ▸ Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _,
          b • F.e 4, Submodule.smul_mem _ b (Submodule.subset_span rfl), by simp⟩⟩ := by
    exact CFSG.LocalAnalysis.ComponentInitial.exists_mem_orthogonalGroup_apply_eq
      (Q := Q.comp (frameW1 F).subtype) F.two_ne_zero
      (by simpa using hQ1.trans hQ2b.symm) (by simpa using hQ2bne)
  obtain ⟨g1, hg1, hg1apply⟩ := hg1ex
  let g1O : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW1 F).subtype)) := ⟨g1, hg1⟩
  let g2O : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW2 F).subtype)) := ⟨g2, hg2⟩
  let b1 : V ≃ₗ[K] V :=
    CFSG.RankThree.PartOne.KCOrthogonal.extendHom (frameW1_isCompl F) g1O
  let b2 : V ≃ₗ[K] V :=
    CFSG.RankThree.PartOne.KCOrthogonal.extendHom (frameW2_isCompl F) g2O
  have hb1O : b1 ∈ frameO1 F := orthImage_extendHom g1O
  have hb2O : b2 ∈ frameO2 F := orthImage_extendHom g2O
  refine ⟨b1 * b2, Subgroup.mul_mem _ (Subgroup.mem_sup_left hb1O)
    (Subgroup.mem_sup_right hb2O), ?_⟩
  have hb2fix : b2 u1 = u1 :=
    orthImage_fix (R := frameW2 F) hb2O (frameU1_le_orthPerp_frameW2 F hu1)
  have hb2w2 : b2 w2 = w2' := by
    rw [show b2 = CFSG.RankThree.PartOne.KCOrthogonal.extendHom (frameW2_isCompl F) g2O from rfl,
      CFSG.RankThree.PartOne.KCOrthogonal.extendHom_apply_mem (frameW2_isCompl F) g2O ⟨w2, hw2W2⟩]
    exact congrArg Subtype.val hg2apply
  have hb1fix : b1 u2' = u2' :=
    orthImage_fix (R := frameW1 F) hb1O (frameU2_le_orthPerp_frameW1 F hu2')
  have hb1u1a : b1 (u1 + a • F.e 4) = b • F.e 4 := by
    rw [show b1 = CFSG.RankThree.PartOne.KCOrthogonal.extendHom (frameW1_isCompl F) g1O from rfl,
      CFSG.RankThree.PartOne.KCOrthogonal.extendHom_apply_mem (frameW1_isCompl F) g1O
        ⟨u1 + a • F.e 4,
          (frameW1_eq_sup F ▸ Submodule.mem_sup.mpr ⟨u1, hu1, a • F.e 4,
            Submodule.smul_mem _ a (Submodule.subset_span rfl), rfl⟩)⟩]
    exact congrArg Subtype.val hg1apply
  have hb2v : b2 (u1 + u2 + a0 • F.e 4) = u1 + w2' := by
    rw [show u1 + u2 + a0 • F.e 4 = u1 + w2 by
      dsimp [w2]
      abel]
    rw [map_add, hb2fix, hb2w2]
  have hb1v : b1 (u1 + w2') = u2' + b • F.e 4 := by
    rw [show u1 + w2' = (u1 + a • F.e 4) + u2' by
      dsimp [w2']
      abel]
    rw [map_add, hb1u1a, hb1fix]
    abel
  have hresult : (b1 * b2) (u1 + u2 + a0 • F.e 4) = u2' + b • F.e 4 := by
    rw [LinearEquiv.mul_apply, hb2v, hb1v]
  rw [hresult]
  rw [frameW2_eq_sup]
  exact Submodule.mem_sup.mpr ⟨u2', hu2', b • F.e 4,
    Submodule.smul_mem _ b (Submodule.subset_span rfl), rfl⟩

private theorem frame_move_to_W2 (F : FrameData Q) (hq5 : 5 ≤ Nat.card K)
    (v : V) (hv : Q v ≠ 0) :
    ∃ g ∈ frameO1 F ⊔ frameO2 F, g v ∈ frameW2 F := by
  obtain ⟨u1, hu1, u2, hu2, a0, hvdecomp⟩ := frame_decompose F v
  let w2 : V := u2 + a0 • F.e 4
  by_cases hw2 : w2 = 0
  · have hv_eq : v = u1 := by
      rw [hvdecomp]
      have h : u1 + u2 + a0 • F.e 4 = u1 + (u2 + a0 • F.e 4) := by abel
      dsimp [w2] at hw2
      rw [h, hw2, add_zero]
    have hQv : Q u1 ≠ 0 := by rwa [hv_eq] at hv
    obtain ⟨u1', hu1', hQ1'⟩ := exists_mem_frameU1_norm F (Q u1 - Q (F.e 4))
    let y : V := u1' + F.e 4
    have hyW1 : y ∈ frameW1 F := by
      rw [frameW1_eq_sup]
      exact Submodule.mem_sup.mpr ⟨u1', hu1', F.e 4,
        Submodule.subset_span rfl, by simp [y]⟩
    have hu1W1 : u1 ∈ frameW1 F := frameU1_le_frameW1 F hu1
    have hQy : Q y = Q u1 := by
      dsimp [y]
      rw [show u1' + F.e 4 = u1' + (1 : K) • F.e 4 by simp]
      rw [Q_add_smul_e4_frameU1 F hu1' 1, hQ1']
      ring
    have hQy_ne : Q y ≠ 0 := by rwa [hQy]
    obtain ⟨gpre, hgpre, hgpreapply⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.exists_mem_orthogonalGroup_apply_eq
        (Q := Q.comp (frameW1 F).subtype) (v := (⟨u1, hu1W1⟩ : ↥(frameW1 F)))
        (w := (⟨y, hyW1⟩ : ↥(frameW1 F))) F.two_ne_zero
        (by simpa using hQy.symm) (by simpa using hQy_ne)
    let gpreO : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (frameW1 F).subtype)) :=
      ⟨gpre, hgpre⟩
    let bpre : V ≃ₗ[K] V :=
      CFSG.RankThree.PartOne.KCOrthogonal.extendHom (frameW1_isCompl F) gpreO
    have hbpreO : bpre ∈ frameO1 F := orthImage_extendHom gpreO
    have hbprev : bpre v = y := by
      rw [hv_eq]
      rw [show bpre = CFSG.RankThree.PartOne.KCOrthogonal.extendHom
          (frameW1_isCompl F) gpreO from rfl,
        CFSG.RankThree.PartOne.KCOrthogonal.extendHom_apply_mem (frameW1_isCompl F) gpreO
          ⟨u1, hu1W1⟩]
      exact congrArg Subtype.val hgpreapply
    have hw2ne : (0 : V) + (1 : K) • F.e 4 ≠ 0 := by
      simpa using F.e.ne_zero 4
    obtain ⟨g, hg, hgy⟩ := frame_move_to_W2_of_ne_zero F hq5 hu1'
      (Submodule.zero_mem _) (1 : K) hw2ne
    refine ⟨g * bpre, Subgroup.mul_mem _ hg (Subgroup.mem_sup_left hbpreO), ?_⟩
    rw [LinearEquiv.mul_apply, hbprev]
    simpa [y] using hgy
  · obtain ⟨g, hg, hgy⟩ :=
      frame_move_to_W2_of_ne_zero F hq5 hu1 hu2 a0 hw2
    exact ⟨g, hg, by rw [hvdecomp]; exact hgy⟩

private theorem reflect_mem_frameO2 (F : FrameData Q) {w : V} (hw : w ∈ frameW2 F) :
    reflect Q w ∈ frameO2 F := by
  have h := mem_map_extendHom_of_preserves (R := frameW2 F) (frameW2_isCompl F)
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q w)
    (reflect_maps_of_mem (R := frameW2 F) hw)
    (fun z hz => CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
      (CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp.mp hz w hw))
  rwa [map_extendHom_top (frameW2_isCompl F)] at h

private theorem frameO1_sup_frameO2_eq_orthogonalGroup (F : FrameData Q)
    (hq5 : 5 ≤ Nat.card K) :
    frameO1 F ⊔ frameO2 F = TauCeti.QuadraticMap.orthogonalGroup Q := by
  apply le_antisymm
  · exact sup_le (orthImage_le_orthogonalGroup (R := frameW1 F))
      (orthImage_le_orthogonalGroup (R := frameW2 F))
  · have hOle : frameO1 F ⊔ frameO2 F ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
      sup_le (orthImage_le_orthogonalGroup (R := frameW1 F))
        (orthImage_le_orthogonalGroup (R := frameW2 F))
    calc TauCeti.QuadraticMap.orthogonalGroup Q
        ≤ Subgroup.closure (Set.range (reflect Q)) :=
          CFSG.ClassicalGroups.Orthogonal.orthogonalGroup_le_closure_reflect
            (Q := Q) F.two_ne_zero F.nondeg
      _ ≤ frameO1 F ⊔ frameO2 F := by
          rw [Subgroup.closure_le]
          rintro _ ⟨v, rfl⟩
          by_cases hv : Q v = 0
          · rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hv]
            exact Subgroup.one_mem _
          · obtain ⟨g, hg, hgv⟩ := frame_move_to_W2 F hq5 v hv
            have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hOle hg
            have href : reflect Q (g v) ∈ frameO2 F := reflect_mem_frameO2 F hgv
            have hconj := CFSG.ClassicalGroups.Orthogonal.reflect_conj (Q := Q) hgO v
            have hformula : reflect Q v = g⁻¹ * reflect Q (g v) * g := by
              calc reflect Q v = g⁻¹ * (g * reflect Q v * g⁻¹) * g := by group
                _ = g⁻¹ * reflect Q (g v) * g := by rw [hconj]
            rw [hformula]
            exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg)
              (Subgroup.mem_sup_right href)) hg

private theorem frameB1_fix_frameW2 (F : FrameData Q) {b : V ≃ₗ[K] V}
    (hb : b ∈ frameB1 F) {w : V} (hw : w ∈ frameW2 F) : b w = w :=
  orthImage_fix (R := frameU1 F) hb (frameW2_le_orthPerp_frameU1 F hw)

private theorem frameB2_fix_frameW1 (F : FrameData Q) {b : V ≃ₗ[K] V}
    (hb : b ∈ frameB2 F) {w : V} (hw : w ∈ frameW1 F) : b w = w :=
  orthImage_fix (R := frameU2 F) hb (frameW1_le_orthPerp_frameU2 F hw)

private theorem frameX2_fix_frameU1 (F : FrameData Q) {x : V ≃ₗ[K] V}
    (hx : x ∈ frameX2 F) {u : V} (hu : u ∈ frameU1 F) : x u = u :=
  orthImage_fix (R := frameW2 F) (frameX2_le_frameO2 F hx) (frameU1_le_orthPerp_frameW2 F hu)

private theorem frameX1_fix_frameU2 (F : FrameData Q) {x : V ≃ₗ[K] V}
    (hx : x ∈ frameX1 F) {u : V} (hu : u ∈ frameU2 F) : x u = u :=
  orthImage_fix (R := frameW1 F) (frameX1_le_frameO1 F hx) (frameU2_le_orthPerp_frameW1 F hu)

private theorem frameB1_centralizes_frameX2 (F : FrameData Q) :
    ∀ b ∈ frameB1 F, ∀ x ∈ frameX2 F, b * x = x * b := by
  intro b hb x hx
  have hbO : b ∈ frameO1 F := frameB1_le_frameO1 F hb
  have hbU1 : ∀ u ∈ frameU1 F, b u ∈ frameU1 F :=
    fun u hu => orthImage_maps (R := frameU1 F) hb hu
  have hxW2 : ∀ w ∈ frameW2 F, x w ∈ frameW2 F :=
    fun w hw => orthImage_maps (R := frameW2 F) (frameX2_le_frameO2 F hx) hw
  apply LinearEquiv.ext
  intro v
  have h : ((b * x : V ≃ₗ[K] V) : V →ₗ[K] V) = ((x * b : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    apply F.e.ext
    intro i
    change (b * x) (F.e i) = (x * b) (F.e i)
    fin_cases i
    · change b (x (F.e 0)) = x (b (F.e 0))
      rw [frameX2_fix_frameU1 F hx (frameU1_e0_mem F),
        frameX2_fix_frameU1 F hx (hbU1 (F.e 0) (frameU1_e0_mem F))]
    · change b (x (F.e 1)) = x (b (F.e 1))
      rw [frameX2_fix_frameU1 F hx (frameU1_e1_mem F),
        frameX2_fix_frameU1 F hx (hbU1 (F.e 1) (frameU1_e1_mem F))]
    · change b (x (F.e 2)) = x (b (F.e 2))
      rw [frameB1_fix_frameW2 F hb (frameW2_e2_mem F),
        frameB1_fix_frameW2 F hb (hxW2 (F.e 2) (frameW2_e2_mem F))]
    · change b (x (F.e 3)) = x (b (F.e 3))
      rw [frameB1_fix_frameW2 F hb (frameW2_e3_mem F),
        frameB1_fix_frameW2 F hb (hxW2 (F.e 3) (frameW2_e3_mem F))]
    · change b (x (F.e 4)) = x (b (F.e 4))
      rw [frameB1_fix_frameW2 F hb (frameW2_e4_mem F),
        frameB1_fix_frameW2 F hb (hxW2 (F.e 4) (frameW2_e4_mem F))]
  exact LinearMap.congr_fun h v

private theorem frameB2_centralizes_frameX1 (F : FrameData Q) :
    ∀ b ∈ frameB2 F, ∀ x ∈ frameX1 F, b * x = x * b := by
  intro b hb x hx
  have hbO : b ∈ frameO2 F := frameB2_le_frameO2 F hb
  have hbU2 : ∀ u ∈ frameU2 F, b u ∈ frameU2 F :=
    fun u hu => orthImage_maps (R := frameU2 F) hb hu
  have hxW1 : ∀ w ∈ frameW1 F, x w ∈ frameW1 F :=
    fun w hw => orthImage_maps (R := frameW1 F) (frameX1_le_frameO1 F hx) hw
  apply LinearEquiv.ext
  intro v
  have h : ((b * x : V ≃ₗ[K] V) : V →ₗ[K] V) = ((x * b : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    apply F.e.ext
    intro i
    change (b * x) (F.e i) = (x * b) (F.e i)
    fin_cases i
    · change b (x (F.e 0)) = x (b (F.e 0))
      rw [frameB2_fix_frameW1 F hb (frameW1_e0_mem F),
        frameB2_fix_frameW1 F hb (hxW1 (F.e 0) (frameW1_e0_mem F))]
    · change b (x (F.e 1)) = x (b (F.e 1))
      rw [frameB2_fix_frameW1 F hb (frameW1_e1_mem F),
        frameB2_fix_frameW1 F hb (hxW1 (F.e 1) (frameW1_e1_mem F))]
    · change b (x (F.e 2)) = x (b (F.e 2))
      rw [frameX1_fix_frameU2 F hx (frameU2_e2_mem F),
        frameX1_fix_frameU2 F hx (hbU2 (F.e 2) (frameU2_e2_mem F))]
    · change b (x (F.e 3)) = x (b (F.e 3))
      rw [frameX1_fix_frameU2 F hx (frameU2_e3_mem F),
        frameX1_fix_frameU2 F hx (hbU2 (F.e 3) (frameU2_e3_mem F))]
    · change b (x (F.e 4)) = x (b (F.e 4))
      rw [frameB2_fix_frameW1 F hb (frameW1_e4_mem F),
        frameB2_fix_frameW1 F hb (hxW1 (F.e 4) (frameW1_e4_mem F))]
  exact LinearMap.congr_fun h v

private theorem frameB1_commutes_frameB2 (F : FrameData Q) :
    ∀ b ∈ frameB1 F, ∀ c ∈ frameB2 F, b * c = c * b := by
  intro b hb c hc
  have hbU1 : ∀ u ∈ frameU1 F, b u ∈ frameU1 F :=
    fun u hu => orthImage_maps (R := frameU1 F) hb hu
  have hcU2 : ∀ u ∈ frameU2 F, c u ∈ frameU2 F :=
    fun u hu => orthImage_maps (R := frameU2 F) hc hu
  apply LinearEquiv.ext
  intro v
  have h : ((b * c : V ≃ₗ[K] V) : V →ₗ[K] V) = ((c * b : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    apply F.e.ext
    intro i
    change (b * c) (F.e i) = (c * b) (F.e i)
    fin_cases i
    · change b (c (F.e 0)) = c (b (F.e 0))
      rw [frameB2_fix_frameW1 F hc (frameU1_le_frameW1 F (frameU1_e0_mem F)),
        frameB2_fix_frameW1 F hc (frameU1_le_frameW1 F (hbU1 (F.e 0) (frameU1_e0_mem F)))]
    · change b (c (F.e 1)) = c (b (F.e 1))
      rw [frameB2_fix_frameW1 F hc (frameU1_le_frameW1 F (frameU1_e1_mem F)),
        frameB2_fix_frameW1 F hc (frameU1_le_frameW1 F (hbU1 (F.e 1) (frameU1_e1_mem F)))]
    · change b (c (F.e 2)) = c (b (F.e 2))
      rw [frameB1_fix_frameW2 F hb
          (frameU2_le_frameW2 F (hcU2 (F.e 2) (frameU2_e2_mem F))),
        frameB1_fix_frameW2 F hb (frameU2_le_frameW2 F (frameU2_e2_mem F))]
    · change b (c (F.e 3)) = c (b (F.e 3))
      rw [frameB1_fix_frameW2 F hb
          (frameU2_le_frameW2 F (hcU2 (F.e 3) (frameU2_e3_mem F))),
        frameB1_fix_frameW2 F hb (frameU2_le_frameW2 F (frameU2_e3_mem F))]
    · change b (c (F.e 4)) = c (b (F.e 4))
      rw [frameB2_fix_frameW1 F hc (frameW1_e4_mem F),
        frameB1_fix_frameW2 F hb (frameW2_e4_mem F),
        frameB2_fix_frameW1 F hc (frameW1_e4_mem F)]
  exact LinearMap.congr_fun h v

private theorem frameO1_eq_sup_frameX1_frameB1 (F : FrameData Q) :
    frameO1 F = frameX1 F ⊔ frameB1 F :=
  le_antisymm (frameO1_le_sup_frameX1_frameB1 F)
    (sup_le (frameX1_le_frameO1 F) (frameB1_le_frameO1 F))

private theorem frameO2_eq_sup_frameX2_frameB2 (F : FrameData Q) :
    frameO2 F = frameX2 F ⊔ frameB2 F :=
  le_antisymm (frameO2_le_sup_frameX2_frameB2 F)
    (sup_le (frameX2_le_frameO2 F) (frameB2_le_frameO2 F))

private noncomputable def frameH (F : FrameData Q) : Subgroup (V ≃ₗ[K] V) :=
  frameX1 F ⊔ frameX2 F

private theorem frameB1_le_normalizer_frameX1 (F : FrameData Q) :
    frameB1 F ≤ Subgroup.normalizer (frameX1 F : Set (V ≃ₗ[K] V)) := by
  calc frameB1 F ≤ frameO1 F := frameB1_le_frameO1 F
    _ ≤ Subgroup.normalizer (frameX1 F : Set (V ≃ₗ[K] V)) := by
        rw [← commutator_frameO1_eq_frameX1 F]
        exact Subgroup.normalizer_commutator_ge_left (frameO1 F) (frameO1 F)

private theorem frameB2_le_normalizer_frameX2 (F : FrameData Q) :
    frameB2 F ≤ Subgroup.normalizer (frameX2 F : Set (V ≃ₗ[K] V)) := by
  calc frameB2 F ≤ frameO2 F := frameB2_le_frameO2 F
    _ ≤ Subgroup.normalizer (frameX2 F : Set (V ≃ₗ[K] V)) := by
        rw [← commutator_frameO2_eq_frameX2 F]
        exact Subgroup.normalizer_commutator_ge_left (frameO2 F) (frameO2 F)

private theorem frameB1_le_normalizer_frameX2 (F : FrameData Q) :
    frameB1 F ≤ Subgroup.normalizer (frameX2 F : Set (V ≃ₗ[K] V)) := by
  refine Subgroup.le_normalizer_iff.mpr ?_
  intro b hb x hx
  have hcomm : b * x = x * b := frameB1_centralizes_frameX2 F b hb x hx
  have hconj : b * x * b⁻¹ = x := by rw [hcomm]; group
  rwa [hconj]

private theorem frameB2_le_normalizer_frameX1 (F : FrameData Q) :
    frameB2 F ≤ Subgroup.normalizer (frameX1 F : Set (V ≃ₗ[K] V)) := by
  refine Subgroup.le_normalizer_iff.mpr ?_
  intro b hb x hx
  have hcomm : b * x = x * b := frameB2_centralizes_frameX1 F b hb x hx
  have hconj : b * x * b⁻¹ = x := by rw [hcomm]; group
  rwa [hconj]

private theorem frameB1_le_normalizer_frameH (F : FrameData Q) :
    frameB1 F ≤ Subgroup.normalizer (frameH F : Set (V ≃ₗ[K] V)) := by
  have h := le_inf (frameB1_le_normalizer_frameX1 F) (frameB1_le_normalizer_frameX2 F)
  refine h.trans ?_
  dsimp [frameH]
  exact Subgroup.inf_normalizer_le_normalizer_sup (frameX1 F) (frameX2 F)

private theorem frameB2_le_normalizer_frameH (F : FrameData Q) :
    frameB2 F ≤ Subgroup.normalizer (frameH F : Set (V ≃ₗ[K] V)) := by
  have h := le_inf (frameB2_le_normalizer_frameX1 F) (frameB2_le_normalizer_frameX2 F)
  refine h.trans ?_
  dsimp [frameH]
  exact Subgroup.inf_normalizer_le_normalizer_sup (frameX1 F) (frameX2 F)

private theorem frameX1_le_normalizer_frameH (F : FrameData Q) :
    frameX1 F ≤ Subgroup.normalizer (frameH F : Set (V ≃ₗ[K] V)) := by
  have h : frameX1 F ≤ frameH F := by dsimp [frameH]; exact le_sup_left
  exact h.trans Subgroup.le_normalizer

private theorem frameX2_le_normalizer_frameH (F : FrameData Q) :
    frameX2 F ≤ Subgroup.normalizer (frameH F : Set (V ≃ₗ[K] V)) := by
  have h : frameX2 F ≤ frameH F := by dsimp [frameH]; exact le_sup_right
  exact h.trans Subgroup.le_normalizer

private theorem frameO1_le_normalizer_frameH (F : FrameData Q) :
    frameO1 F ≤ Subgroup.normalizer (frameH F : Set (V ≃ₗ[K] V)) := by
  rw [frameO1_eq_sup_frameX1_frameB1 F]
  exact sup_le (frameX1_le_normalizer_frameH F) (frameB1_le_normalizer_frameH F)

private theorem frameO2_le_normalizer_frameH (F : FrameData Q) :
    frameO2 F ≤ Subgroup.normalizer (frameH F : Set (V ≃ₗ[K] V)) := by
  rw [frameO2_eq_sup_frameX2_frameB2 F]
  exact sup_le (frameX2_le_normalizer_frameH F) (frameB2_le_normalizer_frameH F)

private theorem frameO_le_normalizer_frameH (F : FrameData Q) (hq5 : 5 ≤ Nat.card K) :
    TauCeti.QuadraticMap.orthogonalGroup Q ≤
      Subgroup.normalizer (frameH F : Set (V ≃ₗ[K] V)) := by
  rw [← frameO1_sup_frameO2_eq_orthogonalGroup F hq5]
  exact sup_le (frameO1_le_normalizer_frameH F) (frameO2_le_normalizer_frameH F)

private theorem frameO_normalizes_frameH (F : FrameData Q) (hq5 : 5 ≤ Nat.card K) :
    ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ h ∈ frameH F,
      g * h * g⁻¹ ∈ frameH F :=
  Subgroup.le_normalizer_iff.mp (frameO_le_normalizer_frameH F hq5)

private theorem frameX1_le_orthDerived (F : FrameData Q) :
    frameX1 F ≤ CFSG.RankThree.Classical2.orthDerived Q := by
  change frameX1 F ≤
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆
  rw [← commutator_frameO1_eq_frameX1 F]
  exact Subgroup.commutator_mono (orthImage_le_orthogonalGroup (R := frameW1 F))
    (orthImage_le_orthogonalGroup (R := frameW1 F))

private theorem frameX2_le_orthDerived (F : FrameData Q) :
    frameX2 F ≤ CFSG.RankThree.Classical2.orthDerived Q := by
  change frameX2 F ≤
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆
  rw [← commutator_frameO2_eq_frameX2 F]
  exact Subgroup.commutator_mono (orthImage_le_orthogonalGroup (R := frameW2 F))
    (orthImage_le_orthogonalGroup (R := frameW2 F))

private theorem frameX1_sup_frameX2_eq_orthDerived (F : FrameData Q) (hq5 : 5 ≤ Nat.card K) :
    frameX1 F ⊔ frameX2 F = CFSG.RankThree.Classical2.orthDerived Q := by
  let O := TauCeti.QuadraticMap.orthogonalGroup Q
  let S : Set (V ≃ₗ[K] V) := (frameB1 F : Set (V ≃ₗ[K] V)) ∪
    (frameB2 F : Set (V ≃ₗ[K] V))
  let C : Subgroup (V ≃ₗ[K] V) := Subgroup.closure (S ∪ (frameH F : Set (V ≃ₗ[K] V)))
  have hB1C : frameB1 F ≤ C := by
    intro x hx
    exact Subgroup.subset_closure
      (Set.mem_union_left _ (Set.mem_union_left _ hx))
  have hB2C : frameB2 F ≤ C := by
    intro x hx
    exact Subgroup.subset_closure
      (Set.mem_union_left _ (Set.mem_union_right _ hx))
  have hHC : frameH F ≤ C := by
    intro x hx
    exact Subgroup.subset_closure (Set.mem_union_right _ hx)
  have hX1C : frameX1 F ≤ C := by
    have h : frameX1 F ≤ frameH F := by dsimp [frameH]; exact le_sup_left
    exact h.trans hHC
  have hX2C : frameX2 F ≤ C := by
    have h : frameX2 F ≤ frameH F := by dsimp [frameH]; exact le_sup_right
    exact h.trans hHC
  have hO1C : frameO1 F ≤ C := by
    rw [frameO1_eq_sup_frameX1_frameB1 F]
    exact sup_le hX1C hB1C
  have hO2C : frameO2 F ≤ C := by
    rw [frameO2_eq_sup_frameX2_frameB2 F]
    exact sup_le hX2C hB2C
  have hOC : O ≤ C := by
    dsimp [O]
    rw [← frameO1_sup_frameO2_eq_orthogonalGroup F hq5]
    exact sup_le hO1C hO2C
  have hDleO : CFSG.RankThree.Classical2.orthDerived Q ≤ O := by
    dsimp [CFSG.RankThree.Classical2.orthDerived, O]
    exact Subgroup.commutator_le_self _
  have hNO : frameH F ≤ O := by
    exact sup_le ((frameX1_le_orthDerived F).trans hDleO)
      ((frameX2_le_orthDerived F).trans hDleO)
  have hSO : S ⊆ O := by
    intro x hx
    rcases hx with hx | hx
    · exact orthImage_le_orthogonalGroup (R := frameW1 F) (frameB1_le_frameO1 F hx)
    · exact orthImage_le_orthogonalGroup (R := frameW2 F) (frameB2_le_frameO2 F hx)
  have hS : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ frameH F := by
    intro s hs t ht
    rcases hs with hs1 | hs2 <;> rcases ht with ht1 | ht2
    · have hle : ⁅frameB1 F, frameB1 F⁆ ≤ frameX1 F := by
        rw [← commutator_frameO1_eq_frameX1 F]
        exact Subgroup.commutator_mono (frameB1_le_frameO1 F) (frameB1_le_frameO1 F)
      have hmem : ⁅s, t⁆ ∈ frameX1 F := hle (Subgroup.commutator_mem_commutator hs1 ht1)
      exact (show frameX1 F ≤ frameH F from by dsimp [frameH]; exact le_sup_left) hmem
    · have hcomm : s * t = t * s := frameB1_commutes_frameB2 F s hs1 t ht2
      have hone : ⁅s, t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm
      rw [hone]
      exact (frameH F).one_mem
    · have hcomm : s * t = t * s := (frameB1_commutes_frameB2 F t ht1 s hs2).symm
      have hone : ⁅s, t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm
      rw [hone]
      exact (frameH F).one_mem
    · have hle : ⁅frameB2 F, frameB2 F⁆ ≤ frameX2 F := by
        rw [← commutator_frameO2_eq_frameX2 F]
        exact Subgroup.commutator_mono (frameB2_le_frameO2 F) (frameB2_le_frameO2 F)
      have hmem : ⁅s, t⁆ ∈ frameX2 F := hle (Subgroup.commutator_mem_commutator hs2 ht2)
      exact (show frameX2 F ≤ frameH F from by dsimp [frameH]; exact le_sup_right) hmem
  have hcommle : ⁅O, O⁆ ≤ frameH F :=
    commutator_le_of_le_closure
      (O := O) (N := frameH F) (S := S)
      (frameO_normalizes_frameH F hq5) hNO hSO hOC hS
  apply le_antisymm
  · exact sup_le (frameX1_le_orthDerived F) (frameX2_le_orthDerived F)
  · simpa [CFSG.RankThree.Classical2.orthDerived, O, frameH] using hcommle

theorem frameW2_eq_t_eigenspace (F : FrameData Q) :
    frameW2 F = Module.End.eigenspace (F.t : V →ₗ[K] V) 1 := by
  apply le_antisymm
  · rw [frameW2]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [Module.End.mem_eigenspace_iff]
  · intro v hv
    have hv' : F.t v = v := by simpa [Module.End.mem_eigenspace_iff] using hv
    obtain ⟨u1, hu1, u2, hu2, a, hvdecomp⟩ := frame_decompose F v
    have ht1 : F.t u1 = -u1 := t_negates_frameU1 F hu1
    have ht2 : F.t u2 = u2 := t_fixes_frameW2 F (frameU2_le_frameW2 F hu2)
    have ht4 : F.t (a • F.e 4) = a • F.e 4 :=
      t_fixes_frameW2 F
        (span_e4_le_frameW2 F (Submodule.smul_mem _ _ (Submodule.subset_span rfl)))
    have htv : F.t v = -u1 + u2 + a • F.e 4 := by
      rw [hvdecomp, map_add, map_add, ht1, ht2, ht4]
    have hEq : -u1 + u2 + a • F.e 4 = u1 + u2 + a • F.e 4 := by
      rw [← htv, hv', hvdecomp]
    have h' : -u1 + (u2 + a • F.e 4) = u1 + (u2 + a • F.e 4) := by
      simpa [add_assoc] using hEq
    have hneg : -u1 = u1 := add_right_cancel h'
    have h2u : (2 : K) • u1 = 0 := by
      calc (2 : K) • u1 = u1 + u1 := two_smul K u1
        _ = (-u1) + u1 := by rw [hneg]
        _ = 0 := neg_add_cancel u1
    have hu1zero : u1 = 0 := by
      rcases smul_eq_zero.mp h2u with h2 | h
      · exact absurd h2 F.two_ne_zero
      · exact h
    rw [hvdecomp, hu1zero, zero_add]
    exact Submodule.add_mem _ (frameU2_le_frameW2 F hu2)
      (span_e4_le_frameW2 F (Submodule.smul_mem _ _ (Submodule.subset_span rfl)))

private theorem s_maps_frameW2 (F : FrameData Q) {v : V} (hv : v ∈ frameW2 F) :
    F.s v ∈ frameW1 F := by
  rw [frameW2] at hv
  refine Submodule.span_induction (p := fun x _ => F.s x ∈ frameW1 F) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [F.s_e, frameW1_e0_mem, frameW1_e1_mem, frameW1_e4_mem]
  · simpa using (frameW1 F).zero_mem
  · intro a b ha hb hsa hsb
    simpa [map_add] using (frameW1 F).add_mem hsa hsb
  · intro c a ha hsa
    simpa [map_smul] using (frameW1 F).smul_mem c hsa

private theorem s_maps_frameW1 (F : FrameData Q) {v : V} (hv : v ∈ frameW1 F) :
    F.s v ∈ frameW2 F := by
  rw [frameW1] at hv
  refine Submodule.span_induction (p := fun x _ => F.s x ∈ frameW2 F) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [F.s_e, frameW2_e2_mem, frameW2_e3_mem, frameW2_e4_mem]
  · simpa using (frameW2 F).zero_mem
  · intro a b ha hb hsa hsb
    simpa [map_add] using (frameW2 F).add_mem hsa hsb
  · intro c a ha hsa
    simpa [map_smul] using (frameW2 F).smul_mem c hsa

private theorem s_inv_eq_self (F : FrameData Q) : F.s⁻¹ = F.s :=
  inv_eq_of_mul_eq_one_right F.s_mul_self

private theorem s_apply_apply (F : FrameData Q) (v : V) : F.s (F.s v) = v := by
  rw [← LinearEquiv.mul_apply, F.s_mul_self]
  rfl

private theorem s_orthPerp_frameW1 (F : FrameData Q) {w : V}
    (hw : w ∈ CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameW1 F)) :
    F.s w ∈ CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameW2 F) := by
  rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp] at hw ⊢
  intro v hv
  have hsv : F.s v ∈ frameW1 F := s_maps_frameW2 F hv
  have h := hw (F.s v) hsv
  have hp := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem F.s_mem v (F.s w)
  have hss : F.s (F.s w) = w := by
    rw [← LinearEquiv.mul_apply, F.s_mul_self]; rfl
  rw [hss] at hp
  rwa [← hp]

private theorem s_orthPerp_frameW2 (F : FrameData Q) {w : V}
    (hw : w ∈ CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameW2 F)) :
    F.s w ∈ CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameW1 F) := by
  rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_orthPerp] at hw ⊢
  intro v hv
  have hsv : F.s v ∈ frameW2 F := s_maps_frameW1 F hv
  have h := hw (F.s v) hsv
  have hp := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem F.s_mem v (F.s w)
  have hss : F.s (F.s w) = w := by
    rw [← LinearEquiv.mul_apply, F.s_mul_self]; rfl
  rw [hss] at hp
  rwa [← hp]

private theorem frameO2_map_conj_s (F : FrameData Q) :
    (frameO2 F).map (MulAut.conj F.s).toMonoidHom = frameO1 F := by
  apply le_antisymm
  · rintro b hb
    obtain ⟨a, ha, hba⟩ := Subgroup.mem_map.mp hb
    have hba' : b = F.s * a * F.s := by
      rw [← hba]
      simp [MulAut.conj_apply, s_inv_eq_self F]
    subst b
    have haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      orthImage_le_orthogonalGroup (R := frameW2 F) ha
    have hbO : F.s * a * F.s ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ F.s_mem haO) F.s_mem
    have h := mem_map_extendHom_of_preserves (R := frameW1 F) (frameW1_isCompl F)
      hbO ?_ ?_
    · rwa [map_extendHom_top (frameW1_isCompl F)] at h
    · intro r hr
      have hs : F.s r ∈ frameW2 F := s_maps_frameW1 F hr
      have hb : a (F.s r) ∈ frameW2 F := orthImage_maps (R := frameW2 F) ha hs
      simpa [LinearEquiv.mul_apply] using s_maps_frameW2 F hb
    · intro w hw
      have hsw : F.s w ∈ CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameW2 F) :=
        s_orthPerp_frameW1 F hw
      have hfix : a (F.s w) = F.s w := orthImage_fix (R := frameW2 F) ha hsw
      change F.s (a (F.s w)) = w
      rw [hfix, s_apply_apply F w]
  · intro b hb
    refine Subgroup.mem_map.mpr ⟨F.s * b * F.s, ?_, ?_⟩
    · have hbO : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
        orthImage_le_orthogonalGroup (R := frameW1 F) hb
      have hbO2 : F.s * b * F.s ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ F.s_mem hbO) F.s_mem
      have h := mem_map_extendHom_of_preserves (R := frameW2 F) (frameW2_isCompl F)
        hbO2 ?_ ?_
      · rwa [map_extendHom_top (frameW2_isCompl F)] at h
      · intro r hr
        have hs : F.s r ∈ frameW1 F := s_maps_frameW2 F hr
        have hb' : b (F.s r) ∈ frameW1 F := orthImage_maps (R := frameW1 F) hb hs
        simpa [LinearEquiv.mul_apply] using s_maps_frameW1 F hb'
      · intro w hw
        have hsw : F.s w ∈ CFSG.RankThree.PartOne.KCOrthogonal.orthPerp Q (frameW1 F) :=
          s_orthPerp_frameW2 F hw
        have hfix : b (F.s w) = F.s w := orthImage_fix (R := frameW1 F) hb hsw
        change F.s (b (F.s w)) = w
        rw [hfix, s_apply_apply F w]
    · change (MulAut.conj F.s) (F.s * b * F.s) = b
      rw [MulAut.conj_apply, s_inv_eq_self F]
      have h : F.s * (F.s * b * F.s) * F.s = b := by
        calc F.s * (F.s * b * F.s) * F.s
            = (F.s * F.s) * b * (F.s * F.s) := by group
          _ = b := by rw [F.s_mul_self]; simp
      exact h

private theorem frameX2_map_conj_s (F : FrameData Q) :
    (frameX2 F).map (MulAut.conj F.s).toMonoidHom = frameX1 F := by
  rw [← commutator_frameO2_eq_frameX2 F, ← commutator_frameO1_eq_frameX1 F,
    Subgroup.map_commutator, frameO2_map_conj_s F]

theorem supportedOrthDerived_frameW2_map_conj_s (F : FrameData Q) :
    (CFSG.RankThree.PartOne.KCOrthogonal.supportedOrthDerived Q (frameW2 F)).map
        (MulAut.conj F.s).toMonoidHom =
      CFSG.RankThree.PartOne.KCOrthogonal.supportedOrthDerived Q (frameW1 F) := by
  simpa [frameX1, frameX2] using frameX2_map_conj_s F

theorem supportedOrthDerived_sup_eq_orthDerived (F : FrameData Q)
    (hq5 : 5 ≤ Nat.card K) :
    CFSG.RankThree.PartOne.KCOrthogonal.supportedOrthDerived Q (frameW1 F) ⊔
        CFSG.RankThree.PartOne.KCOrthogonal.supportedOrthDerived Q (frameW2 F) =
      CFSG.RankThree.Classical2.orthDerived Q := by
  simpa [frameX1, frameX2] using frameX1_sup_frameX2_eq_orthDerived F hq5

theorem frameT_sup_frameX2_eq_frameT_sup_orthDerived (F : FrameData Q) (hq5 : 5 ≤ Nat.card K)
    (T : Subgroup (V ≃ₗ[K] V)) (hs : F.s ∈ T) :
    T ⊔ frameX2 F = T ⊔ CFSG.RankThree.Classical2.orthDerived Q := by
  apply le_antisymm
  · exact sup_le le_sup_left ((frameX2_le_orthDerived F).trans le_sup_right)
  · refine sup_le le_sup_left ?_
    have hX1le : frameX1 F ≤ T ⊔ frameX2 F := by
      rw [← frameX2_map_conj_s F]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      change F.s * y * F.s⁻¹ ∈ T ⊔ frameX2 F
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hs)
        (Subgroup.mem_sup_right hy)) (Subgroup.mem_sup_left (T.inv_mem hs))
    have hDle : frameX1 F ⊔ frameX2 F ≤ T ⊔ frameX2 F :=
      sup_le hX1le le_sup_right
    calc CFSG.RankThree.Classical2.orthDerived Q = frameX1 F ⊔ frameX2 F := by
          rw [frameX1_sup_frameX2_eq_orthDerived F hq5]
      _ ≤ T ⊔ frameX2 F := hDle

theorem frameT_sup_frameX2_eq_of_derived_sup_eq (F : FrameData Q) (hq5 : 5 ≤ Nat.card K)
    {G T : Subgroup (V ≃ₗ[K] V)} (hs : F.s ∈ T)
    (hGen : CFSG.RankThree.Classical2.orthDerived Q ⊔ T = G) :
    T ⊔ frameX2 F = G := by
  rw [frameT_sup_frameX2_eq_frameT_sup_orthDerived F hq5 T hs]
  rw [sup_comm]
  exact hGen

theorem frameT_sup_frameX1_eq_frameT_sup_orthDerived (F : FrameData Q) (hq5 : 5 ≤ Nat.card K)
    (T : Subgroup (V ≃ₗ[K] V)) (hs : F.s ∈ T) :
    T ⊔ frameX1 F = T ⊔ CFSG.RankThree.Classical2.orthDerived Q := by
  apply le_antisymm
  · exact sup_le le_sup_left ((frameX1_le_orthDerived F).trans le_sup_right)
  · refine sup_le le_sup_left ?_
    have hX2le : frameX2 F ≤ T ⊔ frameX1 F := by
      intro x hx
      have hxmap : (MulAut.conj F.s) x ∈ frameX1 F := by
        rw [← frameX2_map_conj_s F]
        exact Subgroup.mem_map_of_mem _ hx
      have hconj : F.s * x * F.s ∈ frameX1 F := by
        simpa [MulAut.conj_apply, s_inv_eq_self F] using hxmap
      have hx_eq : x = F.s * (F.s * x * F.s) * F.s := by
        calc x = (F.s * F.s) * x * (F.s * F.s) := by rw [F.s_mul_self]; simp
          _ = F.s * (F.s * x * F.s) * F.s := by group
      rw [hx_eq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hs)
        (Subgroup.mem_sup_right hconj)) (Subgroup.mem_sup_left hs)
    have hDle : frameX1 F ⊔ frameX2 F ≤ T ⊔ frameX1 F :=
      sup_le le_sup_right hX2le
    calc CFSG.RankThree.Classical2.orthDerived Q = frameX1 F ⊔ frameX2 F := by
          rw [frameX1_sup_frameX2_eq_orthDerived F hq5]
      _ ≤ T ⊔ frameX1 F := hDle

theorem frameT_sup_frameX1_eq_of_derived_sup_eq (F : FrameData Q) (hq5 : 5 ≤ Nat.card K)
    {G T : Subgroup (V ≃ₗ[K] V)} (hs : F.s ∈ T)
    (hGen : CFSG.RankThree.Classical2.orthDerived Q ⊔ T = G) :
    T ⊔ frameX1 F = G := by
  rw [frameT_sup_frameX1_eq_frameT_sup_orthDerived F hq5 T hs]
  rw [sup_comm]
  exact hGen

end CFSG.ClassicalGroups.Orthogonal