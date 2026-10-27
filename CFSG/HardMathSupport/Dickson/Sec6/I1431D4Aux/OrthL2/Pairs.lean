module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Hyp
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Image
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Struct

public section


namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge (Coord)

section Span

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem linearIndependent_pairs {A B : HypPair Q} (h : A.Orth B) :
    LinearIndependent K ![A.e, A.f, B.e, B.f] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_four] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hg
  have hef := A.polar_ef
  have hfe := A.polar_fe
  have hef' := B.polar_ef
  have hfe' := B.polar_fe
  have h1 := h.ee
  have h2 := h.ef
  have h3 := h.fe
  have h4 := h.ff
  have h1' : polar Q B.e A.e = 0 := by rw [polar_comm, h1]
  have h2' : polar Q B.f A.e = 0 := by rw [polar_comm, h2]
  have h3' : polar Q B.e A.f = 0 := by rw [polar_comm, h3]
  have h4' : polar Q B.f A.f = 0 := by rw [polar_comm, h4]
  have e1 := congrArg (fun z => polar Q z A.f) hg
  have e2 := congrArg (fun z => polar Q z A.e) hg
  have e3 := congrArg (fun z => polar Q z B.f) hg
  have e4 := congrArg (fun z => polar Q z B.e) hg
  simp only [polar_add_left, polar_smul_left_eq, polar_zero_left, hef, hfe, hef', hfe', h1, h2, h3,
    h4, h1', h2', h3', h4', A.polar_ee, A.polar_ff, B.polar_ee, B.polar_ff] at e1 e2 e3 e4
  intro i
  fin_cases i
  · simpa using e1
  · simpa using e2
  · simpa using e3
  · simpa using e4

theorem range_pairs (A B : HypPair Q) :
    Set.range ![A.e, A.f, B.e, B.f] = {A.e, A.f, B.e, B.f} := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

theorem finrank_span_pairs {A B : HypPair Q} (h : A.Orth B) :
    finrank K (Submodule.span K {A.e, A.f, B.e, B.f}) = 4 := by
  have h1 := finrank_span_eq_card (linearIndependent_pairs h)
  rw [range_pairs] at h1
  simpa using h1

theorem polar_eq_zero_of_mem_span_span {S T : Set V} (h : ∀ a ∈ S, ∀ b ∈ T, polar Q a b = 0)
    {a b : V} (ha : a ∈ Submodule.span K S) (hb : b ∈ Submodule.span K T) : polar Q a b = 0 := by
  have step1 : ∀ a ∈ Submodule.span K S, ∀ b ∈ T, polar Q a b = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact fun b hb => h a ha b hb
    | zero => exact fun b _ => polar_zero_left Q b
    | add a a' _ _ ha ha' => exact fun b hb => by rw [polar_add_left, ha b hb, ha' b hb, add_zero]
    | smul c a _ ha => exact fun b hb => by rw [polar_smul_left_eq, ha b hb, mul_zero]
  induction hb using Submodule.span_induction with
  | mem b hb => exact step1 a ha b hb
  | zero => exact polar_zero_right Q a
  | add b b' _ _ hb hb' => rw [polar_add_right, hb, hb', add_zero]
  | smul c b _ hb => rw [polar_smul_right_eq, hb, mul_zero]

end Span

section Fixed

variable (K : Type) [Field K] [Finite K]

theorem exists_fixed_pairs (T2 : LeviSelfDual K) {y : (Coord → K) ≃ₗ[K] (Coord → K)}
    (hy : OddOrderIsometry (quadPlus 4 K) 3 y) (hw : finrank K (fixedSpace y) = 4) :
    ∃ A B : HypPair (quadPlus 4 K), A.Orth B ∧
      Submodule.span K {A.e, A.f, B.e, B.f} = fixedSpace y := by
  classical
  have hQ := nondegenerate_quadPlus_four K
  obtain ⟨hcompl, horth⟩ := hy.fixed_others
  have hdimV : finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by simp
  have hdimO : finrank K (othersSpace y.toLinearMap (X - 1)) = 4 := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    have h' : finrank K (fixedSpace y) + finrank K (othersSpace y.toLinearMap (X - 1)) =
        finrank K (Fin 4 ⊕ Fin 4 → K) := h
    omega
  obtain ⟨h₀, hh₀, hne1⟩ : ∃ h₀ ∈ primaryFactors y.toLinearMap, h₀ ≠ X - 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : othersSpace y.toLinearMap (X - 1) = ⊥ := by
      unfold othersSpace
      refine iSup_eq_bot.2 fun k => iSup_eq_bot.2 fun hk => ?_
      exact absurd (hcon k hk.1) hk.2.1
    rw [hbot, finrank_bot] at hdimO
    omega
  have hO := othersSpace_eq_orbitSpace hy hh₀ hne1
  have hm : primaryMultiplicity y.toLinearMap h₀ = 2 := by
    have := finrank_orbitSpace hy hh₀ hne1
    rw [← hO, hdimO] at this
    omega
  obtain ⟨A, B, hAB, hAspan⟩ : ∃ A B : HypPair (quadPlus 4 K), A.Orth B ∧
      Submodule.span K {A.e, A.f, B.e, B.f} = orbitSpace y.toLinearMap h₀ := by
    by_cases hself : h₀ = reciprocalPolynomial h₀
    · obtain ⟨A, B, hAB, hsp, -⟩ := T2 y hy hh₀ hne1 hself hm
      exact ⟨A, B, hAB, hsp⟩
    · obtain ⟨A, B, hAB, hsp, -⟩ := specialBlock_eq_levi_paired hQ hy hh₀ hne1 hself hm
      exact ⟨A, B, hAB, hsp⟩
  obtain ⟨g, hg, h1, h2, h3, h4⟩ := exists_mem_elementaryGroup_two hQ
    (stdPair_orth K (show (0 : Fin 4) ≠ 1 by decide))
    (stdPair_orth K (show (0 : Fin 4) ≠ 2 by decide))
    (stdPair_orth K (show (1 : Fin 4) ≠ 2 by decide)) hAB
  have hgO := elementaryGroup_le_orthogonalGroup (quadPlus 4 K) hg
  set A' := hypPairMap hgO (stdPair K 2) with hA'
  set B' := hypPairMap hgO (stdPair K 3) with hB'
  have hA'B' : A'.Orth B' := orth_hypPairMap hgO (stdPair_orth K (show (2 : Fin 4) ≠ 3 by decide))
  refine ⟨A', B', hA'B', ?_⟩
  set O := othersSpace y.toLinearMap (X - 1) with hOdef
  have hOspan : O = Submodule.span K {A.e, A.f, B.e, B.f} := by rw [hO, hAspan]
  have hgens : ∀ a ∈ ({A.e, A.f, B.e, B.f} : Set (Coord → K)),
      ∀ b ∈ ({A'.e, A'.f, B'.e, B'.f} : Set (Coord → K)), polar (quadPlus 4 K) a b = 0 := by
    have o02 := stdPair_orth K (show (0 : Fin 4) ≠ 2 by decide)
    have o03 := stdPair_orth K (show (0 : Fin 4) ≠ 3 by decide)
    have o12 := stdPair_orth K (show (1 : Fin 4) ≠ 2 by decide)
    have o13 := stdPair_orth K (show (1 : Fin 4) ≠ 3 by decide)
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [hA', hB', hypPairMap, ← h1, ← h2, ← h3, ← h4, polar_map_of_mem hgO] <;>
      first | exact o02.ee | exact o02.ef | exact o02.fe | exact o02.ff |
        exact o03.ee | exact o03.ef | exact o03.fe | exact o03.ff |
        exact o12.ee | exact o12.ef | exact o12.fe | exact o12.ff |
        exact o13.ee | exact o13.ef | exact o13.fe | exact o13.ff
  have hU'le : Submodule.span K {A'.e, A'.f, B'.e, B'.f} ≤
      LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 4 K)) O := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro o ho
    rw [hOspan] at ho
    exact polar_eq_zero_of_mem_span_span hgens ho hu
  have hWle : fixedSpace y ≤ LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 4 K)) O := by
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro o ho
    show polar (quadPlus 4 K) o w = 0
    rw [polar_comm]
    exact horth w hw o ho
  have hfo : finrank K (LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 4 K)) O) = 4 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, hdimV, hdimO]
  have hU'W : Submodule.span K {A'.e, A'.f, B'.e, B'.f} =
      LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 4 K)) O :=
    Submodule.eq_of_le_of_finrank_eq hU'le (by rw [finrank_span_pairs hA'B', hfo])
  have hWO : fixedSpace y = LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 4 K)) O :=
    Submodule.eq_of_le_of_finrank_eq hWle (by rw [hw, hfo])
  rw [hU'W, hWO]

end Fixed

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
