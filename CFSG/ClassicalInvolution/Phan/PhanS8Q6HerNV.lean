module

public import CFSG.ClassicalInvolution.Phan.PhanS8Q2Basic
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K] {M : Model K}

theorem tauV_zero : tauV M (0 : Vec K) = 0 := by
  funext s
  rcases s with i | i | u <;> simp [tauV]

theorem exists_her_ne {x : Fin 4 → Vec K} (hx : GramInj M x) {i j : Fin 4}
    (hij : gram M (x i) (x j) ≠ 0) :
    ∃ u ∈ orthSpan M (Set.range x), ∃ u' ∈ orthSpan M (Set.range x), her M u u' ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set Z := orthSpan M (Set.range x) with hZdef
  have hZ3 : Module.finrank K Z = 3 := hx.finrank_orth
  let b : Module.Basis (Fin 3) K Z := Module.finBasisOfFinrankEq K Z hZ3
  let s : Fin 3 → Vec K := fun l => tauV M ((b l : Z) : Vec K)
  have hs_mem : ∀ l, s l ∈ Submodule.span K (Set.range x) := fun l => by
    refine mem_span_of_forall_orth M fun z hz => ?_
    rw [bf_comm]
    have := hcon z hz ((b l : Z) : Vec K) (b l).2
    simpa [her, s] using this
  have hs_her : ∀ l m, her M (s l) (x m) = 0 := fun l m => by
    have h1 : bf M (x m) ((b l : Z) : Vec K) = 0 := (mem_orthSpan M).1 (b l).2 (x m) ⟨m, rfl⟩
    simp only [her, s]
    rw [bf_tauV, bf_comm, h1, map_zero]
  let f : Fin 5 → Vec K := ![s 0, s 1, s 2, x i, x j]
  have hf_mem : ∀ l, f l ∈ Submodule.span K (Set.range x) := by
    intro l
    fin_cases l
    · exact hs_mem 0
    · exact hs_mem 1
    · exact hs_mem 2
    · exact Submodule.subset_span ⟨i, rfl⟩
    · exact Submodule.subset_span ⟨j, rfl⟩
  let g : Fin 5 → Submodule.span K (Set.range x) := fun l => ⟨f l, hf_mem l⟩
  have hg : ¬ LinearIndependent K g := by
    intro hli
    have h5 := hli.fintype_card_le_finrank
    have h4 : Module.finrank K (Submodule.span K (Set.range x)) ≤ 4 := by
      have h := finrank_range_le_card (R := K) x
      rw [Set.finrank] at h
      simpa using h
    simp at h5
    omega
  obtain ⟨α, hα, l₀, hl₀⟩ := Fintype.not_linearIndependent_iff.1 hg
  have hrel : α 0 • s 0 + α 1 • s 1 + α 2 • s 2 + α 3 • x i + α 4 • x j = 0 := by
    have := congrArg Subtype.val hα
    simp only [Fin.sum_univ_five, Submodule.coe_add, Submodule.coe_smul, g, f] at this
    simpa using this
  have e1 : α 3 * her M (x i) (x i) + α 4 * her M (x j) (x i) = 0 := by
    have := congrArg (fun w => her M w (x i)) hrel
    simp only [her_add_left, her_smul_left, hs_her] at this
    have h0 : her M 0 (x i) = 0 := by simp [her, bf_zero_left]
    simpa [h0] using this
  have e2 : α 3 * her M (x i) (x j) + α 4 * her M (x j) (x j) = 0 := by
    have := congrArg (fun w => her M w (x j)) hrel
    simp only [her_add_left, her_smul_left, hs_her] at this
    have h0 : her M 0 (x j) = 0 := by simp [her, bf_zero_left]
    simpa [h0] using this
  have hα3 : α 3 = 0 := by
    have h1 : α 3 * gram M (x i) (x j) = 0 := by
      unfold gram
      linear_combination (her M (x j) (x j)) * e1 - (her M (x j) (x i)) * e2
    exact (mul_eq_zero.1 h1).resolve_right hij
  have hα4 : α 4 = 0 := by
    have h1 : α 4 * gram M (x i) (x j) = 0 := by
      unfold gram
      linear_combination (her M (x i) (x i)) * e2 - (her M (x i) (x j)) * e1
    exact (mul_eq_zero.1 h1).resolve_right hij
  rw [hα3, hα4, zero_smul, zero_smul, add_zero, add_zero] at hrel
  have hconj : M.τ (α 0) • (b 0 : Vec K) + M.τ (α 1) • (b 1 : Vec K) +
      M.τ (α 2) • (b 2 : Vec K) = 0 := by
    have := congrArg (tauV M) hrel
    simp only [tauV_add, tauV_smul, tauV_zero, s, tauV_tauV] at this
    exact this
  have hβ : ∀ l, ![M.τ (α 0), M.τ (α 1), M.τ (α 2)] l = 0 := by
    refine Fintype.linearIndependent_iff.1 b.linearIndependent
      ![M.τ (α 0), M.τ (α 1), M.τ (α 2)] ?_
    apply Subtype.ext
    simpa [Fin.sum_univ_three] using hconj
  have hα0 : α 0 = 0 := by simpa using hβ 0
  have hα1 : α 1 = 0 := by simpa using hβ 1
  have hα2 : α 2 = 0 := by simpa using hβ 2
  fin_cases l₀ <;> simp_all

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q
