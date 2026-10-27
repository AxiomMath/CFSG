module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineHexagonLocal
public import CFSG.GroupTheory.InvolutionHexagonCycles

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

variable {F : Type} [Field F]

@[expose] def incGraph (F : Type) [Field F] : SimpleGraph (NonisoLine F ⊕ HexLine F) :=
  SimpleGraph.fromRel fun a b => ∃ p T, a = Sum.inl p ∧ b = Sum.inr T ∧ p ∈ T.1

@[simp] theorem incGraph_adj_inl_inr (p : NonisoLine F) (T : HexLine F) :
    (incGraph F).Adj (Sum.inl p) (Sum.inr T) ↔ p ∈ T.1 := by
  rw [incGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨p', T', hp, hT, hpT⟩ | ⟨p', T', hp, -, -⟩⟩
    · cases hp
      cases hT
      exact hpT
    · cases hp
  · intro hpT
    exact ⟨Sum.inl_ne_inr, Or.inl ⟨p, T, rfl, rfl, hpT⟩⟩

@[simp] theorem incGraph_adj_inr_inl (T : HexLine F) (p : NonisoLine F) :
    (incGraph F).Adj (Sum.inr T) (Sum.inl p) ↔ p ∈ T.1 := by
  rw [SimpleGraph.adj_comm, incGraph_adj_inl_inr]

@[simp] theorem not_incGraph_adj_inl_inl (p q : NonisoLine F) :
    ¬ (incGraph F).Adj (Sum.inl p) (Sum.inl q) := by
  rw [incGraph, SimpleGraph.fromRel_adj]
  rintro ⟨-, ⟨p', T', -, hT, -⟩ | ⟨p', T', -, hT, -⟩⟩ <;> cases hT

@[simp] theorem not_incGraph_adj_inr_inr (T T' : HexLine F) :
    ¬ (incGraph F).Adj (Sum.inr T) (Sum.inr T') := by
  rw [incGraph, SimpleGraph.fromRel_adj]
  rintro ⟨-, ⟨p', T'', hp, -, -⟩ | ⟨p', T'', hp, -, -⟩⟩ <;> cases hp

@[expose] def incColoring (F : Type) [Field F] : (incGraph F).Coloring Bool :=
  SimpleGraph.Coloring.mk (fun v => v.isRight) (by
    rintro (p | T) (q | T') hadj
    · exact absurd hadj (not_incGraph_adj_inl_inl p q)
    · exact Bool.false_ne_true
    · exact Bool.false_ne_true.symm
    · exact absurd hadj (not_incGraph_adj_inr_inr T T'))

@[simp] theorem incColoring_apply (v : NonisoLine F ⊕ HexLine F) :
    incColoring F v = v.isRight :=
  rfl

theorem neighborSet_inl (p : NonisoLine F) :
    (incGraph F).neighborSet (Sum.inl p) = Sum.inr '' {T : HexLine F | p ∈ T.1} := by
  ext v
  rw [SimpleGraph.mem_neighborSet, Set.mem_image]
  rcases v with q | T
  · constructor
    · intro hadj
      exact absurd hadj (not_incGraph_adj_inl_inl p q)
    · rintro ⟨T, -, hT⟩
      exact absurd hT Sum.inr_ne_inl
  · rw [incGraph_adj_inl_inr]
    constructor
    · intro hpT
      exact ⟨T, hpT, rfl⟩
    · rintro ⟨T', hpT', hT'⟩
      cases hT'
      exact hpT'

theorem neighborSet_inr (T : HexLine F) :
    (incGraph F).neighborSet (Sum.inr T) = Sum.inl '' (T.1 : Set (NonisoLine F)) := by
  ext v
  rw [SimpleGraph.mem_neighborSet, Set.mem_image]
  rcases v with q | T'
  · rw [incGraph_adj_inr_inl]
    constructor
    · intro hqT
      exact ⟨q, hqT, rfl⟩
    · rintro ⟨q', hq'T, hq'⟩
      cases hq'
      exact hq'T
  · constructor
    · intro hadj
      exact absurd hadj (not_incGraph_adj_inr_inr T T')
    · rintro ⟨q, -, hq⟩
      exact absurd hq Sum.inl_ne_inr

theorem ncard_neighborSet_inl (hF : Nat.card F = 9) (p : NonisoLine F) :
    ((incGraph F).neighborSet (Sum.inl p)).ncard = 3 := by
  rw [neighborSet_inl, Set.ncard_image_of_injective _ Sum.inr_injective, ncard_lines_through hF]

theorem ncard_neighborSet_inr (T : HexLine F) :
    ((incGraph F).neighborSet (Sum.inr T)).ncard = 3 := by
  rw [neighborSet_inr, Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_coe_finset,
    T.2.1]

theorem ncard_neighborSet (hF : Nat.card F = 9) (v : NonisoLine F ⊕ HexLine F) :
    ((incGraph F).neighborSet v).ncard = 3 := by
  rcases v with p | T
  · exact ncard_neighborSet_inl hF p
  · exact ncard_neighborSet_inr T

theorem card_incGraph_vertices (hF : Nat.card F = 9) :
    Nat.card (NonisoLine F ⊕ HexLine F) = 126 := by
  have := finite_nonisoLine hF
  have := finite_hexLine hF
  rw [Nat.card_sum, card_nonisoLine hF, card_hexLine hF]

open CFSG.GroupTheory.InvolutionHexagon in
theorem collinear_iff_orth (hF : Nat.card F = 9) {a b : NonisoLine F} (hab : a ≠ b) :
    Collinear (fun (p : NonisoLine F) (T : HexLine F) => p ∈ T.1) a b ↔ Orth a b := by
  constructor
  · rintro ⟨T, ha, hb⟩
    exact orth_of_mem T ha hb hab
  · exact exists_line hF

open CFSG.GroupTheory.InvolutionHexagon in
theorem hexagonData (hF : Nat.card F = 9) :
    HexagonData (fun (p : NonisoLine F) (T : HexLine F) => p ∈ T.1) where
  finite_points := finite_nonisoLine hF
  finite_lines := finite_hexLine hF
  card_points := card_nonisoLine hF
  ncard_points T := (Set.ncard_coe_finset T.1).trans T.2.1
  ncard_lines := ncard_lines_through hF
  eq_of_inc hpq hp hq hp' hq' := eq_of_mem_of_mem hF hpq hp hq hp' hq'
  exists_inc_of_triangle {a b c} hab hbc hac hcab hcbc hcac := by
    obtain ⟨T, ha, hb⟩ := hcab
    refine ⟨T, ha, hb, (mem_line_iff hF hab ha hb c).mpr (Or.inr (Or.inr ⟨?_, ?_⟩))⟩
    · exact (collinear_iff_orth hF hac).mp hcac
    · exact (collinear_iff_orth hF hbc).mp hcbc
  not_square := by
    rintro ⟨a, b, c, d, hnd, hab, hbc, hcd, hda, hac, hbd⟩
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true] at hnd'
    obtain ⟨⟨hab', hac', had'⟩, ⟨hbc', hbd'⟩, hcd'⟩ := hnd'
    exact not_exists_orth_square hF ⟨a, b, c, d, hnd, (collinear_iff_orth hF hab').mp hab,
      (collinear_iff_orth hF hbc').mp hbc, (collinear_iff_orth hF hcd').mp hcd,
      (collinear_iff_orth hF (Ne.symm had')).mp hda,
      fun h => hac ((collinear_iff_orth hF hac').mpr h),
      fun h => hbd ((collinear_iff_orth hF hbd').mpr h)⟩
  not_pentagon := by
    rintro ⟨a, b, c, d, e, hnd, hab, hbc, hcd, hde, hea, hac, had, hbd, hbe, hce⟩
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true] at hnd'
    obtain ⟨⟨hab', hac', had', hae'⟩, ⟨hbc', hbd', hbe'⟩, ⟨hcd', hce'⟩, hde'⟩ := hnd'
    exact not_exists_orth_pentagon hF ⟨a, b, c, d, e, hnd, (collinear_iff_orth hF hab').mp hab,
      (collinear_iff_orth hF hbc').mp hbc, (collinear_iff_orth hF hcd').mp hcd,
      (collinear_iff_orth hF hde').mp hde, (collinear_iff_orth hF (Ne.symm hae')).mp hea,
      fun h => hac ((collinear_iff_orth hF hac').mpr h),
      fun h => had ((collinear_iff_orth hF had').mpr h),
      fun h => hbd ((collinear_iff_orth hF hbd').mpr h),
      fun h => hbe ((collinear_iff_orth hF hbe').mpr h),
      fun h => hce ((collinear_iff_orth hF hce').mpr h)⟩

theorem getVert_inl_or_inr {p₀ : NonisoLine F} {v : NonisoLine F ⊕ HexLine F}
    (c : (incGraph F).Walk (Sum.inl p₀) v) (i : ℕ) (hi : i ≤ c.length) :
    (Even i → ∃ p, c.getVert i = Sum.inl p) ∧ (Odd i → ∃ T, c.getVert i = Sum.inr T) :=
  CFSG.GroupTheory.InvolutionHexagon.getVert_inl_or_inr
    (inc := fun (p : NonisoLine F) (T : HexLine F) => p ∈ T.1) c i hi

theorem twelve_le_length_of_inl (hF : Nat.card F = 9) {p₀ : NonisoLine F}
    (c : (incGraph F).Walk (Sum.inl p₀) (Sum.inl p₀)) (hc : c.IsCycle) : 12 ≤ c.length :=
  (hexagonData hF).twelve_le_length_of_inl c hc

theorem twelve_le_length (hF : Nat.card F = 9) {v : NonisoLine F ⊕ HexLine F}
    (c : (incGraph F).Walk v v) (hc : c.IsCycle) : 12 ≤ c.length :=
  (hexagonData hF).twelve_le_length c hc

end CFSG.LinearGroups.UnitaryThreeOverNine
