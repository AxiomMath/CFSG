module

public import Certificates.Data.S7Q8
public import Mathlib.Algebra.BigOperators.Group.List.Basic

public section

namespace Certificates.S7Q8

open Certificates.S5Rows

section Map

variable {M N : Type*} [Group M] [DecidableEq M] [Group N] [DecidableEq N] (f : M →* N)
  (hf : Function.Injective f)

theorem q8Span_map (i j : M) : q8Span (f i) (f j) = (q8Span i j).map f := by
  simp only [q8Span, List.map_cons, List.map_nil, map_one, map_pow, map_inv, map_mul]

include hf

theorem decide_mem_map (x : M) (l : List M) : decide (f x ∈ l.map f) = decide (x ∈ l) := by
  simp only [List.mem_map_of_injective hf]

theorem q8RelB_map (i j : M) : q8RelB (f i) (f j) = q8RelB i j := by
  simp only [q8RelB, ← map_pow, ← map_inv, ← map_mul, ← map_one f, hf.eq_iff]

theorem inSpanB_map (i j x : M) : inSpanB (f i) (f j) (f x) = inSpanB i j x := by
  rw [inSpanB, inSpanB, q8Span_map, decide_mem_map f hf]

theorem normB_map (i j g : M) : normB (f i) (f j) (f g) = normB i j g := by
  simp only [normB, ← map_inv, ← map_mul, inSpanB_map f hf]

theorem ord4B_map (u : M) : ord4B (f u) = ord4B u := by
  simp only [ord4B, ← map_mul, ← map_one f, hf.eq_iff]

theorem normVB_map (z w a : M) : normVB (f z) (f w) (f a) = normVB z w a := by
  simp only [normVB, List.mem_cons, List.not_mem_nil, or_false, ← map_inv, ← map_mul,
    ← map_one f, hf.eq_iff]

theorem classStepB_map (i j u x : M) :
    classStepB (f i) (f j) (f u) (f x) = classStepB i j u x := by
  simp only [classStepB, ← map_inv, ← map_mul, hf.eq_iff, inSpanB_map f hf, normB_map f hf,
    normVB_map f hf, q8Span_map, List.any_map, Function.comp_def]

theorem classCheck_map (i j : M) (S X : List M) :
    classCheck (f i) (f j) (S.map f) (X.map f) = classCheck i j S X := by
  simp only [classCheck, List.all_map, List.any_map, Function.comp_def, ord4B_map f hf,
    classStepB_map f hf]

theorem normAllB_map (i j : M) (C : List M) : normAllB (f i) (f j) (C.map f) = normAllB i j C := by
  simp only [normAllB, List.all_map, Function.comp_def, normB_map f hf]

theorem q8InCheck_map (L : List M) (i₁ j₁ i₂ j₂ : M) :
    q8InCheck (L.map f) (f i₁) (f j₁) (f i₂) (f j₂) = q8InCheck L i₁ j₁ i₂ j₂ := by
  simp only [q8InCheck, List.all_map, Function.comp_def, q8RelB_map f hf, inSpanB_map f hf]

theorem edgeB_map (i₁ j₁ i₂ j₂ e : M) :
    edgeB (f i₁) (f j₁) (f i₂) (f j₂) (f e) = edgeB i₁ j₁ i₂ j₂ e := by
  simp only [edgeB, ← map_inv, ← map_mul, q8Span_map, List.any_map, Function.comp_def,
    ord4B_map f hf, normB_map f hf]

theorem factB_map (i₁ j₁ i₂ j₂ : M) (E : List M) (g : M) (fs : List M) :
    factB (f i₁) (f j₁) (f i₂) (f j₂) (E.map f) (f g) (fs.map f) = factB i₁ j₁ i₂ j₂ E g fs := by
  simp only [factB, ← map_list_prod, hf.eq_iff, List.all_map, Function.comp_def, ← map_inv,
    decide_mem_map f hf, normB_map f hf]

theorem threeCycB_map (y i j : M) : threeCycB (f y) (f i) (f j) = threeCycB y i j := by
  simp only [threeCycB, ← map_inv, ← map_mul, hf.eq_iff]

theorem threeCycCheck_map (L Y : List M) (p : N → Bool) :
    threeCycCheck (L.map f) (Y.map f) p = threeCycCheck L Y fun x => p (f x) := by
  simp only [threeCycCheck, List.all_map, List.any_map, Function.comp_def, q8RelB_map f hf,
    threeCycB_map f hf]

theorem invPairB_map (g : N → ℕ) (u x i j : M) :
    invPairB g (f u) (f x) (f i) (f j) = invPairB (fun y => g (f y)) u x i j := by
  simp only [invPairB, ← map_inv, ← map_mul, ← map_one f, hf.eq_iff, q8Span_map,
    decide_mem_map f hf]

theorem invPairCheck_map (L : List M) (g : N → ℕ) :
    invPairCheck (L.map f) g = invPairCheck L fun y => g (f y) := by
  simp only [invPairCheck, List.all_map, List.any_map, Function.comp_def, q8RelB_map f hf,
    q8Span_map, invPairB_map f hf]

end Map

section Filter

variable {M : Type*} [Group M] [DecidableEq M]

theorem ord4B_of_q8RelB {a b : M} (h : q8RelB a b = true) : ord4B a = true ∧ ord4B b = true := by
  simp only [q8RelB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨h4, h2⟩, hab⟩, -⟩ := h
  have ha4 : a * a * (a * a) = 1 := by
    rw [← h4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have ha2 : ¬ a * a = 1 := by rwa [← sq]
  have hb2 : b * b = a * a := by rw [← sq, ← sq, hab]
  simp only [ord4B, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, hb2]
  exact ⟨⟨ha4, ha2⟩, ha4, ha2⟩

theorem all_all_filter_ord4 (L : List M) (P : M → M → Bool)
    (hP : ∀ a b, (ord4B a && ord4B b) = false → P a b = true) :
    ((L.filter ord4B).all fun a => (L.filter ord4B).all fun b => P a b) =
      L.all fun a => L.all fun b => P a b := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_filter]
  constructor
  · intro h a ha b hb
    by_cases hab : (ord4B a && ord4B b) = true
    · rw [Bool.and_eq_true] at hab
      exact h a ⟨ha, hab.1⟩ b ⟨hb, hab.2⟩
    · exact hP a b (by simpa using hab)
  · intro h a ha b hb
    exact h a ha.1 b hb.1

theorem q8InCheck_filter_ord4 (L : List M) (i₁ j₁ i₂ j₂ : M) :
    q8InCheck (L.filter ord4B) i₁ j₁ i₂ j₂ = q8InCheck L i₁ j₁ i₂ j₂ := by
  refine all_all_filter_ord4 L _ fun a b hab => ?_
  have hq : q8RelB a b = false := by
    by_contra hq
    obtain ⟨h1, h2⟩ := ord4B_of_q8RelB (Bool.eq_true_of_ne_false hq)
    rw [h1, h2] at hab
    exact Bool.noConfusion hab
  rw [hq]
  rfl

theorem threeCycCheck_filter_ord4 (L Y : List M) (p : M → Bool) :
    threeCycCheck (L.filter ord4B) Y p = threeCycCheck L Y p := by
  refine all_all_filter_ord4 L _ fun a b hab => ?_
  have hq : q8RelB a b = false := by
    by_contra hq
    obtain ⟨h1, h2⟩ := ord4B_of_q8RelB (Bool.eq_true_of_ne_false hq)
    rw [h1, h2] at hab
    exact Bool.noConfusion hab
  rw [hq]
  rfl

end Filter

end Certificates.S7Q8

end
