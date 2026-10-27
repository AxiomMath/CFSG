module

public import CFSG.GF2Type.Smith1979.GammaU.Bits
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GF2Type.Smith1979.GammaU

open Module

theorem codeOf_vecOf {n : ℕ} (hn : n < 4096) : codeOf (vecOf n) = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have h := testBit_codeOf (vecOf n) ⟨i, hi⟩
    simp only at h
    rw [h, vecOf]
    cases n.testBit i <;> decide
  · rw [testBit_of_lt (codeOf_lt _) (by omega), testBit_of_lt hn (by omega)]

theorem vecOf_inj {a b : ℕ} (ha : a < 4096) (hb : b < 4096) (h : vecOf a = vecOf b) : a = b := by
  rw [← codeOf_vecOf ha, ← codeOf_vecOf hb, h]

theorem vecOf_eq_zero {n : ℕ} (hn : n < 4096) : vecOf n = 0 ↔ n = 0 :=
  ⟨fun h => vecOf_inj hn (by norm_num) (h.trans vecOf_zero.symm), fun h => h ▸ vecOf_zero⟩

theorem xor_lt {a b : ℕ} (ha : a < 4096) (hb : b < 4096) : a ^^^ b < 4096 :=
  Nat.xor_lt_two_pow (n := 12) ha hb

theorem vec_sub_eq_add (x y : V12) : x - y = x + y := by
  funext j
  exact CharTwo.sub_eq_add (x j) (y j)

@[expose] def spanList : List ℕ → List ℕ
  | [] => [0]
  | v :: vs => spanList vs ++ (spanList vs).map (· ^^^ v)

abbrev spanOf (vs : List ℕ) : Submodule (ZMod 2) V12 :=
  Submodule.span (ZMod 2) {x | ∃ v ∈ vs, vecOf v = x}

theorem setOf_cons (v : ℕ) (vs : List ℕ) :
    {x | ∃ w ∈ v :: vs, vecOf w = x} = insert (vecOf v) {x | ∃ w ∈ vs, vecOf w = x} := by
  ext x
  simp only [List.mem_cons, Set.mem_setOf_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨w, rfl | hw, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨w, hw, rfl⟩
  · rintro (rfl | ⟨w, hw, rfl⟩)
    · exact ⟨v, Or.inl rfl, rfl⟩
    · exact ⟨w, Or.inr hw, rfl⟩

theorem spanOf_cons (v : ℕ) (vs : List ℕ) :
    spanOf (v :: vs) = Submodule.span (ZMod 2) (insert (vecOf v) {x | ∃ w ∈ vs, vecOf w = x}) := by
  unfold spanOf
  rw [setOf_cons]

theorem spanOf_nil : spanOf [] = ⊥ := by
  unfold spanOf
  have hset : {x : V12 | ∃ v ∈ ([] : List ℕ), vecOf v = x} = ∅ := by simp
  rw [hset, Submodule.span_empty]

theorem mem_spanOf_of_mem {v : ℕ} {vs : List ℕ} (h : v ∈ vs) : vecOf v ∈ spanOf vs :=
  Submodule.subset_span ⟨v, h, rfl⟩

theorem spanList_lt {vs : List ℕ} (hvs : ∀ v ∈ vs, v < 4096) : ∀ n ∈ spanList vs, n < 4096 := by
  induction vs with
  | nil => simp [spanList]
  | cons v vs ih =>
    intro n hn
    simp only [spanList, List.mem_append, List.mem_map] at hn
    rcases hn with hn | ⟨m, hm, rfl⟩
    · exact ih (fun w hw => hvs w (List.mem_cons_of_mem v hw)) n hn
    · exact xor_lt (ih (fun w hw => hvs w (List.mem_cons_of_mem v hw)) m hm)
        (hvs v List.mem_cons_self)

theorem mem_spanList_iff {vs : List ℕ} (hvs : ∀ v ∈ vs, v < 4096) {n : ℕ} (hn : n < 4096) :
    n ∈ spanList vs ↔ vecOf n ∈ spanOf vs := by
  induction vs generalizing n with
  | nil =>
    rw [spanOf_nil, Submodule.mem_bot]
    simp only [spanList, List.mem_singleton]
    exact (vecOf_eq_zero hn).symm
  | cons v vs ih =>
    have hvs' : ∀ w ∈ vs, w < 4096 := fun w hw => hvs w (List.mem_cons_of_mem v hw)
    have hv : v < 4096 := hvs v List.mem_cons_self
    have hzmod : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rw [spanOf_cons, Submodule.mem_span_insert]
    simp only [spanList, List.mem_append, List.mem_map]
    constructor
    · rintro (h | ⟨m, hm, rfl⟩)
      · exact ⟨0, vecOf n, (ih hvs' hn).1 h, by rw [zero_smul, zero_add]⟩
      · refine ⟨1, vecOf m, (ih hvs' (spanList_lt hvs' m hm)).1 hm, ?_⟩
        rw [vecOf_xor, one_smul, add_comm]
    · rintro ⟨a, z, hz, hnz⟩
      rcases hzmod a with rfl | rfl
      · rw [zero_smul, zero_add] at hnz
        exact Or.inl ((ih hvs' hn).2 (hnz ▸ hz))
      · right
        refine ⟨n ^^^ v, (ih hvs' (xor_lt hn hv)).2 ?_, by rw [Nat.xor_assoc, Nat.xor_self,
          Nat.xor_zero]⟩
        rw [vecOf_xor, ← vec_sub_eq_add, hnz, one_smul, add_sub_cancel_left]
        exact hz

theorem finrank_spanOf_cons {v : ℕ} {vs : List ℕ} (hv : vecOf v ∉ spanOf vs) :
    finrank (ZMod 2) (spanOf (v :: vs)) = finrank (ZMod 2) (spanOf vs) + 1 := by
  rw [spanOf_cons, Submodule.span_insert]
  unfold spanOf at hv ⊢
  have hv0 : vecOf v ≠ 0 := fun h => hv (h ▸ Submodule.zero_mem _)
  have hinf : (ZMod 2 ∙ vecOf v) ⊓ Submodule.span (ZMod 2) {x | ∃ w ∈ vs, vecOf w = x} = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy1
    have hzmod : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hzmod c with rfl | rfl
    · simp
    · rw [one_smul] at hy2
      exact absurd hy2 hv
  have h := Submodule.finrank_sup_add_finrank_inf_eq (ZMod 2 ∙ vecOf v)
    (Submodule.span (ZMod 2) {x | ∃ w ∈ vs, vecOf w = x})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hv0] at h
  omega

end CFSG.GF2Type.Smith1979.GammaU
