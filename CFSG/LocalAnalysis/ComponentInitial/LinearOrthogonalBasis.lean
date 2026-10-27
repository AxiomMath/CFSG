module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Module LinearMap.BilinForm Polynomial

universe u v

variable {k : Type u} [Field k]

theorem exists_mul_sq_add_mul_sq_eq [Fintype k] (hk : Fintype.card k % 2 = 1) {b c : k}
    (hb : b ≠ 0) (hc : c ≠ 0) (a : k) : ∃ x y : k, b * x ^ 2 + c * y ^ 2 = a := by
  have hf : degree (C b * X ^ 2) = 2 := degree_C_mul_X_pow 2 hb
  have hg : degree (C c * X ^ 2 - C a) = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 hc]; norm_num), degree_C_mul_X_pow 2 hc]
    rfl
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic hf hg hk
  refine ⟨x, y, ?_⟩
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub] at h
  linear_combination h

theorem two_ne_zero_of_card_odd [Fintype k] (hk : Fintype.card k % 2 = 1) : (2 : k) ≠ 0 :=
  Ring.two_ne_zero fun h => by
    rw [FiniteField.even_card_iff_char_two] at h
    omega

variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem exists_bilin_self_eq [Fintype k] (hk : Fintype.card k % 2 = 1) (hV : 2 ≤ finrank k V)
    {B : LinearMap.BilinForm k V} (hB : B.Nondegenerate) (hBs : B.IsSymm) (a : k) :
    ∃ v : V, B v v = a := by
  let : Invertible (2 : k) := invertibleOfNonzero (two_ne_zero_of_card_odd hk)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  obtain ⟨u, hu⟩ := exists_bilinForm_self_ne_zero hB.ne_zero (isSymm_iff.mp hBs)
  set W := B.orthogonal (k ∙ u) with hWdef
  have hW : finrank k W = finrank k V - 1 := by
    rw [finrank_orthogonal hB, finrank_span_singleton (ne_zero_of_not_isOrtho_self u hu)]
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have hBW := restrict_nondegenerate_orthogonal_spanSingleton B hB hBs.isRefl hu
  obtain ⟨w, hw⟩ := exists_bilinForm_self_ne_zero hBW.ne_zero (isSymm_iff.mp (hBs.restrict W))
  obtain ⟨x, y, hxy⟩ := exists_mul_sq_add_mul_sq_eq hk hu hw a
  refine ⟨x • u + y • (w : V), ?_⟩
  have huw : B u w = 0 := w.prop u (Submodule.mem_span_singleton_self u)
  have hwu : B w u = 0 := by rw [hBs.eq]; exact huw
  rw [← hxy]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, huw,
    hwu, restrict_apply, LinearMap.domRestrict_apply]
  ring

theorem exists_orthoFamily_aux [Fintype k] (hk : Fintype.card k % 2 = 1) {a : k} (ha : a ≠ 0) :
    ∀ (d : ℕ) (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V],
      finrank k V = d + 1 → ∀ (B : LinearMap.BilinForm k V), B.Nondegenerate → B.IsSymm →
        ∀ v : V, B v v ≠ 0 → ∃ e : Fin (d + 1) → V, B.IsOrthoᵢ e ∧ e 0 = v ∧
          (∀ i : Fin (d + 1), 0 < (i : ℕ) → (i : ℕ) < d → B (e i) (e i) = a) ∧
          B (e (Fin.last d)) (e (Fin.last d)) ≠ 0 := by
  intro d
  induction d with
  | zero =>
    intro V _ _ _ _ B _ _ v hv
    refine ⟨fun _ => v, fun i j hij => (hij (Fin.ext (by omega))).elim, rfl,
      fun i h0 h1 => by omega, hv⟩
  | succ d ih =>
    intro V _ _ _ hV B hB hBs v hv
    set W := B.orthogonal (k ∙ v) with hWdef
    have hW : finrank k W = d + 1 := by
      rw [finrank_orthogonal hB, finrank_span_singleton (ne_zero_of_not_isOrtho_self v hv), hV]
      rfl
    have hBW : (B.restrict W).Nondegenerate :=
      restrict_nondegenerate_orthogonal_spanSingleton B hB hBs.isRefl hv
    obtain ⟨w, hw0, hwa⟩ : ∃ w : W, B.restrict W w w ≠ 0 ∧ (1 ≤ d → B.restrict W w w = a) := by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · let : Invertible (2 : k) := invertibleOfNonzero (two_ne_zero_of_card_odd hk)
        have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := k) (by omega)
        obtain ⟨w, hw⟩ :=
          exists_bilinForm_self_ne_zero hBW.ne_zero (isSymm_iff.mp (hBs.restrict W))
        exact ⟨w, hw, fun h => by omega⟩
      · obtain ⟨w, hw⟩ := exists_bilin_self_eq hk (by omega) hBW (hBs.restrict W) a
        exact ⟨w, hw ▸ ha, fun _ => hw⟩
    obtain ⟨e', he'o, he'0, he'a, he'l⟩ := ih W hW (B.restrict W) hBW (hBs.restrict W) w hw0
    have hvW : ∀ x : W, B v x = 0 := fun x => x.prop v (Submodule.mem_span_singleton_self v)
    have hWv : ∀ x : W, B x v = 0 := fun x => by rw [hBs.eq]; exact hvW x
    refine ⟨Fin.cons v fun i => (e' i : V), ?_, rfl, ?_, ?_⟩
    · rw [LinearMap.isOrthoᵢ_def]
      intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => simpa using hvW (e' j)
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa using hWv (e' i)
        | succ j =>
          have := (LinearMap.isOrthoᵢ_def.mp he'o) i j (fun h => hij (by rw [h]))
          simpa using this
    · intro i hi0 hid
      cases i using Fin.cases with
      | zero => exact absurd hi0 (lt_irrefl 0)
      | succ j =>
        simp only [Fin.val_succ, Fin.cons_succ] at hi0 hid ⊢
        rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj0
        · have hj' : j = 0 := Fin.ext hj0
          subst hj'
          rw [he'0]
          exact hwa (by omega)
        · exact he'a j hj0 (by omega)
    · have hl : (Fin.last (d + 1)) = (Fin.last d).succ := rfl
      rw [hl, Fin.cons_succ]
      exact he'l

theorem finite_odd_symmetric_equal_value_orthogonal_basis [Finite k] (hk : Odd (Nat.card k))
    {d : ℕ} (hd : finrank k V = d) (h2 : 2 ≤ d) {B : LinearMap.BilinForm k V} (hB : B.Nondegenerate)
    (hBs : B.IsSymm) :
    (∀ a : k, a ≠ 0 → ∃ v : V, B v v = a) ∧
      ∀ (a : k) (v : V), a ≠ 0 → B v v = a →
        ∃ e : Basis (Fin d) k V, B.IsOrthoᵢ e ∧ (∀ i : Fin d, (i : ℕ) = 0 → e i = v) ∧
          (∀ i : Fin d, (i : ℕ) < d - 1 → B (e i) (e i) = a) ∧
          (∀ i : Fin d, (i : ℕ) = d - 1 → B (e i) (e i) ≠ 0) := by
  have := Fintype.ofFinite k
  have hk' : Fintype.card k % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hk
  refine ⟨fun a _ => exists_bilin_self_eq hk' (by omega) hB hBs a, fun a v ha hv => ?_⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨e, heo, he0, hea, hel⟩ :=
    exists_orthoFamily_aux hk' ha d' V hd B hB hBs v (hv ▸ ha)
  have hne : ∀ i, B (e i) (e i) ≠ 0 := by
    intro i
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [show i = 0 from Fin.ext h0, he0, hv]
      exact ha
    · rcases Nat.lt_or_ge (i : ℕ) d' with h1 | h1
      · rw [hea i h0 h1]
        exact ha
      · rw [show i = Fin.last d' from Fin.ext (by have := i.isLt; simp; omega)]
        exact hel
  have hli : LinearIndependent k e := LinearMap.linearIndependent_of_isOrthoᵢ heo hne
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hd])
  have hb : ⇑b = e := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  refine ⟨b, hb ▸ heo, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hb, show i = 0 from Fin.ext hi, he0]
  · rw [hb]
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [show i = 0 from Fin.ext h0, he0, hv]
    · exact hea i h0 (by omega)
  · rw [hb]
    exact hne i

end CFSG.LocalAnalysis.ComponentInitial
