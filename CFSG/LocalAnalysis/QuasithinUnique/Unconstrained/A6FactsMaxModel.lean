module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsMax
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel4

public section

namespace CFSG.QuasithinUnique.A6Facts

open Equiv

@[expose] def maxRepsP : List P10 :=
  [A6Models.perm10 [[2, 5, 9, 8], [3, 7, 4, 6]], A6Models.perm10 [[1, 3, 2, 6], [4, 5, 8, 7]],
    A6Models.perm10 [[1, 3], [2, 7], [5, 6], [8, 9]], A6Models.perm10 [[1, 3, 5, 7], [2, 9, 6, 4]]]

theorem maxRepsP_code : maxRepsP.map code = Core.maxReps := by decide +kernel

theorem maxRepsInvP_code : (maxRepsP.map (·⁻¹)).map code = Core.maxRepsInv := by decide +kernel

theorem invol_cent_not_P0 {g : P10} (hgP : g ∈ P0) (hne : g ≠ 1) (hz : g ≠ zb) (hg2 : g * g = 1) :
    ∃ k ∈ A6Models.psl29, k * g = g * k ∧ k ∉ P0 := by
  have hall := Core.invol_cent_check
  rw [List.all_eq_true] at hall
  have h1 := hall (code g) ((mem_P0_iff g).1 hgP)
  rw [beq_cid_false hne, ← zb_code, beq_ne_false hz, beq_sq_true hg2] at h1
  simp only [Bool.false_or, Bool.not_true, Bool.or_false, List.any_eq_true] at h1
  obtain ⟨c, hc, hcany⟩ := h1
  obtain ⟨k, hk, rfl⟩ := exists_psl29_of_code hc
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hcany
  refine ⟨k, hk, ?_, fun hkP => ?_⟩
  · apply code_injective
    rw [code_mul, code_mul]
    exact hcany.1
  · have := List.contains_iff_mem.mpr ((mem_P0_iff k).1 hkP)
    rw [hcany.2] at this
    exact Bool.false_ne_true this

theorem eval_word_mem {X : Subgroup P10} :
    ∀ (w : List (List ℕ)) (acc : P10), acc ∈ X → (∀ a ∈ w, ∃ σ ∈ X, code σ = a) →
      ∃ σ ∈ X, code σ = w.foldl Core.cmul (code acc) := by
  intro w
  induction w with
  | nil => intro acc hacc _; exact ⟨acc, hacc, rfl⟩
  | cons a w ih =>
    intro acc hacc hw
    obtain ⟨σ, hσ, hσa⟩ := hw a (List.mem_cons_self)
    have h1 : code (acc * σ) = Core.cmul (code acc) a := by rw [code_mul, hσa]
    obtain ⟨τ, hτ, hτc⟩ := ih (acc * σ) (X.mul_mem hacc hσ)
      (fun b hb => hw b (List.mem_cons_of_mem a hb))
    exact ⟨τ, hτ, by rw [hτc, List.foldl_cons, h1]⟩

theorem maxRepsP_length : maxRepsP.length = 4 := by decide +kernel

theorem getD_map_code (l : List P10) (i : ℕ) (hi : i < l.length) :
    (l.map code).getD i [] = code (l.getD i 1) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem getD_map_inv_code (l : List P10) (i : ℕ) (hi : i < l.length) :
    ((l.map (·⁻¹)).map code).getD i [] = code ((l.getD i 1)⁻¹) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem P0_overgroup {X : Subgroup P10} (hP : ∀ p ∈ P0, p ∈ X) {k : P10} (hk : k ∈ A6Models.psl29)
    (hkP : k ∉ P0) (hkX : k ∈ X) : A6Models.psl29 ≤ X := by
  have hkL : code k ∈ Core.pslLit := (mem_psl29_iff k).1 hk
  have hkn : code k ∉ Core.p0Lit := fun h => hkP ((mem_P0_iff k).2 h)
  have hkey : code k ∈ Core.maxCert.map (fun e => e.1) := by
    rw [Core.max_cert_keys, List.mem_filter]
    refine ⟨hkL, ?_⟩
    simpa using hkn
  obtain ⟨⟨ek, i, p, q⟩, he, hek⟩ := List.mem_map.mp hkey
  have hek' : ek = code k := hek
  subst hek'
  have hcert := Core.max_cert_ok
  rw [List.all_eq_true] at hcert
  have hc := hcert _ he
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hi4, hpmem⟩, hqmem⟩, heq⟩ := hc
  have hi : i < maxRepsP.length := by rw [maxRepsP_length]; exact hi4
  obtain ⟨σp, hσp, rfl⟩ := exists_P0_of_code hpmem
  obtain ⟨σq, hσq, rfl⟩ := exists_P0_of_code hqmem
  set ρ : P10 := maxRepsP.getD i 1 with hρ
  have hρcode : code ρ = Core.maxReps.getD i [] := by
    rw [← maxRepsP_code, getD_map_code _ _ hi]
  have hρinvcode : code ρ⁻¹ = Core.maxRepsInv.getD i [] := by
    rw [← maxRepsInvP_code, getD_map_inv_code _ _ hi]
  have hkeq : σp * ρ * σq = k := by
    apply code_injective
    rw [code_mul, code_mul, hρcode]
    exact heq
  have hρX : ρ ∈ X := by
    have : ρ = σp⁻¹ * k * σq⁻¹ := by rw [← hkeq]; group
    rw [this]
    exact X.mul_mem (X.mul_mem (X.inv_mem (hP _ hσp)) hkX) (X.inv_mem (hP _ hσq))
  have hgens : ∀ j : ℕ, j < 3 → pslGens.getD j 1 ∈ X := by
    intro j hj
    have hall := Core.max_words_ok
    rw [List.all_eq_true] at hall
    have h1 := hall i (List.mem_range.mpr hi4)
    rw [List.all_eq_true] at h1
    have h2 := h1 j (List.mem_range.mpr hj)
    unfold Core.wordOk at h2
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
      List.contains_iff_mem] at h2
    obtain ⟨hletters, hprod⟩ := h2
    have hmem : ∀ a ∈ (Core.maxWords.getD i []).getD j [], ∃ σ ∈ X, code σ = a := by
      intro a ha
      rcases hletters a ha with (h | h) | h
      · obtain ⟨σ, hσ, rfl⟩ := exists_P0_of_code h
        exact ⟨σ, hP σ hσ, rfl⟩
      · exact ⟨ρ, hρX, by rw [hρcode, h]⟩
      · exact ⟨ρ⁻¹, X.inv_mem hρX, by rw [hρinvcode, h]⟩
    obtain ⟨σ, hσX, hσc⟩ := eval_word_mem ((Core.maxWords.getD i []).getD j []) 1 X.one_mem hmem
    rw [code_one] at hσc
    have hgc : code (pslGens.getD j 1) = Core.pslGenC.getD j [] := by
      rw [← pslGens_code]
      have : j < pslGens.length := by simpa [pslGens] using hj
      exact (getD_map_code pslGens j this).symm
    have : σ = pslGens.getD j 1 := by
      apply code_injective
      rw [hσc, hprod, hgc]
    rw [← this]
    exact hσX
  rw [psl29_eq, Subgroup.closure_le]
  intro g hg
  simp only [pslGens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact hgens 0 (by norm_num)
  · exact hgens 1 (by norm_num)
  · exact hgens 2 (by norm_num)

end CFSG.QuasithinUnique.A6Facts
