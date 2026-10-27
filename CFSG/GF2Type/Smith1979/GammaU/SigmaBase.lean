
module

public import CFSG.GF2Type.Smith1979.GammaU.SigmaInputs
public import CFSG.GF2Type.Smith1979.GammaU.Violation

public section

namespace CFSG.GF2Type.Smith1979.GammaU.SigmaP

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.GammaU.ResPair Module
open scoped commutatorElement

@[expose] def sigma (i : ℕ) : Submodule (ZMod 2) V12 := spanOf (sigmaBasis i)

@[expose] def p2 (i : ℕ) : Subgroup (V12 ≃ₗ[ZMod 2] V12) := genGrp (pGens i)

theorem gensOK_spec {gs : List (Array ℕ)} (h : gensOK gs = true) : GensOK gs := by
  simp only [gensOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  intro g hg
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h g hg
  exact ⟨h1, h2, h3, h4⟩

theorem finrank_of_indepCheck : ∀ {B : List ℕ}, (∀ b ∈ B, b < 4096) → indepCheck B = true →
    finrank (ZMod 2) (spanOf B) = B.length
  | [], _, _ => by rw [spanOf_nil, finrank_bot]; rfl
  | v :: vs, hlt, h => by
    simp only [indepCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hvs : ∀ b ∈ vs, b < 4096 := fun b hb => hlt b (List.mem_cons_of_mem v hb)
    have hv : vecOf v ∉ spanOf vs := fun hm => by
      rw [← mem_spanList_iff hvs (hlt v List.mem_cons_self), ← List.contains_iff_mem, h.1] at hm
      exact Bool.noConfusion hm
    rw [finrank_spanOf_cons hv, finrank_of_indepCheck hvs h.2, List.length_cons]

theorem mem_spanOf_of_mem_spanList {vs : List ℕ} (hvs : ∀ v ∈ vs, v < 4096) {n : ℕ}
    (hn : n ∈ spanList vs) : vecOf n ∈ spanOf vs :=
  (mem_spanList_iff hvs (spanList_lt hvs n hn)).1 hn

theorem codeOf_mem_spanList {vs : List ℕ} (hvs : ∀ v ∈ vs, v < 4096) {x : V12}
    (hx : x ∈ spanOf vs) : codeOf x ∈ spanList vs := by
  rw [mem_spanList_iff hvs (codeOf_lt x), vecOf_codeOf]
  exact hx

theorem f4Indep_of {x y : ℕ} (hx : x < 4096) (hy : y < 4096)
    (h : F4Indep (vecOf x) (vecOf y)) : f4Indep x y = true := by
  obtain ⟨hx0, hxy⟩ := h
  have htx := theta0N_lt hx
  simp only [f4Indep, Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨fun h0 => hx0 (by rw [h0, vecOf_zero]), fun h0 => hxy 0 0 ?_⟩,
    fun h0 => hxy 1 0 ?_⟩, fun h0 => hxy 0 1 ?_⟩, fun h0 => hxy 1 1 ?_⟩
  · simp [h0]
  · simp [h0]
  · rw [h0, vecOf_theta0N hx]; simp
  · rw [h0, vecOf_xor, vecOf_theta0N hx]; simp

variable {i : ℕ}

theorem basis_lt (hi : i = 0 ∨ i = 1) : ∀ b ∈ sigmaBasis i, b < 4096 := by
  rcases hi with rfl | rfl <;> decide

theorem orbit_lt (hi : i = 0 ∨ i = 1) : ∀ x ∈ s45 i, x < 4096 := by
  rcases hi with rfl | rfl <;> decide +kernel

end CFSG.GF2Type.Smith1979.GammaU.SigmaP
