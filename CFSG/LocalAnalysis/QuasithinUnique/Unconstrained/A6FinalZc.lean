module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel4

public section

namespace CFSG.QuasithinUnique.A6Facts.Core

@[expose] def zcLit : List (List Nat) :=
  p0Lit.filter fun c => e4Lit.all fun b => cmul c b == cmul b c

theorem zc_fourth : zcLit.all (fun c => cmul (cmul c c) (cmul c c) == cid) = true := by
  decide +kernel

theorem zc_no_q8 : zcLit.all (fun a => zcLit.all fun b =>
    cmul a a == cid || cmul a a != cmul b b || cmul a a != cmul (cmul a b) (cmul a b)) = true := by
  decide +kernel

end CFSG.QuasithinUnique.A6Facts.Core

namespace CFSG.QuasithinUnique.A6Facts

theorem exists_E4_of_code {c : List ℕ} (hc : c ∈ Core.e4Lit) : ∃ x, InE4 x ∧ code x = c := by
  have hcP : c ∈ Core.p0Lit := by
    unfold Core.e4Lit at hc
    rw [List.mem_filter] at hc
    exact hc.1
  obtain ⟨x, -, rfl⟩ := exists_P0_of_code hcP
  exact ⟨x, (inE4_iff x).2 hc, rfl⟩

theorem code_mem_zc {y : P10} (hy : y ∈ P0) (hc : ∀ c, InE4 c → y * c = c * y) :
    code y ∈ Core.zcLit := by
  unfold Core.zcLit
  rw [List.mem_filter]
  refine ⟨(mem_P0_iff y).1 hy, ?_⟩
  rw [List.all_eq_true]
  intro b hb
  obtain ⟨x, hx, rfl⟩ := exists_E4_of_code hb
  rw [beq_iff_eq, ← code_mul, ← code_mul, hc x hx]

theorem zc_fourth_perm {y : P10} (hy : y ∈ P0) (hc : ∀ c, InE4 c → y * c = c * y) :
    y * y * (y * y) = 1 := by
  have h := Core.zc_fourth
  rw [List.all_eq_true] at h
  have h1 := h (code y) (code_mem_zc hy hc)
  rw [beq_iff_eq] at h1
  apply code_injective
  simp only [code_mul, code_one]
  exact h1

theorem zc_no_q8_perm {a b : P10} (ha : a ∈ P0) (hb : b ∈ P0)
    (hca : ∀ c, InE4 c → a * c = c * a) (hcb : ∀ c, InE4 c → b * c = c * b) (h1 : a * a ≠ 1)
    (h2 : a * a = b * b) (h3 : a * a = a * b * (a * b)) : False := by
  have h := Core.zc_no_q8
  rw [List.all_eq_true] at h
  have h4 := h (code a) (code_mem_zc ha hca)
  rw [List.all_eq_true] at h4
  have h5 := h4 (code b) (code_mem_zc hb hcb)
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h5
  have e1 : code (a * a) = Core.cmul (code a) (code a) := code_mul a a
  have e2 : code (b * b) = Core.cmul (code b) (code b) := code_mul b b
  have e3 : code (a * b * (a * b)) =
      Core.cmul (Core.cmul (code a) (code b)) (Core.cmul (code a) (code b)) := by
    simp only [code_mul]
  rcases h5 with (h | h) | h
  · apply h1
    apply code_injective
    rw [e1, code_one]
    exact h
  · exact h (by rw [← e1, ← e2, h2])
  · exact h (by rw [← e1, ← e3, h3])

end CFSG.QuasithinUnique.A6Facts
