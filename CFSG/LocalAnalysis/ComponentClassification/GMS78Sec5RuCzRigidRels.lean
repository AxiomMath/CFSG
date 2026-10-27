module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzModel
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzSign
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmGlue

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.VecSurj
  CFSG.Sporadic.Bridge.SurjD.Native

section Words

variable {G : Type*} [Group G]

private theorem wordProd_natWord (x : ℕ → G) (w : List ℕ) :
    wordProd x (natWord w) = Sign.evalC x w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [show natWord (c :: w) = (c / 2, c % 2 == 0) :: natWord w from rfl, wordProd_cons, ih,
      Sign.evalC_cons]
    by_cases h : c % 2 = 0 <;> simp [h]

private theorem xor_one_codes (c : ℕ) :
    (c ^^^ 1) / 2 = c / 2 ∧ ((c ^^^ 1) % 2 = 0 ↔ ¬ c % 2 = 0) := by
  rcases Nat.even_or_odd c with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [Nat.xor_one_of_even ⟨k, rfl⟩]
    omega
  · rw [Nat.xor_one_of_odd ⟨k, rfl⟩]
    omega

private theorem evalC_invCodes (g : ℕ → G) (w : List ℕ) :
    Sign.evalC g (invCodes w) = (Sign.evalC g w)⁻¹ := by
  induction w with
  | nil => simp [invCodes]
  | cons c w ih =>
    have e : invCodes (c :: w) = invCodes w ++ [c ^^^ 1] := by
      simp [invCodes]
    obtain ⟨h1, h2⟩ := xor_one_codes c
    rw [e, Sign.evalC_append, ih, Sign.evalC_cons, Sign.evalC_cons, Sign.evalC_nil, h1, mul_one,
      mul_inv_rev]
    congr 1
    by_cases hc : c % 2 = 0
    · rw [ite_eq_right (fun h => h2.1 h hc), ite_eq_left hc]
    · rw [ite_eq_left (h2.2 hc), ite_eq_right hc, inv_inv]

private theorem evalC_conjRel (g : ℕ → G) (y i : ℕ) (W : List ℕ) :
    Sign.evalC g (conjRel y i W) = (g y)⁻¹ * g i * g y * (Sign.evalC g W)⁻¹ := by
  have h1 : (2 * y + 1) % 2 = 1 := by omega
  have h2 : (2 * y + 1) / 2 = y := by omega
  have h3 : 2 * i % 2 = 0 := by omega
  have h4 : 2 * i / 2 = i := by omega
  have h5 : 2 * y % 2 = 0 := by omega
  have h6 : 2 * y / 2 = y := by omega
  rw [conjRel, Sign.evalC_append, evalC_invCodes, Sign.evalC_cons, Sign.evalC_cons,
    Sign.evalC_cons, Sign.evalC_nil]
  simp only [h1, h2, h3, h4, h5, h6, one_ne_zero, ↓reduceIte, mul_one, mul_assoc]

end Words

theorem czJ_eval :
    ∀ v ∈ czJRelRels, wordProd pi7Img v = 1 :=
  fun v hv => (cz_jrel v hv).2

section Relations


theorem czJ_eq_one {v : List (ℕ × Bool)} (hv : v ∈ czJRelRels) : wordProd pi7L v = 1 := by
  refine pi7ToJ_bijective.1 ?_
  rw [map_one, map_wordProd, wordProd_congr (y := pi7Img) fun l hl =>
    pi7ToJ_pi7L ((cz_jrel v hv).1 l hl)]
  exact czJ_eval v hv

theorem czJRelCodes_eval {r : List ℕ} (hr : r ∈ czJRelCodes) : Sign.evalC czImg r = 1 := by
  have h := czJ_eq_one (v := substWord (natWord r)) (by
    unfold czJRelRels
    exact List.mem_append_left _ (List.mem_map_of_mem hr))
  rwa [wordProd_substWord, wordProd_natWord] at h

theorem czJ_rels : ∀ r ∈ czRelsJ, Sign.evalC czImg r = 1 := fun _ hr =>
  czJRelCodes_eval (by
    unfold czJRelCodes
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr)))

theorem czJ_conjQ :
    ∀ i < 6, (czImg 6)⁻¹ * czImg i * czImg 6 = Sign.evalC czImg (czWq.getD i []) := by
  intro i hi
  have h := czJRelCodes_eval (r := conjRel 6 i (czWq.getD i [])) (by
    unfold czJRelCodes
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))))
  rw [evalC_conjRel] at h
  exact mul_inv_eq_one.mp h

theorem czJ_conjV :
    ∀ i < 6, (czImg 7)⁻¹ * czImg i * czImg 7 = Sign.evalC czImg (czWv.getD i []) := by
  intro i hi
  have h := czJRelCodes_eval (r := conjRel 7 i (czWv.getD i [])) (by
    unfold czJRelCodes
    exact List.mem_append_left _
      (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))
  rw [evalC_conjRel] at h
  exact mul_inv_eq_one.mp h

theorem czJ_conjW :
    ∀ i < 6, (czImg 8)⁻¹ * czImg i * czImg 8 = Sign.evalC czImg (czWw.getD i []) := by
  intro i hi
  have h := czJRelCodes_eval (r := conjRel 8 i (czWw.getD i [])) (by
    unfold czJRelCodes
    exact List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
  rw [evalC_conjRel] at h
  exact mul_inv_eq_one.mp h

theorem czZ0_eq : czImg 0 ^ 2 = RuAsm.ruZ0 := by
  have h := czJ_eq_one (v := substWord (natWord [0, 0]) ++
    invNatWord (RuAsm.ruZ0Word.map fun l => (l.1.val, l.2))) (by
      unfold czJRelRels
      exact List.mem_append_right _ (List.mem_singleton.2 rfl))
  rw [wordProd_append, wordProd_invNatWord, wordProd_substWord, wordProd_natWord,
    mul_inv_eq_one] at h
  have e : (fun i : Fin 7 => pi7L i.val) = fun i => (PresentedGroup.of i : Pi7) :=
    funext fun i => pi7L_of_lt i.2
  rw [RuAsm.ruZ0, RuAsm.pi7Word_eq_lift, ← e, lift_mk_eq_wordProd, ← h, pow_two]
  simp only [Sign.evalC_cons, Sign.evalC_nil, Nat.zero_mod, Nat.zero_div, ↓reduceIte, mul_one]
  rfl

end Relations

end CFSG.ComponentClassification.GMS78.RuCz
