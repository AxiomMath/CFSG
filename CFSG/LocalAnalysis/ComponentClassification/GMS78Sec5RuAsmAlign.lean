module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmNorm
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmWords
public import Certificates.Certificate15105

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

open Subgroup CFSG.ComponentClassification.GMS78.RuPi7

theorem pi7Word_append (u v : List (Fin 7 × Bool)) :
    pi7Word (u ++ v) = pi7Word u * pi7Word v := by
  unfold pi7Word
  rw [← map_mul, FreeGroup.mul_mk]

theorem pi7Word_nil : pi7Word [] = 1 := by
  unfold pi7Word
  rw [← FreeGroup.one_eq_mk, map_one]

theorem pi7Word_invWord (w : List (Fin 7 × Bool)) :
    pi7Word (ruAsmInvWord w) = (pi7Word w)⁻¹ := by
  unfold pi7Word
  rw [← map_inv, FreeGroup.inv_mk]
  rfl

theorem pi7Word_letter (i : Fin 7) : pi7Word [(i, true)] = PresentedGroup.of i := rfl

theorem pi7Word_letter_inv (i : Fin 7) : pi7Word [(i, false)] = (PresentedGroup.of i)⁻¹ := by
  rw [← pi7Word_letter, ← pi7Word_invWord]
  rfl

theorem pi7Word_mem_letterSub {l : List (Fin 7)} {w : List (Fin 7 × Bool)}
    (hw : ∀ p ∈ w, p.1 ∈ l) : pi7Word w ∈ letterSub l := by
  induction w with
  | nil => rw [pi7Word_nil]; exact one_mem _
  | cons p w ih =>
    rw [show p :: w = [p] ++ w from rfl, pi7Word_append]
    refine mul_mem ?_ (ih fun q hq => hw q (List.mem_cons_of_mem _ hq))
    obtain ⟨i, b⟩ := p
    have hi : i ∈ l := hw _ List.mem_cons_self
    cases b
    · rw [pi7Word_letter_inv]
      exact inv_mem (mem_letterSub hi)
    · rw [pi7Word_letter]
      exact mem_letterSub hi

theorem conj_mem_of_mem_closure {S : Set Pi7} {H : Subgroup Pi7} {g : Pi7}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ H) {x : Pi7} (hx : x ∈ closure S) : g * x * g⁻¹ ∈ H := by
  have hle : closure S ≤ H.comap (MulAut.conj g).toMonoidHom :=
    (closure_le _).2 fun s hs => by simpa using h s hs
  simpa using hle hx

@[expose] noncomputable def ruA0Elt (e : ℕ) : Pi7 := pi7Word (ruA0PowWord e)

theorem ruA0Elt_zero : ruA0Elt 0 = 1 := by
  rw [ruA0Elt, show ruA0PowWord 0 = [] by decide, pi7Word_nil]

theorem ruA0Words_getD_mem {j : ℕ} (hj : j < 3) : pi7Word (ruA0Words.getD j []) ∈ ruA0 := by
  have h : ∀ j < 3, ruA0Words.getD j [] ∈ ruA0Words := by decide
  exact subset_closure ⟨_, h j hj, rfl⟩

theorem ruA0Elt_mem (e : ℕ) : ruA0Elt e ∈ ruA0 := by
  simp only [ruA0Elt, ruA0PowWord, pi7Word_append]
  refine mul_mem (mul_mem ?_ ?_) ?_ <;> split_ifs <;>
    first
    | exact ruA0Words_getD_mem (by norm_num)
    | (rw [pi7Word_nil]; exact one_mem _)

theorem xor_lt_eight {e e' : ℕ} (he : e < 8) (he' : e' < 8) : e ^^^ e' < 8 :=
  Nat.xor_lt_two_pow (n := 3) he he'

theorem ruAlignTransWords_letters : ∀ k < 7, ∀ p ∈ ruAlignTransWords.getD k [],
    p.1 ∈ ([0, 1, 2, 3, 4, 6] : List (Fin 7)) := by
  decide

theorem ruA0Words_eq_getD : ∀ w ∈ ruA0Words, ∃ j < 3, ruA0Words.getD j [] = w := by
  decide

theorem ruM2Letters_eq_getD : ∀ l ∈ ([0, 1, 2, 3, 4, 6] : List (Fin 7)),
    ∃ i < 6, ruM2Letters.getD i 0 = l := by
  decide


theorem pi7Word_eq_of_mem_align {u v : List (Fin 7 × Bool)}
    (h : (u, v) ∈ ruAlignMulPairs ++ ruAlignTransPairs ++ ruAlignNormPairs) :
    pi7Word u = pi7Word v :=
  pi7Word_eq_of_wordProd (Certificates.certificate15105 _ h)

theorem ruA0Elt_mul {e e' : ℕ} (he : e < 8) (he' : e' < 8) :
    ruA0Elt e * ruA0Elt e' = ruA0Elt (e ^^^ e') := by
  rw [ruA0Elt, ruA0Elt, ← pi7Word_append]
  refine pi7Word_eq_of_mem_align (List.mem_append_left _ (List.mem_append_left _ ?_))
  exact List.mem_flatMap.2
    ⟨e, List.mem_range.2 he, List.mem_map.2 ⟨e', List.mem_range.2 he', rfl⟩⟩

theorem mem_ruA0_iff {a : Pi7} : a ∈ ruA0 ↔ ∃ e < 8, a = ruA0Elt e := by
  constructor
  · intro ha
    induction ha using closure_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      change w ∈ ruA0Words at hw
      simp only [ruA0Words, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨1, by norm_num, congrArg pi7Word (by decide)⟩
      · exact ⟨2, by norm_num, congrArg pi7Word (by decide)⟩
      · exact ⟨4, by norm_num, congrArg pi7Word (by decide)⟩
    | one => exact ⟨0, by norm_num, ruA0Elt_zero.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨e, he, rfl⟩ := hx
      obtain ⟨e', he', rfl⟩ := hy
      exact ⟨e ^^^ e', xor_lt_eight he he', ruA0Elt_mul he he'⟩
    | inv x _ hx =>
      obtain ⟨e, he, rfl⟩ := hx
      refine ⟨e, he, inv_eq_of_mul_eq_one_right ?_⟩
      rw [ruA0Elt_mul he he, Nat.xor_self, ruA0Elt_zero]
  · rintro ⟨e, -, rfl⟩
    exact ruA0Elt_mem e

theorem ruA0Elt_eq_conj {k : ℕ} (hk : k < 7) :
    ruA0Elt (k + 1) = pi7Word (ruAlignTransWords.getD k []) * ruZ0 *
      (pi7Word (ruAlignTransWords.getD k []))⁻¹ := by
  rw [ruZ0, ← pi7Word_invWord, ← pi7Word_append, ← pi7Word_append, ruA0Elt]
  refine (pi7Word_eq_of_mem_align (List.mem_append_left _ (List.mem_append_right _ ?_))).symm
  exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

theorem ruM2_trans_A0 {a : Pi7} (ha : a ∈ ruA0) (ha1 : a ≠ 1) :
    ∃ m ∈ ruM2, m * ruZ0 * m⁻¹ = a := by
  obtain ⟨e, he, rfl⟩ := mem_ruA0_iff.1 ha
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := by
    rcases e with _ | k
    · exact absurd ruA0Elt_zero ha1
    · exact ⟨k, rfl⟩
  have hk : k < 7 := by omega
  exact ⟨_, pi7Word_mem_letterSub (ruAlignTransWords_letters k hk), (ruA0Elt_eq_conj hk).symm⟩

theorem ruM2Letter_conj {i j : ℕ} (hi : i < 6) (hj : j < 3) :
    PresentedGroup.of (ruM2Letters.getD i 0) * pi7Word (ruA0Words.getD j []) *
        (PresentedGroup.of (ruM2Letters.getD i 0))⁻¹ =
      ruA0Elt (ruAlignNormData.getD (3 * i + j) (0, 0)).1 ∧
    (PresentedGroup.of (ruM2Letters.getD i 0))⁻¹ * pi7Word (ruA0Words.getD j []) *
        PresentedGroup.of (ruM2Letters.getD i 0) =
      ruA0Elt (ruAlignNormData.getD (3 * i + j) (0, 0)).2 := by
  have hmem : ∀ p ∈ [([(ruM2Letters.getD i 0, true)] ++ ruA0Words.getD j [] ++
        [(ruM2Letters.getD i 0, false)], ruA0PowWord (ruAlignNormData.getD (3 * i + j) (0, 0)).1),
      ([(ruM2Letters.getD i 0, false)] ++ ruA0Words.getD j [] ++
        [(ruM2Letters.getD i 0, true)], ruA0PowWord (ruAlignNormData.getD (3 * i + j) (0, 0)).2)],
      p ∈ ruAlignMulPairs ++ ruAlignTransPairs ++ ruAlignNormPairs := fun p hp =>
    List.mem_append_right _ (List.mem_flatMap.2
      ⟨i, List.mem_range.2 hi, List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, hp⟩⟩)
  constructor
  · rw [← pi7Word_letter_inv, ← pi7Word_letter, ← pi7Word_append, ← pi7Word_append, ruA0Elt]
    exact pi7Word_eq_of_mem_align (hmem _ List.mem_cons_self)
  · rw [← pi7Word_letter_inv, ← pi7Word_letter, ← pi7Word_append, ← pi7Word_append, ruA0Elt]
    exact pi7Word_eq_of_mem_align (hmem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem ruM2_le_normalizer : ruM2 ≤ normalizer (ruA0 : Set Pi7) := by
  refine (closure_le _).2 ?_
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨i, hi, rfl⟩ := ruM2Letters_eq_getD l hl
  have hS : ∀ (g : Pi7), (∀ w ∈ ruA0Words, ∃ e, g * pi7Word w * g⁻¹ = ruA0Elt e) →
      ∀ x ∈ ruA0, g * x * g⁻¹ ∈ ruA0 := fun g hg x hx => by
    refine conj_mem_of_mem_closure ?_ hx
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨e, he⟩ := hg w hw
    rw [he]
    exact ruA0Elt_mem e
  have h₁ := hS (PresentedGroup.of (ruM2Letters.getD i 0)) fun w hw => by
    obtain ⟨j, hj, rfl⟩ := ruA0Words_eq_getD w hw
    exact ⟨_, (ruM2Letter_conj hi hj).1⟩
  have h₂ := hS (PresentedGroup.of (ruM2Letters.getD i 0))⁻¹ fun w hw => by
    obtain ⟨j, hj, rfl⟩ := ruA0Words_eq_getD w hw
    exact ⟨_, by rw [inv_inv]; exact (ruM2Letter_conj hi hj).2⟩
  refine mem_normalizer_iff.2 fun n => ⟨fun hn => h₁ n hn, fun hn => ?_⟩
  have h3 := h₂ _ hn
  rwa [inv_inv, show ∀ g : Pi7, g⁻¹ * (g * n * g⁻¹) * g = n from fun g => by group] at h3

theorem ruAlignFacts : RuAlignFacts where
  M2_le := ruM2_le_normalizer
  trans_A0 := fun _ ha ha1 => ruM2_trans_A0 ha ha1

end CFSG.ComponentClassification.GMS78.RuAsm
