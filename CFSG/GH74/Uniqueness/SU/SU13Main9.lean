module

public import CFSG.GH74.Uniqueness.SU.SU13TC6G
public import CFSG.GH74.Uniqueness.SU.SU13Main10
public import CFSG.GH74.Uniqueness.SU.SU13TA9Loc9
public import CFSG.GH74.Uniqueness.SU.SU13Stmts

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74

variable {G : Type} [Group G] [Finite G] {z : G}

theorem epart10_of_epart9 {e : Elts G z} {e9 : Elts9 z e} {f : FPart z e} (E9 : EPart9 z e e9 f) :
    EPart10 z e :=
  ⟨⟨E9.E, E9.Es, E9.s₁_mem, E9.Es_ge, E9.E_card, E9.E_abel, E9.Es_p, E9.Es_card, E9.Es_comm, E9.Es_max,
    E9.E_unique, E9.cent⟩⟩

theorem false_of_loc9_of_ki8c (hKI7d : K.KI7d) (hKI8c : K.KI8c) [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hz : orderOf z = 2)
    (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 9) (L : Loc9 G z) : False := by
  have l : Lem232 z L.e := lemma232_nine hnab hz L.e L.f.toFPart L.p3 L.m
  have l3 : Lem233 z L.e L.E.E :=
    lemma233_nine hKI8c hz L.e l L.m L.E.E_card L.E.E_exp L.E.E_abel
  have h3 : 3 ^ 5 ∣ Nat.card (centralizer ({L.e.s₂} : Set G)) := by
    rcases l3.C_card with h | h <;> rw [h] <;> norm_num
  have h38 : 3 ^ 8 ∣ Nat.card (centralizer ({L.e.s₂} : Set G)) := by
    rcases l3.C_card with h | h <;> rw [h] <;> norm_num
  have hW5 := W_card9 hKI7d hH hz L.e L.f l (epart10_of_epart9 L.E) h3
  have hWc := W_comm hz L.e L.f l hW5 h38
  have h39 := three_pow_nine_dvd L.f L.E hWc hz hW5 l L.m
  exact (Ctx9.mk L hz l l3 hWc hW5 h39).false_of_ctx9

theorem thm231_nine_of_ki8c (hKI7d : K.KI7d) (hKI8c : K.KI8c) (G : Type) [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (z : G)
    (hz : orderOf z = 2) : ¬ K.IsTwoAlt ↥(centralizer ({z} : Set G)) 9 := by
  intro hH
  have := hs
  obtain ⟨loc⟩ := loc9_of_isTwoAlt hz hH
  exact false_of_loc9_of_ki8c hKI7d hKI8c hnab hz hH loc

theorem thm231_of_ki7d_ki8bc (hKI7d : K.KI7d) (hKI8b : K.KI8b) (hKI8c : K.KI8c) : Thm231Stmt := by
  intro G _ _ hs hnab z hz n hn
  rcases hn with rfl | rfl
  · exact thm231_nine_of_ki8c hKI7d hKI8c G hs hnab z hz
  · exact thm231_ten_of_ki8b hKI7d hKI8b G hs hnab z hz

end CFSG.GH74.Uniqueness.SU.SU13
