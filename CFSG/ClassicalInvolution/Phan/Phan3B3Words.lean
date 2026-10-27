module

public import CFSG.ClassicalInvolution.Phan.Phan3AModel

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

variable {n k : ℕ} {G : Type*} [Group G]

theorem wordVal_append (g : Fin n → G) (u v : List (Fin n × Bool)) :
    wordVal g (u ++ v) = wordVal g u * wordVal g v := by
  simp [wordVal]

theorem wordVal_invWord (g : Fin n → G) (u : List (Fin n × Bool)) :
    wordVal g (invWord u) = (wordVal g u)⁻¹ := by
  induction u with
  | nil => simp [invWord, wordVal]
  | cons l u ih =>
    have h : invWord (l :: u) = invWord u ++ [(l.1, !l.2)] := by simp [invWord]
    rw [h, wordVal_append, ih]
    obtain ⟨i, b⟩ := l
    cases b <;> simp [wordVal, letterVal]

theorem wordVal_reindex (g : Fin n → G) (f : Fin k → Fin n) (r : List (Fin k × Bool)) :
    wordVal g (r.map fun l => (f l.1, l.2)) = wordVal (fun i => g (f i)) r := by
  induction r with
  | nil => rfl
  | cons l r ih =>
    simp only [wordVal, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    rfl

theorem wordVal_flatMap (y : Fin n → G) (h : Fin k → G)
    (s : Fin k × Bool → List (Fin n × Bool)) (hs : ∀ l, wordVal y (s l) = letterVal h l)
    (w : List (Fin k × Bool)) : wordVal y (w.flatMap s) = wordVal h w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.flatMap_cons, wordVal_append, ih, hs]
    simp [wordVal]

theorem wordVal_comm_iff (g : Fin n → G) (u v : List (Fin n × Bool)) :
    wordVal g (u ++ v ++ invWord u ++ invWord v) = 1 ↔ wordVal g u * wordVal g v =
      wordVal g v * wordVal g u := by
  rw [wordVal_append, wordVal_append, wordVal_append, wordVal_invWord, wordVal_invWord]
  constructor
  · intro h
    have h1 : wordVal g u * wordVal g v * (wordVal g u)⁻¹ * (wordVal g v)⁻¹ = 1 := h
    calc wordVal g u * wordVal g v = (wordVal g u * wordVal g v * (wordVal g u)⁻¹ *
          (wordVal g v)⁻¹) * (wordVal g v * wordVal g u) := by group
      _ = wordVal g v * wordVal g u := by rw [h1, one_mul]
  · intro h
    show wordVal g u * wordVal g v * (wordVal g u)⁻¹ * (wordVal g v)⁻¹ = 1
    rw [h]
    group

end CFSG.ClassicalInvolution.Phan.Q3G
