module

public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WordG

open CFSG.Sporadic.Th

theorem wordG_nil {G : Type*} [Group G] (g : ℤ → G) : wordG g [] = 1 := by simp [wordG]

theorem wordG_cons {G : Type*} [Group G] (g : ℤ → G) (z : ℤ) (l : List ℤ) :
    wordG g (z :: l) = g z * wordG g l := by simp [wordG]

theorem wordG_append {G : Type*} [Group G] (g : ℤ → G) (l₁ l₂ : List ℤ) :
    wordG g (l₁ ++ l₂) = wordG g l₁ * wordG g l₂ := by simp [wordG]

theorem wordG_replicate {G : Type*} [Group G] (g : ℤ → G) (n : ℕ) (z : ℤ) :
    wordG g (List.replicate n z) = g z ^ n := by simp [wordG]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WordG
