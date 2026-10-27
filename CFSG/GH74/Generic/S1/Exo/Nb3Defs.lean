module

public import CFSG.GH74.GLS.Classes
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup

structure Nbhd3Hyp (H : Type) [Group H] [Finite H] (c y : H) (JA JB : Subgroup H) : Prop where
  core : pPrimeCore 2 H = ⊥
  gen4 : Gen4 H
  kgroup : IsKGroupNative H
  gh : ∀ (A : Subgroup H) (B : Subgroup ↥A) [B.Normal], IsSimpleGroup (↥A ⧸ B) →
    (∃ a b : ↥A ⧸ B, a * b ≠ b * a) → GHList (↥A ⧸ B)
  c_central : ∀ h : H, h * c = c * h
  c_sq : c * c = 1
  c_ne_one : c ≠ 1
  y_sq : y * y = 1
  y_ne_one : y ≠ 1
  c_ne_y : c ≠ y
  c_mem : c ∈ JA
  y_mem : y ∈ JB
  y_cent : ∀ b ∈ JB, y * b = b * y
  sl2A : HasSL2Model ↥JA (fun r => r = 3)
  sl2B : HasSL2Model ↥JB (fun r => r = 3)
  centA : ∀ a ∈ JA, (∀ b ∈ JA, a * b = b * a) → a = 1 ∨ a = c
  centB : ∀ a ∈ JB, (∀ b ∈ JB, a * b = b * a) → a = 1 ∨ a = y
  comm : ∀ a ∈ JA, ∀ b ∈ JB, a * b = b * a
  perfect_free : ∀ M : Subgroup H, ⁅M, M⁆ = M → M ≤ centralizer ({c * y} : Set H) → M = ⊥
  balA : (∀ g ∈ JA, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ pCore 2 H) ∨
    ∃ N : Subgroup H, IsComponent N ∧ ∀ g ∈ JA, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ N
  balB : (∀ g ∈ JB, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ pCore 2 H) ∨
    ∃ N : Subgroup H, IsComponent N ∧ ∀ g ∈ JB, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ N

end CFSG.GH74.Generic.S1.Exo
