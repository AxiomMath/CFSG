module

public import CFSG.GH74.GLS.Classes
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup

structure NbhdHyp (H : Type) [Group H] [Finite H] (q : ℕ) (w y : H) (J₂ J₄ : Subgroup H) : Prop where
  odd : Odd q
  five : 5 ≤ q
  core : pPrimeCore 2 H = ⊥
  gen4 : Gen4 H
  kgroup : IsKGroupNative H
  gh : ∀ (A : Subgroup H) (B : Subgroup ↥A) [B.Normal], IsSimpleGroup (↥A ⧸ B) →
    (∃ a b : ↥A ⧸ B, a * b ≠ b * a) → GHList (↥A ⧸ B)
  w_central : ∀ h : H, h * w = w * h
  w_sq : w * w = 1
  w_ne_one : w ≠ 1
  y_sq : y * y = 1
  y_ne_one : y ≠ 1
  w_ne_y : w ≠ y
  w_mem : w ∈ J₂
  y_mem : y ∈ J₄
  y_cent : ∀ b ∈ J₄, y * b = b * y
  sl₂ : HasSL2Model ↥J₂ (fun r => r = q)
  sl₄ : HasSL2Model ↥J₄ (fun r => r = q)
  cent₂ : ∀ a ∈ J₂, (∀ b ∈ J₂, a * b = b * a) → a = 1 ∨ a = w
  cent₄ : ∀ a ∈ J₄, (∀ b ∈ J₄, a * b = b * a) → a = 1 ∨ a = y
  comm : ∀ a ∈ J₂, ∀ b ∈ J₄, a * b = b * a
  comp₂ : IsComponent (J₂.subgroupOf (centralizer ({w * y} : Set H)))
  comp₄ : IsComponent (J₄.subgroupOf (centralizer ({w * y} : Set H)))
  bal : ∀ L : Subgroup ↥(centralizer ({w * y} : Set H)), IsComponent L →
    L.map (centralizer ({w * y} : Set H)).subtype ≤ J₂ ⊔ J₄
  le_layer : J₂ ⊔ J₄ ≤ layer H
  growth : ¬ layer H ≤ J₂ ⊔ J₄

@[expose] def NoCommonComponent {H : Type} [Group H] (J₂ J₄ : Subgroup H) : Prop :=
  ∀ K : Subgroup H, IsComponent K → ¬ (J₂ ≤ K ∧ J₄ ≤ K)

end CFSG.GH74.Generic.S1.Exo
