module

public import CFSG.CGT.T75H.D8Data

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G}

structure SylowData (T T₁ : Subgroup G) (S : Sylow 2 G) : Prop where
  le : sStar T T₁ ≤ S
  norm : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (T : Set G)
  hSH : (S : Subgroup G) ⊓ hSub T (normIn T₁ T) = sStar T T₁
  dS : ∀ y ∈ (S : Subgroup G), y ∈ classD T → y ∈ sStar T T₁

theorem SylowData.sStar_norm {S : Sylow 2 G} (hS : SylowData T T₁ S) :
    ∀ s ∈ (S : Subgroup G), ∀ z ∈ sStar T T₁, s * z * s⁻¹ ∈ sStar T T₁ := by
  intro s hs z hz
  rw [← hS.hSH] at hz ⊢
  exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs hz.1) ((S : Subgroup G).inv_mem hs),
    mul_mul_inv_mem_hSub (hS.norm s hs) hz.2⟩

namespace D8Data

variable {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)

include D

theorem mem_classD_of_invol {z : G} (hz : z ∈ sStar T T₁) (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hconj : ∃ x : G, T₁ = conjSubgroup x T) : z ∈ classD T := by
  by_cases hzT : z ∈ T
  · exact mem_classD_of_mem hzT hz1
  · have hℓD : ℓ ∈ classD T := by
      obtain ⟨x, hx⟩ := hconj
      exact mem_classD_of_mem_conjSubgroup (hx ▸ D.hℓT₁) D.hℓ1
    rcases D.invol_class hz hzz hzT with h | h
    · rw [h]; exact hℓD
    · have := classD_conj hℓD b
      rw [D.inv_b, D.conj_ℓ_b] at this
      rw [h]; exact this

end D8Data

end CFSG.CGT.T75H
