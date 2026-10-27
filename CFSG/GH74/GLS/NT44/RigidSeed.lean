module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
public import CFSG.GH74.GLS.C3.Layer1.Defs
import CFSG.GH74.GLS.Bg.Iii2.L41Main
public import CFSG.GH74.GLS.TwoThin.Rank

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem exists_rigidSeed (hnonab : ∃ a b : G, a * b ≠ b * a)
    {x : G} {K : Subgroup G} (hterm : IsTwoTerminal x K)
    (hZ : center (kBar K) ≠ ⊥) :
    ∃ (z : G) (J : Subgroup G), IsRigidOfType (kBar K) z J := by
  have h3 : 3 ≤ pRank 2 G := by
    have h1 : IsILo 2 x K := hterm.1
    have h2 : oBound 2 ≤ pRank 2 ↥(centralizer ({x} : Set G)) := h1.2.1
    have h3' : oBound 2 = 3 := by simp [oBound]
    exact (h3' ▸ h2).trans (CFSG.GH74.GLS.Bg.pRank_subgroup_le (by norm_num) _)
  have hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) :=
    fun y hy => CFSG.GH74.GLS.TwoThin.rankThreeCentralizers G (inferInstance : IsSimpleGroup G)
      hnonab h3 y hy
  obtain ⟨z, L, hP, hLK⟩ :=
    CFSG.GH74.GLS.Bg.Iii2.L41.exists_goodPair hR hterm hZ
  exact ⟨z, L, CFSG.GH74.GLS.Bg.Iii2.L41.isPRigid_of_goodPair hP, hLK⟩

theorem exists_rigidSeed_of_center_card_sixteen
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {x : G} {K : Subgroup G} (hterm : IsTwoTerminal x K)
    (hZ : Nat.card (center (kBar K)) = 16) :
    ∃ (z : G) (J : Subgroup G), IsRigidOfType (kBar K) z J := by
  apply exists_rigidSeed hnonab hterm
  intro hbot
  rw [hbot, Subgroup.card_bot] at hZ
  exact absurd hZ (by norm_num)

end CFSG.GH74.GLS.NT44
