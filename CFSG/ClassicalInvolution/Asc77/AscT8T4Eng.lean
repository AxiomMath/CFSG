module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.WP2Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8T

section Sigma

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem alphaOf_eq_of_mem_dCompE
    (hsymm : ∀ {A B : Subgroup G}, A ∈ Ω → B ∈ Ω → B ∈ omegaNbr Ω A → A ∈ omegaNbr Ω B)
    (huniq : ∀ {A : Subgroup G}, A ∈ Ω → ∃ y : G, IsUniqueInvolution A y)
    (hA : ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z → ∀ J₁ ∈ omegaNbr Ω K, ∀ J₂ ∈ omegaNbr Ω K,
      ∀ t₁ t₂ : G, IsUniqueInvolution J₁ t₁ → IsUniqueInvolution J₂ t₂ →
        alphaOf (Subgroup.closure ({t₁, z} : Set G)) =
          alphaOf (Subgroup.closure ({t₂, z} : Set G)))
    {K J : Subgroup G} {z t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hJ : J ∈ omegaNbr Ω K) (ht : IsUniqueInvolution J t) {L : Subgroup G} (hL : L ∈ dComp Ω K) :
    L ∈ Ω ∧ ∀ L' ∈ omegaNbr Ω L, ∀ y y' : G, IsUniqueInvolution L y → IsUniqueInvolution L' y' →
      alphaOf (Subgroup.closure ({y', y} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) := by
  induction hL with
  | refl =>
    refine ⟨hK, fun L' hL' y y' hy hy' => ?_⟩
    have hyz : y = z := hy.eq hz
    rw [hyz]
    exact hA K hK z hz L' hL' J hJ y' t hy' ht
  | @tail b c hbk hbc ih =>
    obtain ⟨hbΩ, hPb⟩ := ih
    obtain ⟨hcΩ, hadj⟩ := hbc
    have hcb : c ∈ omegaNbr Ω b ∧ b ∈ omegaNbr Ω c := by
      rcases hadj with h | h
      · exact ⟨h, hsymm hbΩ hcΩ h⟩
      · exact ⟨hsymm hcΩ hbΩ h, h⟩
    refine ⟨hcΩ, fun L'' hL'' y₂ y'' hy₂ hy'' => ?_⟩
    obtain ⟨yb, hyb⟩ := huniq hbΩ
    have h1 : alphaOf (Subgroup.closure ({y'', y₂} : Set G)) =
        alphaOf (Subgroup.closure ({yb, y₂} : Set G)) :=
      hA c hcΩ y₂ hy₂ L'' hL'' b hcb.2 y'' yb hy'' hyb
    have h2 : alphaOf (Subgroup.closure ({y₂, yb} : Set G)) =
        alphaOf (Subgroup.closure ({t, z} : Set G)) := hPb c hcb.1 yb y₂ hyb hy₂
    rw [h1, Set.pair_comm]
    exact h2

end Sigma

end T8T

end CFSG.ClassicalInvolution.Asc77
