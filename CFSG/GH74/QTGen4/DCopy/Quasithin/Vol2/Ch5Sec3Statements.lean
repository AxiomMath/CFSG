module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5Sec3Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Stmt5_3_4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfLieType52 M L H B D T t m f → IsSec53Param t m f →
      LieModel G t m 2 f ∨
      (t = .PSL ∧ m = 3 ∧ ∀ z ∈ sec53ZS T L, orderOf z = 2 →
        ¬ Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H)

@[expose] def Stmt5_3_7_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n f : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfLieType52 M L H B D T .PSL 3 f → 2 ≤ f →
    (∀ z ∈ sec53ZS T L, orderOf z = 2 →
      ¬ Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H) →
    ∀ z ∈ sec53ZS T L, orderOf z = 2 → Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H

@[expose] def Stmt5_3_Lie_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfLieType52 M L H B D T t m f → IsSec53Param t m f → LieModel G t m 2 f

theorem stmt5_3_Lie_of_F4 (h534 : Stmt5_3_4_F4) (h537 : Stmt5_3_7_F4) : Stmt5_3_Lie_F4 := by
  intro G _ _ T M L V H B D L₂ n t m f hyp hty hpar
  rcases h534 G T M L V H B D L₂ n t m f hyp hty hpar with h | ⟨rfl, rfl, h2⟩
  · exact h
  · exfalso
    obtain ⟨z, hz, hz2⟩ := exists_involution_sec53ZS hyp.toHyp5_0_1
    exact h2 z hz hz2 (h537 G T M L V H B D L₂ n f hyp hty hpar.1 h2 z hz hz2)

end CFSG.Quasithin.H13
