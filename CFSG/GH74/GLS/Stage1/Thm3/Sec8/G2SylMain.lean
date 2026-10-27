module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylFwd

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

open CFSG.Blueprint

theorem g2_sylow_shape : G2_Sylow_shape := by
  intro X _ _ S A a t y n _ hshape p f hp hp2 hf hval
  exact g2_sylow_of_shapeConds hshape p f hp hp2 hf hval

theorem g2_sylow_shape_fwd :
    ∀ (Gs : Type) [Group Gs] [Finite Gs] (p f : ℕ), p.Prime → p ≠ 2 → 0 < f →
      LieModel Gs .G2 0 p f → ∀ S' : Sylow 2 Gs, ∃ (A : Subgroup Gs) (a t y : Gs) (n : ℕ),
        2 ≤ n ∧ G2Shape (S' : Subgroup Gs) A a t y n ∧
          ((p ^ f) ^ 2 - 1).factorization 2 = n + 1 :=
  g2_sylow_shapeConds_fwd

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl
