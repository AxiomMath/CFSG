module

public import CFSG.ClassicalInvolution.Phan.PhanS15Geom
import CFSG.ClassicalInvolution.Phan.PhanS6T9Main
import CFSG.ClassicalInvolution.Phan.PhanS7P4Main

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.ClassicalInvolution.PhanB3.H

section Fin

variable {p f : ℕ} [Fact p.Prime]

theorem phanB3Std_of_dict_geom (hd : PhanB3StdDict p f)
    (hg : ∀ (K : Type) [Field K] [Finite K] (M : Std.Model K), 5 ≤ M.q → M.q % 4 = 3 →
      M.q = p ^ f → Std.DiamTwo M ∧ Std.TriNull M ∧ Std.QuadNullStd M ∧ Std.PentNullStd M) :
    PhanB3StdSimplyTwoConnected p f := by
  refine phanB3Std_of_pointGeometry ?_
  intro hp2 hq hmod hK h2 C M E hgood hrange
  obtain ⟨SM, hSMq, ⟨D⟩⟩ := hd hp2 hq hmod hK h2 C M E hgood hrange
  obtain ⟨h1, h2', h3, h4⟩ :=
    hg _ SM (by rw [hSMq]; exact hq) (by rw [hSMq]; exact hmod) hSMq
  exact D.pointGeometry h1 h2' h3 h4

theorem phanB3Std_of_dict_ne_seven (hd : PhanB3StdDict p f) (h7 : p ^ f ≠ 7) :
    PhanB3StdSimplyTwoConnected p f := by
  refine phanB3Std_of_dict_geom hd ?_
  intro K _ _ M hq hmod hMq
  have hne : M.q ≠ 7 := by
    rw [hMq]
    exact h7
  have hq11 : 11 ≤ M.q := by omega
  have hq7 : 7 ≤ M.q := by omega
  have hQ : Std.QuadNullStd M := Std.Q.quadNull_of_model M hq11
  exact ⟨Std.D.diamTwo_of_model M hq7, Std.T.triNull_of_model M hq7, hQ,
    Std.P.pentNullStd_of_model M hq7 hQ⟩

theorem phanB3Std_of_dict_q7 (hd : PhanB3StdDict p f) (h7 : Q7Residual) :
    PhanB3StdSimplyTwoConnected p f :=
  phanB3Std_of_dict hd (stdGeometryFacts_of_q7 h7)

end Fin

end CFSG.ClassicalInvolution.PhanB3.S
