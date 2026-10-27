module

public import CFSG.ClassicalInvolution.Phan.PhanS6Dict
import CFSG.ClassicalInvolution.Phan.PhanS6T9Main
import CFSG.ClassicalInvolution.Phan.PhanS7P4Main
public import CFSG.ClassicalInvolution.Phan.PhanS8Q10Final

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

@[expose] def Q7Residual : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (M : Std.Model K), M.q = 7 → Std.Q.BBQuad M

theorem q7Residual_of_hardWay
    (h : ∀ (K : Type) [Field K] [Finite K] (M : Std.Model K), M.q = 7 → Std.Q.HardWay M) :
    Q7Residual :=
  fun K _ _ M hM => Std.Q.bbQuad_of_hardWay (h K M hM)

theorem stdGeometryFacts_of_q7 (h7 : Q7Residual) : StdGeometryFacts := by
  intro K _ _ M hq hmod
  have hq7 : 7 ≤ M.q := by omega
  have hQ : Std.QuadNullStd M := by
    by_cases h : M.q = 7
    · exact Std.Q.quadNull_of_BB M hq7 (h7 K M h)
    · exact Std.Q.quadNull_of_model M (by omega)
  exact ⟨Std.D.diamTwo_of_model M hq7, Std.T.triNull_of_model M hq7, hQ,
    Std.P.pentNullStd_of_model M hq7 hQ⟩

end CFSG.ClassicalInvolution.PhanB3.S
