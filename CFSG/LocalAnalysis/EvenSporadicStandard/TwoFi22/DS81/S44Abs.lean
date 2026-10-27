module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44AbsShape
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44AbsClosed

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44

open Subgroup MulAction

theorem cocodeMain (hGL : GLDvdStmt) (h2047 : NoCard2047Stmt) (hOrb : Orbit23Stmt)
    (hSimple : SimpleOfShapeStmt) : CocodeMainStmt := by
  intro V _ _ hV hsq X M t O hMX hO hM hY hmove hν
  have hcardX : Nat.card X = (orbit X t).ncard * 887040 := by
    rw [Abs.card_eq_mul, hY]
  have hdvd : (orbit X t).ncard * 887040 ∣
      2 ^ 55 * 3 ^ 6 * 5 ^ 2 * 7 ^ 3 * 11 * 17 * 23 * 31 ^ 2 * 73 * 89 * 127 := by
    have := hGL hV hsq X
    rwa [hcardX] at this
  rcases Abs.shape hMX hO hν hmove hdvd with
    ⟨hc, -, h1, h2, h3, h4⟩ | ⟨hc, h0, h1, h4, h23⟩ | ⟨hc, -⟩
  · exact (Abs.not_card_45 hV hsq hMX hO hν h1 h2 h3 h4 hc).elim
  · have hX : Nat.card X = 244823040 := by
      calc Nat.card X = (orbit X t).ncard * 887040 := hcardX
        _ = 276 * 887040 := by rw [hc]
        _ = 244823040 := rfl
    refine ⟨hSimple hV hsq X M t O hMX hO hM hY hν hX hc, hX, hc, ?_⟩
    refine Abs.exists_rest hMX hO (fun y hy => ?_) h0 h1 h4 h23
    have := hOrb hV hsq X hX y hy
    rwa [Nat.card_coe_set_eq] at this
  · refine (h2047 hV hsq X ?_).elim
    calc Nat.card X = (orbit X t).ncard * 887040 := hcardX
      _ = 2047 * 887040 := by rw [hc]
      _ = 23 * 89 * 887040 := rfl

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44
