module

public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LieType.Universal.Unitary.Extras

public section

namespace CFSG.LieType.CurtisTits

open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary

universe w

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {n : ℕ}

theorem curtisTitsConclusion_unitary (hadm : StatedLieAdmissible .PSU n p f)
    (hF : Nat.card F = (p ^ f) ^ 2) :
    CurtisTitsConclusion.{w} (rootDatum hF n) .PSU n p f := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hn : 3 ≤ n := hadm.2.2.1
  exact curtisTitsConclusion_of (isCTGroupDatum hF n (by omega) ζ hζ)
    (steinbergExtras hF n (by omega) ζ hζ) (by change 0 < n / 2; omega)
    (isQuasisimple_SU hF hn hadm.2.2.2)
    (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], statedClassicalModel_center_quotient hadm hF⟩)

end CFSG.LieType.CurtisTits
