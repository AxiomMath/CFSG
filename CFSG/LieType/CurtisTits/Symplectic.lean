module

public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.LieType.CurtisTits

open CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.Assembly.LowTwoRank
  CFSG.Blueprint

universe w

variable {n : ℕ} {F : Type} [Field F]

theorem curtisTitsConclusion_symplectic [Finite F] {p f : ℕ}
    (hadm : StatedLieAdmissible .PSp n p f) (hF : Nat.card F = p ^ f) (hn : 3 ≤ n) :
    CurtisTitsConclusion.{w} (rootDatum n F) .PSp n p f :=
  curtisTitsConclusion_of (isCTGroupDatum n F) (steinbergExtras n F) (by change 0 < n; omega)
    (isQuasisimple_of_admissible n F hadm hF)
    (Or.inl ⟨by simp [classicalTags], statedClassicalModel_center_quotient n F hadm hF⟩)

end CFSG.LieType.CurtisTits
