module

public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.LieType.CurtisTits

open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.Assembly.LowTwoRank
  CFSG.Blueprint

universe w

variable (m : ℕ) (F : Type) [Field F]

theorem isUniversalCompletion_specialLinear :
    IsUniversalCompletion.{0, 0, w} (rootDatum m F).leviAmalgam :=
  (rootDatum m F).isUniversalCompletion_of_steinbergPresentation (isCTGroupDatum m F)
    (CFSG.LieType.Steinberg.steinbergPresentation_of_extras (isCTGroupDatum m F)
      (steinbergExtras m F))

variable {m F}

theorem curtisTitsConclusion_specialLinear [Finite F] {p f : ℕ}
    (hadm : StatedLieAdmissible .PSL (m + 1) p f) (hF : Nat.card F = p ^ f) (hm : 3 ≤ m) :
    CurtisTitsConclusion.{w} (rootDatum m F) .PSL (m + 1) p f :=
  curtisTitsConclusion_of (isCTGroupDatum m F) (steinbergExtras m F) (by change 0 < m; omega)
    (isQuasisimple m F (by omega))
    (Or.inl ⟨by simp [classicalTags], statedClassicalModel_center_quotient m F hadm hF⟩)

end CFSG.LieType.CurtisTits
