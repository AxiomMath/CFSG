module

public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Steinberg.Adjoint.Perfect

public section

namespace CFSG.LieType.CurtisTits

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint

universe w

variable (p f : ℕ) [Fact p.Prime]

private theorem lieModel_adjoint {t : StatedLieTag} {τ : Tag} (ht : t ∈ chevalleyExceptionalTags)
    (hmodel : ∀ G : Type, [Group G] → (∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = p ^ f ∧ Nonempty (G ≃* AdjointQuotient τ K)) →
        ChevalleyExceptionalModel G t p f)
    (hcard : Nat.card (GaloisField p f) = p ^ f) :
    LieModel (AdjointQuotient τ (GaloisField p f)) t 0 p f :=
  Or.inr (Or.inl ⟨rfl, ht, hmodel _ ⟨GaloisField p f, inferInstance, inferInstance, hcard,
    ⟨MulEquiv.refl _⟩⟩⟩)

theorem curtisTitsConclusion_f4 (hadm : StatedLieAdmissible .F4 0 p f) :
    CurtisTitsConclusion.{w} (f4Datum (GaloisField p f)) .F4 0 p f :=
  curtisTitsConclusion_of (f4_isCTGroupDatum _) (f4_steinbergExtras _) (by change 0 < 4; norm_num)
    (isQuasisimple_f4 _)
    (lieModel_adjoint p f (τ := .F4) (by decide) (fun _ _ h => ⟨hadm, h⟩)
      (GaloisField.card p f (by have := hadm.2.1; omega)))

theorem curtisTitsConclusion_e8 (hadm : StatedLieAdmissible .E8 0 p f) :
    CurtisTitsConclusion.{w} (e8Datum (GaloisField p f)) .E8 0 p f :=
  curtisTitsConclusion_of (e8_isCTGroupDatum _) (e8_steinbergExtras _) (by change 0 < 8; norm_num)
    (isQuasisimple_e8 _)
    (lieModel_adjoint p f (τ := .E8) (by decide) (fun _ _ h => ⟨hadm, h⟩)
      (GaloisField.card p f (by have := hadm.2.1; omega)))

end CFSG.LieType.CurtisTits
