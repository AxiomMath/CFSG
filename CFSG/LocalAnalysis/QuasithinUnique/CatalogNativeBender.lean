module

public import CFSG.GH74.Bender.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover

public section

namespace CFSG.QuasithinUnique

theorem catalog_of_mulEquiv_psu3 {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* CFSG.Open.PSU3 2 f) : CFSG.Blueprint.Catalog X :=
  CFSG.Blueprint.lieModel_catalog X .PSU 3 2 f
    (CFSG.ShultStronglyClosedTI.unitaryCover_equiv_lieModel (K := GaloisField 2 (2 * f)) f hf
      (GaloisField.card 2 (2 * f) (by omega))
      (e.trans (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative f).symm))

theorem catalog_of_mulEquiv_sz {X : Type} [Group X] {a : ℕ} (ha : 1 ≤ a)
    (e : X ≃* CFSG.Open.Sz a) : CFSG.Blueprint.Catalog X :=
  Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr
    ⟨2, 2 * a + 1, CFSG.GH74.Bender.suzukiModel_of_mulEquiv_sz ha e⟩)))))

end CFSG.QuasithinUnique
