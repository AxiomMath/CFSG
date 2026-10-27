module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParW
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverBig

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
  CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.Quasithin

@[expose] def HasBQ (Y : Type) [Group Y] : Prop :=
  ∃ (K : Type) (_ : Group K) (_ : Finite K) (D : UniversalRootDatum K) (n : Fin D.rank → K)
    (H : Fin D.rank → Subgroup K) (π : K →* Y) (M : ℕ), BorelQuotient D n H π M

theorem nonempty_minParData_of_hasBQ {W : Type} [Group W] [Finite W] {L S₀ : Subgroup W}
    (hS : IsSylowTwoOf S₀ L) (h : HasBQ (↥L ⧸ Subgroup.center ↥L)) :
    Nonempty (MinParData L S₀) := by
  obtain ⟨K, _, _, D, n, H, π, M, hπ⟩ := h
  obtain ⟨π', hπ', hT⟩ := exists_borelQuotient_conj hS hπ
  have D0 := minParData_of_borelQuotient hπ'
  rw [← hT] at D0
  exact ⟨minParData_of_center D0 hS⟩

theorem minParabolic_of_hasBQ {W : Type} [Group W] [Finite W] {L R P : Subgroup W}
    (hR : R ≤ Subgroup.normalizer (L : Set W)) (hR2 : IsPGroup 2 R)
    (hS : IsSylowTwoOf (R ⊓ L) L) (hP : IsMinOverBorel L (R ⊓ L) P)
    (h : HasBQ (↥L ⧸ Subgroup.center ↥L)) :
    ∃ M : Subgroup W, MinParabolic (pElementSubgroup 2 (conjClosure P R) ⊔ R) R M := by
  obtain ⟨D⟩ := nonempty_minParData_of_hasBQ hS h
  exact minParabolic_of_minParData hR hR2 hS hP D

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
