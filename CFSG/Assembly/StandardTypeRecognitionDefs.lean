module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.InCatalog

public section

namespace CFSG.Assembly

open scoped MatrixGroups

theorem standardTypeRecognitionRawDatum_mono {lab : LargeEvenLabel}
    {Q Q' : LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → Q' R I F)
    (h : LargeEvenRawDatum lab Q) : LargeEvenRawDatum lab Q' := by
  obtain ⟨tag, rank, exponent⟩ := lab
  cases tag
  all_goals dsimp only [LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, fieldInst, finiteInst, hK, scalarB, scalarC, hbc, hq⟩ := h
       exact ⟨K, fieldInst, finiteInst, hK, scalarB, scalarC, hbc, hQQ' _ _ _ hq⟩)
    | (obtain ⟨K, fieldInst, finiteInst, hK, hq⟩ := h
       exact ⟨K, fieldInst, finiteInst, hK, hQQ' _ _ _ hq⟩)

theorem standardTypeRecognitionMarking_mono {X : Type*} [Group X]
    {P P' : LargeEvenMarkProp X}
    (hPP' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), P lab R I F θ → P' lab R I F θ)
    (h : LargeEvenMarking X P) : LargeEvenMarking X P' := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, standardTypeRecognitionRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, θ, hPP' lab R I F θ hθ⟩

@[expose] def InLieTypeCharTwoCatalog : GroupProp := fun G _ =>
  ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧
    Nonempty (G ≃* (TauCeti.CFSGIndex.lie d).Group)

theorem inCatalog_of_inLieTypeCharTwoCatalog (G : Type) [Group G]
    (h : InLieTypeCharTwoCatalog G) : InCatalog G := by
  rcases h with ⟨d, _, he⟩
  exact ⟨TauCeti.CFSGIndex.lie d, he⟩

end CFSG.Assembly
