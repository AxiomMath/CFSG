module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G4LB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint


theorem l43_quotient {W : Type} [Group W] [Finite W] {Φ : Set (Subgroup W)} {K K' : Subgroup W}
    {k k' : W} {σ : MulAut W} (hT : TwinSProp3 Φ K K' k k' σ) (N : Subgroup W) [N.Normal]
    (hN : N = Subgroup.zpowers (k * k'))
    (hS : LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) .PSL 4 3 1) :
    ∃ (B : Subgroup ↥(fixSylGen Φ σ)) (_ : B.Normal),
      LieModel (↥(fixSylGen Φ σ) ⧸ B) .PSL 3 3 1 := by
  obtain ⟨hf, hf2, hs, hOS⟩ := E3S3O.quotCenter_reduction hT.toTwinBase3 N hN (Or.inl rfl) hS
  have hSP := sPHyp_of_reduction hT _ hf hf2 hs hOS
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_fixSub_equiv_sl3 hS hSP
  have hC : IsSimpleGroup ↥(fixSub (E3S3O.descend _ hf σ
      (E3S3O.map_ker_aut hT.toTwinBase3 _ hf hf2 hs σ))) := by
    have := isSimpleGroup_sl3 hF
    exact e.isSimpleGroup
  obtain ⟨B, hB, ⟨e'⟩⟩ := exists_quotient_of_simple_fix hT _ hf hf2 hs hOS hC
  exact ⟨B, hB, lieModel_L33_of_equiv_sl3 hF (e'.trans e)⟩

end CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4
