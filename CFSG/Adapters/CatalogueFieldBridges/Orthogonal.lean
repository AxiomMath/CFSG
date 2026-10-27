module

public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.Adapters.CatalogueFieldBridges

open TauCeti CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.RankThree.PartOne
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.Adapters.RankTwoModelTransports
open CFSG.ClassicalModels
open CFSG.ClassicalInvolution.Upgrade
open CFSG.RankThree.PartTwo.Census.Carrier


theorem exists_mulEquiv_catalogue_pomegaOdd {n ℓ s : ℕ} {k : Type} [Field k] [Finite k]
    (hℓ : ℓ.Prime) (hpos : 0 < s)
    (hv₀ : (TauCeti.LieTypeIndex.B n ⟨ℓ, s, hℓ, hpos⟩).Valid) (hn3 : 3 ≤ n) (hℓ2 : ℓ ≠ 2)
    (hSCk : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadOdd n k))
      .POmegaOdd n ℓ s) :
    Nonempty (matrixProjectiveDerived (coordinateQuadOdd n k) ≃*
      (TauCeti.CFSGIndex.lie ⟨.B n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩).Group) := by
  obtain ⟨-, K₁, hfield, hfinite, hK₁, ⟨θ⟩⟩ := hSCk
  letI := hfield
  letI := hfinite
  let Fd := ↥(ValidLieTypeIndex.fixedField ⟨.B n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩)
  have hFd : Finite Fd := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  letI := hFd
  have hK₁' : Nat.card K₁ = ValidLieTypeIndex.fieldOrder ⟨.B n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩ := by
    have hc : ValidLieTypeIndex.characteristic ⟨.B n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩ =
        (⟨ℓ, s, hℓ, hpos⟩ : TauCeti.PrimePower).p :=
      LieTypeIndex.characteristic_B n ⟨ℓ, s, hℓ, hpos⟩
    have he : ValidLieTypeIndex.fieldExponent ⟨.B n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩ =
        (⟨ℓ, s, hℓ, hpos⟩ : TauCeti.PrimePower).exponent :=
      LieTypeIndex.fieldExponent_B n ⟨ℓ, s, hℓ, hpos⟩
    rw [ValidLieTypeIndex.fieldOrder_eq_characteristic_pow ⟨.B n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩,
      hc, he, ← PrimePower.card_def, hK₁, PrimePower.card_def]
  obtain ⟨φ⟩ := nonempty_ringEquiv_validIndex_fixedField ⟨.B n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩ K₁ hK₁'
  have hH : (StatedOmega (StatedQuadOdd n K₁)).map (glCongr φ).toMonoidHom =
      StatedOmega (StatedQuadOdd n Fd) := map_statedOmega φ (statedQuadOdd_comp φ)
  let e1 := statedProjCongr (glCongr φ) hH (glCongr_statedScalars φ)
  exact ⟨θ.trans (e1.trans
    (SpinB.typeBGroupEquivStatedProj_odd n ⟨ℓ, s, hℓ, hpos⟩ hv₀ hℓ2 hn3).symm)⟩

theorem exists_mulEquiv_catalogue_pomegaPlus {n ℓ s : ℕ} {k : Type} [Field k] [Finite k]
    (hℓ : ℓ.Prime) (hpos : 0 < s)
    (hv₀ : (TauCeti.LieTypeIndex.D n ⟨ℓ, s, hℓ, hpos⟩).Valid) (hn4 : 4 ≤ n)
    (hSCk : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n k))
      .POmegaPlus n ℓ s) :
    Nonempty (matrixProjectiveDerived (coordinateQuadPlus n k) ≃*
      (TauCeti.CFSGIndex.lie ⟨.D n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩).Group) := by
  obtain ⟨-, K₁, hfield, hfinite, hK₁, ⟨θ⟩⟩ := hSCk
  letI := hfield
  letI := hfinite
  let Fd := ↥(ValidLieTypeIndex.fixedField ⟨.D n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩)
  have hFd : Finite Fd := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  letI := hFd
  have hK₁' : Nat.card K₁ = ValidLieTypeIndex.fieldOrder ⟨.D n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩ := by
    have hc : ValidLieTypeIndex.characteristic ⟨.D n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩ =
        (⟨ℓ, s, hℓ, hpos⟩ : TauCeti.PrimePower).p :=
      LieTypeIndex.characteristic_D n ⟨ℓ, s, hℓ, hpos⟩
    have he : ValidLieTypeIndex.fieldExponent ⟨.D n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩ =
        (⟨ℓ, s, hℓ, hpos⟩ : TauCeti.PrimePower).exponent :=
      LieTypeIndex.fieldExponent_D n ⟨ℓ, s, hℓ, hpos⟩
    rw [ValidLieTypeIndex.fieldOrder_eq_characteristic_pow ⟨.D n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩,
      hc, he, ← PrimePower.card_def, hK₁, PrimePower.card_def]
  obtain ⟨φ⟩ := nonempty_ringEquiv_validIndex_fixedField ⟨.D n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩ K₁ hK₁'
  have hH : (StatedOmega (StatedQuadPlus n K₁)).map (glCongr φ).toMonoidHom =
      StatedOmega (StatedQuadPlus n Fd) := map_statedOmega φ (statedQuadPlus_comp φ)
  let e1 := statedProjCongr (glCongr φ) hH (glCongr_statedScalars φ)
  exact ⟨θ.trans (e1.trans
    (SpinD.typeDGroupEquivStatedProj_of_valid n ⟨ℓ, s, hℓ, hpos⟩ hv₀).symm)⟩

theorem exists_mulEquiv_catalogue_pomegaMinus {n ℓ s : ℕ} {k : Type} [Field k] [Finite k]
    (hn : 1 ≤ n) {b c : k} (hirr : ∀ t : k, t ^ 2 + b * t + c ≠ 0)
    (hℓ : ℓ.Prime) (hpos : 0 < s)
    (hv₀ : (TauCeti.LieTypeIndex.twistedD n ⟨ℓ, s, hℓ, hpos⟩).Valid) (hn4 : 4 ≤ n)
    (hSCk : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadMinus n k hn b c))
      .POmegaMinus n ℓ s) :
    Nonempty (matrixProjectiveDerived (coordinateQuadMinus n k hn b c) ≃*
      (TauCeti.CFSGIndex.lie ⟨.twistedD n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩).Group) := by
  obtain ⟨-, K₁, hfield, hfinite, hK₁, b₁, c₁, hirr₁, ⟨θ⟩⟩ := hSCk
  letI := hfield
  letI := hfinite
  let Fd := ↥(ValidLieTypeIndex.fixedField ⟨.twistedD n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩)
  have hFd : Finite Fd := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  letI := hFd
  have hK₁' : Nat.card K₁ = ValidLieTypeIndex.fieldOrder ⟨.twistedD n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩ := by
    have hc : ValidLieTypeIndex.characteristic ⟨.twistedD n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩ =
        (⟨ℓ, s, hℓ, hpos⟩ : TauCeti.PrimePower).p :=
      LieTypeIndex.characteristic_twistedD n ⟨ℓ, s, hℓ, hpos⟩
    have he : ValidLieTypeIndex.fieldExponent ⟨.twistedD n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩ =
        (⟨ℓ, s, hℓ, hpos⟩ : TauCeti.PrimePower).exponent :=
      LieTypeIndex.fieldExponent_twistedD n ⟨ℓ, s, hℓ, hpos⟩
    rw [ValidLieTypeIndex.fieldOrder_eq_characteristic_pow
      ⟨.twistedD n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩, hc, he, ← PrimePower.card_def, hK₁,
      PrimePower.card_def]
  obtain ⟨φ⟩ := nonempty_ringEquiv_validIndex_fixedField
    ⟨.twistedD n ⟨ℓ, s, hℓ, hpos⟩, hv₀⟩ K₁ hK₁'
  obtain ⟨b₀, c₀, hirr₀, ⟨eT⟩⟩ :=
    SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid n ⟨ℓ, s, hℓ, hpos⟩ hv₀
  have hH : (StatedOmega (StatedQuadMinus n K₁ b₁ c₁)).map (glCongr φ).toMonoidHom =
      StatedOmega (StatedQuadMinus n Fd (φ b₁) (φ c₁)) :=
    map_statedOmega φ (statedQuadMinus_comp (b := b₁) (c := c₁) φ rfl rfl)
  let e1 := statedProjCongr (glCongr φ) hH (glCongr_statedScalars φ)
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := n)
    (by omega) (irreducible_map φ hirr₁) hirr₀
  exact ⟨θ.trans (e1.trans (e2.trans eT.symm))⟩

end CFSG.Adapters.CatalogueFieldBridges

end
