module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Group
public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuterParts
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.LowTwoRank

noncomputable def projSUCongr' (a b : ℕ) [Fact a.Prime] (ha : a = 2) (hb : b = 3) :
    StatedProj (StatedSU 3 8 (GaloisField 2 6)) ≃*
      StatedProj (StatedSU (2 + 1) (a ^ b) (GaloisField a (2 * b))) := by
  subst ha hb
  exact MulEquiv.refl _

theorem exists_equiv_unitaryPSU (d : TauCeti.ValidLieTypeIndex)
    (hd : CFSG.LocalAnalysis.RankThreeTheoremC.IsChevTwoOuterU38Index d) :
    Nonempty ((TauCeti.CFSGIndex.lie d).Group ≃* unitaryPSU hU 3) := by
  obtain ⟨q, hqp, hqe, hdq⟩ := hd
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.twistedA 2 q := hdq
  have : Fintype GF64 := Fintype.ofFinite GF64
  have : Fintype (GaloisField 2 6) := Fintype.ofFinite _
  have hc : Fintype.card GF64 = Fintype.card (GaloisField 2 6) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, GF64.card_eq,
      GaloisField.card 2 6 (by norm_num)]
    norm_num
  let e : GF64 ≃+* GaloisField 2 6 := FiniteField.ringEquivOfCardEq hc
  have h1 : TauCeti.ValidLieTypeIndex.characteristic
      ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ = 2 := by
    show (TauCeti.LieTypeIndex.twistedA 2 q).characteristic = 2
    simp [hqp]
  have h2 : TauCeti.ValidLieTypeIndex.fieldExponent
      ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ = 3 := by
    show (TauCeti.LieTypeIndex.twistedA 2 q).fieldExponent = 3
    simp [hqe]
  have : Fact (TauCeti.ValidLieTypeIndex.characteristic
      ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Prime :=
    ⟨TauCeti.ValidLieTypeIndex.characteristic_prime _⟩
  let f3 := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv
  let f4 := projSUCongr' (TauCeti.ValidLieTypeIndex.characteristic
      ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩) h1 h2
  let f2 := CFSG.Fischer.Classification.Recognition.statedProjSUEquiv e 3 8
  exact ⟨f3.trans (f4.symm.trans (f2.symm.trans (unitaryPSUEquiv hU (by norm_num)).symm))⟩

end CFSG.AGLEmbedding.ChevOuter.U38
