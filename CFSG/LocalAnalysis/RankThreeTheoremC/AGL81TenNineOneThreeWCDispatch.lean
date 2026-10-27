module

import CFSG.Adapters.CatalogueFieldBridges.Symplectic
import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint
import CFSG.LocalAnalysis.EvenBN.Tits.R2.CatalogSp6
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.CoverNotCaseTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalViso
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeCore
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 TenNineOneThree

@[expose] def IsSpFourEight (Y : Type*) [Group Y] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .B 2 q) ∧
    Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

section Bridges

variable {K : Type} [Group K]

theorem nonempty_V0_of_isSpFourIndex
    (d : TauCeti.ValidLieTypeIndex) (hd : CFSG.AGLEmbedding.IsSpFourIndex 3 d)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Nonempty (K ≃* CFSG.AGLEmbedding.KFactProofs.Sp62Local.V0) := by
  obtain ⟨eV⟩ := CFSG.AGLEmbedding.KFactProofs.Sp62Local.nonempty_V0_mulEquiv_catGroup
  obtain ⟨d1, hv⟩ := d
  obtain ⟨q, ⟨hqp, hqe, hd1⟩ | ⟨-, hqp, hqe, hd1⟩⟩ := hd
  · subst hd1
    have hk : Nat.card (ZMod 3) = q.card := by
      rw [TauCeti.PrimePower.card_def, hqp, hqe, Nat.card_zmod, pow_one]
    obtain ⟨e₁⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj
      hv hk
    obtain ⟨e₂⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_u42
      (k := ZMod 3) (Nat.card_zmod 3)
    exact ⟨e.trans (e₁.symm.trans (e₂.trans eV.symm))⟩
  · subst hd1
    obtain ⟨p, n, hp, hn⟩ := q
    simp only at hqp hqe
    subst hqp hqe
    exact ⟨e.trans eV.symm⟩

theorem nonempty_H6_of_B3 (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Nonempty (K ≃* CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.H6) := by
  obtain ⟨d1, hv⟩ := d
  obtain ⟨q, hqp, hqe, hd1⟩ := hd
  subst hd1
  rcases CFSG.Models.lieModel_B 3 q hv e with hL | hL
  · rw [hqp, hqe] at hL
    exact CFSG.LocalAnalysis.EvenBN.Tits.R2.nonempty_mulEquiv_H6_of_lieModel
      (CFSG.Models.LieModel.toBlueprint (by decide) hL)
  · rw [hqp] at hL
    exact absurd hL.1.2.2.2 (by simp)

end Bridges

end CFSG.LocalAnalysis.RankThreeTheoremC
