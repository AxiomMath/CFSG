module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneUnitary
import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.AGLEmbedding CFSG.BenderSuzuki.MatrixGroups

theorem signalizerAutAt_unitary {p : ℕ} (hp : p.Prime) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) : SignalizerAutAt p (.lie d) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hf, hq, F, _, _, J, hJ, hF, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu
      (UnitaryModel.statedClassicalModel (L := CatGroup d) hd ⟨MulEquiv.refl _⟩)
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hF hfix hf
  have D := UnitaryModel.smallRankOneData_psu J hJ hF hfix hq S hS hd ⟨e.symm⟩
  have hout : ¬ GL83OuterType24 p (.lie d) := by
    obtain ⟨q, -, hq'⟩ := hd
    rintro ⟨d', hdd, h | h⟩
    · obtain rfl := TauCeti.CFSGIndex.lie.inj hdd
      obtain ⟨q₁, h₁, -⟩ := h.2
      rw [h₁] at hq'
      cases hq'
    · obtain rfl := TauCeti.CFSGIndex.lie.inj hdd
      rw [h.2] at hq'
      cases hq'
  have hR : Nat.card (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
      p ^ (Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)).factorization p :=
    Sylow.card_eq_multiplicity S
  have hTI : WeakTI (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    intro g x hx hx1 hxg
    have hg := D.ti x hx hx1 g⁻¹ (by rwa [inv_inv])
    simpa using hg
  exact signalizerAutAt_of_model_weakTI hp hout e.symm D.center hR hTI

end CFSG.LocalAnalysis.RankFourTheoremC
