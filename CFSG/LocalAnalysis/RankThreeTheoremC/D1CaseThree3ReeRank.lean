module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Lie
public import CFSG.Adapters.TauCetiExceptional.ReeBridge
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbedding (IsReeGTwoIndex kFactReeSchur)

theorem kFactReeSylowElemAbelian : KFactReeSylowElemAbelian := by
  intro L _ _ d hd ⟨e⟩ U
  obtain ⟨-, m, hm, hdm, hfe⟩ := hd.exists_eq
  obtain ⟨d₀, hv⟩ := d
  simp only at hdm hfe
  subst hdm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv (GaloisField 3 (2 * m + 1)) hK
  have hmodel : CFSG.Blueprint.ReeTitsModel L .twistedG2 3 (2 * m + 1) :=
    ⟨⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩, m, rfl,
      GaloisField 3 (2 * m + 1), inferInstance, inferInstance, hK, ⟨e.trans φ.symm⟩⟩
  obtain ⟨-, -, hrank⟩ := CFSG.SectionRank.smallReeModel_rank hmodel
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hrank
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L Q U
  have hU : (U : Subgroup L) = (Q : Subgroup L).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  refine ⟨E.map (MulAut.conj g).toMonoidHom, hU ▸ Subgroup.map_mono hQ,
    elementary_abelian_map 3 hE _, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard, hfe]

theorem d1CaseThreeReeFacts3 : D1CaseThreeReeFacts3 :=
  ⟨kFactReeSchur, kFactReeSylowElemAbelian⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
