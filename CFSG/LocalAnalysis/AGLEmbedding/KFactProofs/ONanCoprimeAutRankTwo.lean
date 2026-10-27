module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Constrained
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoprimeAutRankTwoCore

public section

namespace CFSG.AGLEmbedding

theorem stmtCoprimeAutRankTwo : StmtCoprimeAutRankTwo := by
  intro p hp hp2 Y N _ _ _ _ hNp hrk ρ hρ m hm hdvd
  have hN : IsPGroup p N := hNp.of_surjective (⊤ : Subgroup N).subtype
    fun n => ⟨⟨n, Subgroup.mem_top n⟩, rfl⟩
  exact KFactProofs.CoprimeAutRankTwo.false_of_dvd_card hp hp2 hN hrk ρ hρ hm hdvd

end CFSG.AGLEmbedding
