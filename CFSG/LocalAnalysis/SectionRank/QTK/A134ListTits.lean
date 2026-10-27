module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
import CFSG.LocalAnalysis.SectionRank.QTK.A134ListSporC
import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LieType.Ree.ReeHolds

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree


theorem oddLocalWitness_tits {S : Type} [Group S] [Finite S]
    (hm : ReeTitsModel S .Tits 2 1) : OddLocalWitness S := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hm
  have : Finite (commutator (reeFixed ReeTag.F4 K 0)) := Finite.of_equiv S e.toEquiv
  obtain ⟨x, y, h, hx, hy, hxy, hc, h1, h2⟩ := CFSG.SectionRank.Tits_sylow5_square_witness hK
  exact OddLocalWitness.of_mulEquiv e (oddLocalWitness_of_square_Tits hx hy hxy hc h1 h2)

end CFSG.SectionRank.QTK
