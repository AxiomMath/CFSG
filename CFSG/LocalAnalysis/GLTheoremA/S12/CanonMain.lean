module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTri
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

namespace S12

theorem canonNbrAt_of_facts (F6 : E6FourFacts) (F3 : TriFacts) {G : Type} [Group G] [Finite G] {m p : ℕ}
    (hc : S12Ctx G m p) (h171 : I171OneAt G) : CanonNbrAt G p where
  e6four := by
    intro B x L D K y J hS hsplit hstd hshat hnb hKJ hBN hrank _ lab hlab ⟨htag, hn, hZ, hp5⟩
    subst hp5
    exact canon_e6four_of_facts F6 B x L D K y J hS hsplit hstd hshat hnb hKJ hBN hrank lab hlab htag hn hZ
  tri := by
    intro B x L D K y J hS hsplit hstd hshat hnb hKJ hBN hrank hp3 lab hlab htag hodd h3
    subst hp3
    exact canon_tri_of_facts F3 hc h171 B x L D K y J hS hsplit hstd hshat hnb hKJ hBN hrank lab hlab htag
      hodd h3

end S12

end CFSG.LocalAnalysis.GLTheoremA
