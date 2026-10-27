module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.LocalAnalysis.GLTheoremB.BarXTools

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem IsPComponentIn.nonempty_quotEquiv_starImg (hp : p.Prime) {H K : Subgroup G}
    (hK : IsPComponentIn p K H) :
    Nonempty (↥K ⧸ CFSG.pPrimeCore p ↥K ≃* ↥(starImg p H K)) := by
  rcases hK.2 with ⟨K', hKcomp, hsn, hKmap, hKmin⟩
  have hsn' : CFSG.Open.IsSubnormal K H := (CFSG.Open.IsSubnormal.iff_subgroupOf hK.1).2 hsn
  have hbar : CFSG.LocalAnalysis.GLTheoremB.barX p H K = starImg p H K := rfl
  exact ⟨(CFSG.LocalAnalysis.GLTheoremB.quotEquivBarX hp hK.1 hsn').trans
    (MulEquiv.subgroupCongr hbar)⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
