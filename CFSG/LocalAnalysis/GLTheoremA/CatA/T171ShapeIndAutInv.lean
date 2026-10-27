module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

theorem indAut_inv {G : Type} [Group G] {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    CFSG.LocalAnalysis.GLTheoremA.MI.indAut p L g⁻¹ (Subgroup.inv_mem _ hg) =
      (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p L g hg)⁻¹ := by
  simpa using CFSG.LocalAnalysis.GLTheoremA.T156.indAut_zpow (p := p) (L := L) (g := g) hg (-1)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
