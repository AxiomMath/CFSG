module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Scalar
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3ScalarAdapt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

theorem kFactI2026_holds : KFactI2026 := by
  intro q E _ _ hq hq2 hcomm hexp hcard X P S hPX hPcard hSX hSO hSP hQ8
  haveI : Finite (MulAut E) :=
    Finite.of_injective (fun g : MulAut E => (g : E → E)) DFunLike.coe_injective
  have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [hcard]; exact Nat.one_lt_pow (by norm_num) hq.one_lt)
  have hZc : ∀ k ∈ scalarSubgroup q E hq hexp hnt, ∀ g : MulAut E, g * k = k * g :=
    scalarSubgroup_central
  have hZ2 := scalarSubgroup_two (q := q) (E := E) (hq := hq) (hexp := hexp) (hnt := hnt)
  have hF1 : ∀ g : MulAut E, (∀ s ∈ S, g * s = s * g) → g ∈ scalarSubgroup q E hq hexp hnt := by
    intro g hg
    obtain ⟨z, i, j, r, t, hF, hG⟩ := q8d8_exists hQ8
    exact scalar_of_commute_Q8D8 hq hq2 hcomm hexp hcard hF hG hg
  obtain ⟨h1, h2⟩ := partA hZc hZ2 hPX hPcard hSX hSO hSP hQ8 hF1
  exact ⟨fun g hg => h1 hg, h2⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
