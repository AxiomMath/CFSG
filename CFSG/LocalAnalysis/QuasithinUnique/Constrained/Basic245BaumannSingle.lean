module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannA3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannLin2

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup

namespace C56

variable {G : Type} [Group G] [Finite G]

theorem baumann_single {R H L : Subgroup G} (hmin : IsMinimalParabolic R H)
    (hblk : IsChi0Block H L) (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3)
    (hth : ⁅L, thompsonJ R⁆ = L) (hHLR : H = L ⊔ R) (hRN : R ≤ normalizer (L : Set G)) :
    baum R ≤ normalizer (L : Set G) ∧ IsSylowTwoOf (baum R) (L ⊔ baum R) := by
  rcases hL with ⟨n, hn, hlin⟩ | ha
  · have hBR : baum R ≤ R := inf_le_left
    exact ⟨hBR.trans hRN, (baumann_Lin2_single hmin hblk hn hlin hth hHLR hRN).1⟩
  · obtain ⟨-, h1, h2⟩ := baumann_A3_single hmin hblk ha hth hHLR hRN
    exact ⟨h1, h2⟩

theorem baumann_c542 {R H L : Subgroup G} (hmin : IsMinimalParabolic R H)
    (hblk : IsChi0Block H L) {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type L n)
    (hth : ⁅L, thompsonJ R⁆ = L) (hHLR : H = L ⊔ R) (hRN : R ≤ normalizer (L : Set G)) :
    baum R ≤ (baum R ⊓ L) ⊔ pCoreOf 2 (L ⊔ baum R) :=
  (baumann_Lin2_single hmin hblk hn hlin hth hHLR hRN).2

end C56

end CFSG.QuasithinUnique
