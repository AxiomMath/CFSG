module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdMax
public import CFSG.LocalAnalysis.ComponentClassification.Foote5WMPHeld

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Foote5.SolMax
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem lieModel_of_gsMirrorReach [IsSimpleGroup G]
    (hS : SchreierFor Blueprint.Catalog) (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog G) (hC5 : L3TwoPowProperFixedCatalog)
    {M : Subgroup G} {n : ℕ} (hn : 4 ≤ n) (hev : Even n)
    (hL : Blueprint.LieModel (M ⧸ Open.fusionZStar M) .PSL 3 2 n)
    {M' : Subgroup G} (hM : GSMirrorReach M M') :
    ∃ m : ℕ, 4 ≤ m ∧ Even m ∧ Blueprint.LieModel (M' ⧸ Open.fusionZStar M') .PSL 3 2 m := by
  classical
  induction hM with
  | refl => exact ⟨n, hn, hev, hL⟩
  | @tail Y X _ hst ih =>
    obtain ⟨m, hm, hmev, hLm⟩ := ih
    rcases hst with ⟨c, d, hW⟩ | hMir | ⟨g, rfl⟩
    ·
      have hdZ : d ∉ center G := GSLit.not_mem_center_of_orderOf_eq_two hnonab hW.2.1
      rcases gsWeakCorr_type_dichotomy hS hK hW hdZ with he | ⟨hMa, hTM, hTp, hlt, ⟨eT⟩⟩
      · obtain ⟨e⟩ := he
        exact ⟨m, hm, hmev, LieType.CurtisTits.lieModel_of_mulEquiv e hLm⟩
      · have hbtop : centralizer ({d} : Set G) ≠ ⊤ :=
          centralizer_ne_top_of_not_mem_center hdZ
        exact ⟨2 * m, by omega, even_two_mul m,
          lieModel_two_mul_of_fixed hC5 hK hW.1 hW.2.1 hW.2.2.1 hbtop
            hW.2.2.2.2.2.1 hW.2.2.2.2.2.2.1 hMa hTM hTp hlt hm hmev
            (LieType.CurtisTits.lieModel_of_mulEquiv eT hLm)⟩
    ·
      obtain ⟨z, s, D, hz, hs, hzs, hYz, hYs, hX, hD, hDY, hDX⟩ := hMir
      by_cases hfree : conjugate X z ≠ X ∨ z ∈ coreActionKernel X
      · obtain ⟨e⟩ := mirror_fusionZStar_equiv_of_free hz hs hzs hYz hYs hX hD hDY hDX hfree
        exact ⟨m, hm, hmev, LieType.CurtisTits.lieModel_of_mulEquiv e hLm⟩
      · obtain ⟨hXz, hzX⟩ := not_or.mp hfree
        have hXz' : conjugate X z = X := not_not.mp hXz
        obtain ⟨hTD, hTDp, hlt⟩ := properFixed_of_badShape hz hzs hX hD hDX hXz' hzX
        obtain ⟨eDY⟩ := diagonal_fusionZStar_equiv hs hzs hYz hYs hD hDY
        have hsZ : s ∉ center G := GSLit.not_mem_center_of_orderOf_eq_two hnonab hs
        have hbtop : centralizer ({s} : Set G) ≠ ⊤ :=
          centralizer_ne_top_of_not_mem_center hsZ
        exact ⟨2 * m, by omega, even_two_mul m,
          lieModel_two_mul_of_fixed hC5 hK hz hs hzs hbtop hX.1 hX.2 hXz' hTD hTDp hlt hm hmev
            (LieType.CurtisTits.lieModel_of_mulEquiv eDY.symm hLm)⟩
    ·
      obtain ⟨e⟩ := GrSLit.nonempty_fusionZStar_equiv_conjugate Y g
      exact ⟨m, hm, hmev, LieType.CurtisTits.lieModel_of_mulEquiv e hLm⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
