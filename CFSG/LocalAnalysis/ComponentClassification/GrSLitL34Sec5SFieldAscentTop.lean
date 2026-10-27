module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldAscent
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldMirror
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdSolMax
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm12KStar

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem centralizer_le_normalizer_of_solomonMaximal_field (h13 : Sol76T13.SolomonThm13Simple)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog G) {c : G} (hc : orderOf c = 2) {J : Subgroup G}
    (hJ : FooteLit.IsTwoComponentIn J (centralizer ({c} : Set G)))
    (hJsol : FooteLit.IsSolomonMaximal J) {k : ℕ} (hk : 4 ≤ k)
    (hJL : Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 k) :
    centralizer ({c} : Set G) ≤ normalizer (J : Set G) := by
  have hJs : J ∈ FooteLit.solomonKStar G := ⟨hJsol, hJsol.1, fun K hK => by
    obtain ⟨e⟩ := Sol76.nonempty_fusionZStar_equiv_of_reflTransGen hK.2
    have := three_le_pRank_of_lieModel_fusionZStar (by omega)
      (LieType.CurtisTits.lieModel_of_mulEquiv e hJL)
    omega⟩
  intro h hh
  have hC : (centralizer ({c} : Set G)).map (MulAut.conj h⁻¹).toMonoidHom =
      centralizer ({c} : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer (inv_mem hh))
  have hJh := Sol76.isTwoComponentIn_map (MulAut.conj h⁻¹) hJ
  rw [hC] at hJh
  have heq := Sol76.eq_of_mem_kStarComponents_of_simple h13 hna hKP
    (mem_centralizer_singleton_iff.mpr rfl) (fun _ hn => mem_centralizer_singleton_iff.mp hn) hc
    ⟨hJ, hJs⟩ (three_le_pRank_of_lieModel_fusionZStar (by omega) hJL)
    ⟨hJh, Sol76.conjugate_mem_solomonKStar hJs h⟩
  have h' := inv_mem (mem_normalizer_iff_map_conj_eq.mpr heq)
  rwa [inv_inv] at h'

theorem l34FieldSignalizerVanishing_of_mirror_ascent
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h13 : Sol76T13.SolomonThm13Simple)
    (hcat : L3TwoPowProperFixedCatalog)
    (hmult : Quasithin.SchurMult2L3)
    (hterminal : L34FieldSignalizerVanishingMirror) :
    L34FieldSignalizerVanishing := by
  intro G _ _ t P hset E hEt hE hE8
  obtain ⟨hG, ht, hPt, hPp, -, m, hm, hev, hPL⟩ := id hset
  obtain ⟨hsimple, hna, hKP, -, -, -, -, -⟩ := id hG
  have := hsimple
  obtain ⟨hsF, hnF, -⟩ := GrS5.fstar_facts hG
  obtain ⟨J, hPJ, hJmm, -, hJsol, k, hk, hkev, hJL⟩ :=
    exists_field_mirror_solomon_top hS hna hsF hnF hKP hcat ht ⟨hPt, hPp⟩ hm hev hPL
  obtain ⟨c, hc, hJc⟩ := Foote5.SolMax.isTwoComponentAt_of_gsMirrorReach ⟨t, ht, ⟨hPt, hPp⟩⟩ hPJ
  have hsetJ : L34FieldNormalSetting G c J := ⟨hG, hc, hJc.1, hJc.2,
    (normal_subgroupOf_iff_le_normalizer hJc.1).mpr
      (centralizer_le_normalizer_of_solomonMaximal_field h13 hna hKP hc hJc hJsol hk hJL),
    k, hk, hkev, hJL⟩
  have hP0 := (field_internal_vanishing_iff_of_gsMirrorReach hS hcat hmult hG ht ⟨hPt, hPp⟩ hm
    hev hPL hPJ).mpr fun B hBJ hB hB8 => hterminal G c J hsetJ hJmm B (hBJ.trans hJc.1) hB hB8
  obtain ⟨W, -, -, hWE⟩ := l34FieldSignalizerGluing_of_inputs hmult G t P hset
  obtain ⟨A, hAP, hA, hA8⟩ := exists_isElemTwo_of_three_le_pRank
    (three_le_pRank_of_lieModel_fusionZStar (by omega) hPL)
  rw [hWE E hEt hE hE8, ← hWE A (hAP.trans hPt) hA.isElemAbelian hA8]
  exact hP0 A hAP hA.isElemAbelian hA8

end CFSG.ComponentClassification.GrSLit.L34Sec5S
