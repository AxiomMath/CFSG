module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseXfer
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem sp62Close_coprime_pCore_two (M : Subgroup G) :
    Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

theorem normalizer_le_of_isElemAbelian_three_cube {P M J : Subgroup G}
    (hM : GLBWeakCore 3 P ≤ M) (hJP : J ≤ P) (hJ : IsElemAbelian 3 J)
    (hJcard : Nat.card J = 3 ^ 3) :
    Subgroup.normalizer (J : Set G) ≤ M := by
  have hrk : 3 ≤ Open.pRank 3 J :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 Nat.prime_three J)
      ⟨J, le_rfl, hJ, hJcard⟩
  have hrk3 : 3 ≤ Open.pRank 3 (J ⊔ P ⊓ Subgroup.centralizer (J : Set G)) :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 Nat.prime_three _)
      ⟨J, le_sup_left, hJ, hJcard⟩
  exact (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore 3 hJP (by omega) hrk3).trans hM

theorem sp62Close_barJ [Fact (Nat.Prime 3)] {P : Sylow 3 G} {M H R L : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {d : TauCeti.ValidLieTypeIndex}
    (c : Sp62CloseCtx P M H R L Rbar K d) {J : Subgroup G} (hJP : J ≤ (P : Subgroup G))
    (hJ : IsElemAbelian 3 J) (hJcard : Nat.card J = 3 ^ 3) :
    barM M J ≤ barM M L ∧ IsElemAbelian 3 (barM M J) ∧ Nat.card (barM M J) = 3 ^ 3 := by
  have hJM : J ≤ M := hJP.trans c.cfg.ext.sylow_le
  have hJR : J ≤ R := c.rp ▸ hJP
  have hJ3 : IsPGroup 3 J := c.cfg.ext.isPGroup.to_le hJR
  refine ⟨?_, ?_, ?_⟩
  · exact (Subgroup.map_mono (Subgroup.comap_mono hJR)).trans c.shape.1.2.2.2.1
  · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
      (isElemAbelian_subgroupOf hJ M) _
  · have h1 : Nat.card (barM M J) = Nat.card (J.subgroupOf M) :=
      card_map_mk_of_isPGroup Nat.prime_three _ (sp62Close_coprime_pCore_two M)
        hJ3.comap_subtype
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJM).toEquiv]
    exact hJcard

theorem sp62Close_normBound [Fact (Nat.Prime 3)] (hK2 : KFactOmega8Frame) {P : Sylow 3 G}
    {M H R L : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {d : TauCeti.ValidLieTypeIndex}
    (c : Sp62CloseCtx P M H R L Rbar K d) {J : Subgroup G} (hJP : J ≤ (P : Subgroup G))
    (hJ : IsElemAbelian 3 J) (hJcard : Nat.card J = 3 ^ 3) :
    (Subgroup.centralizer (J : Set G)).relIndex (Subgroup.normalizer (J : Set G)) ∣ 48 := by
  have hJM : J ≤ M := hJP.trans c.cfg.ext.sylow_le
  have hJR : J ≤ R := c.rp ▸ hJP
  have hJ3 : IsPGroup 3 J := c.cfg.ext.isPGroup.to_le hJR
  have hN : Subgroup.normalizer (J : Set G) ≤ M :=
    normalizer_le_of_isElemAbelian_three_cube c.cfg.loc.core hJP hJ hJcard
  obtain ⟨hle, hel, hcard⟩ := sp62Close_barJ c hJP hJ hJcard
  obtain ⟨d', hd', e⟩ := c.shape.2
  have h4 := relIndex_centralizer_eq_of_quotient Nat.prime_three (CFSG.pCore 2 ↥M)
    (sp62Close_coprime_pCore_two M) hJM hJ3
  rw [inf_eq_left.mpr hN] at h4
  rw [h4]
  exact (hK2 _ (barM M L) d' hd' c.shape.1.2.2.1 e (barM M J) hle hel hcard).1

theorem sp62Close_section [Fact (Nat.Prime 3)] (hK2 : KFactOmega8Frame) {P : Sylow 3 G}
    {M H R L : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {d : TauCeti.ValidLieTypeIndex}
    (c : Sp62CloseCtx P M H R L Rbar K d) {J : Subgroup G} {b : G}
    (hF : ElemFrame3 (P : Subgroup G) J (Subgroup.zpowers b))
    (hidx : (Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer (J : Set G)) = 3) :
    ∃ (W : Subgroup G) (Wb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (φ : ↥W →* ↥Wb),
      W ≤ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) ⊓ M ∧
        Function.Surjective φ ∧ IsSimpleGroup ↥Wb ∧ (∃ x y : Wb, x * y ≠ y * x) ∧
        3 ∣ Nat.card Wb := by
  have hJP : J ≤ (P : Subgroup G) := hF.le_P
  have hJM : J ≤ M := hJP.trans c.cfg.ext.sylow_le
  have hJR : J ≤ R := c.rp ▸ hJP
  have hJ3 : IsPGroup 3 J := c.cfg.ext.isPGroup.to_le hJR
  have hN : Subgroup.normalizer (J : Set G) ≤ M :=
    normalizer_le_of_isElemAbelian_three_cube c.cfg.loc.core hJP hF.elem hF.card_J
  have hbJ : b ∈ J := hF.le_J (Subgroup.mem_zpowers b)
  have hbM : b ∈ M := hJM hbJ
  have hbord : orderOf b = 3 := by rw [← Nat.card_zpowers, hF.card_B]
  have hOcop := sp62Close_coprime_pCore_two M
  set ρ := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hρ
  obtain ⟨hle, hel, hcard⟩ := sp62Close_barJ c hJP hF.elem hF.card_J
  obtain ⟨d', hd', e⟩ := c.shape.2
  have hBJ : Subgroup.zpowers b ≤ J := hF.le_J
  have h4 := relIndex_normalizer_eq_of_quotient Nat.prime_three (CFSG.pCore 2 ↥M) hOcop hJM
    hBJ hJ3
  rw [inf_eq_left.mpr hN, hidx, map_mk_subgroupOf_zpowers _ hbM] at h4
  have hBcard : Nat.card (Subgroup.zpowers (ρ ⟨b, hbM⟩)) = 3 := by
    have h1 : Nat.card (((Subgroup.zpowers b).subgroupOf M).map ρ) =
        Nat.card ((Subgroup.zpowers b).subgroupOf M) :=
      card_map_mk_of_isPGroup Nat.prime_three _ hOcop (hJ3.to_le hBJ).comap_subtype
    rw [← map_mk_subgroupOf_zpowers (CFSG.pCore 2 ↥M) hbM, h1,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBJ.trans hJM)).toEquiv, hF.card_B]
  have hbbord : orderOf (ρ ⟨b, hbM⟩) = 3 := by rw [← Nat.card_zpowers, hBcard]
  have hbbJ : ρ ⟨b, hbM⟩ ∈ barM M J := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbJ)
  obtain ⟨Wb, hWbL, hWbs, hWbna, hWb3⟩ :=
    (hK2 _ (barM M L) d' hd' c.shape.1.2.2.1 e (barM M J) hle hel hcard).2 (ρ ⟨b, hbM⟩) hbbJ
      hbbord h4.symm
  have he : IsPGroup 3 (Subgroup.zpowers (⟨b, hbM⟩ : ↥M)) :=
    (P.isPGroup'.comap_subtype (K := M)).to_le
      (Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr (hJP hbJ)))
  set W' : Subgroup ↥M :=
    Subgroup.centralizer ({(⟨b, hbM⟩ : ↥M)} : Set ↥M) ⊓ Wb.comap ρ with hW'
  let φ' : ↥W' →* ↥Wb := (ρ.comp W'.subtype).codRestrict Wb fun w => w.2.2
  have hφ' : Function.Surjective φ' := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hg, hgy⟩ := exists_mem_centralizer_mk_eq Nat.prime_three (CFSG.pCore 2 ↥M) hOcop he
      (Subgroup.mem_inf.mp (hWbL hy)).2
    have hρg : ρ g = y := hgy
    have hgW : g ∈ W' := Subgroup.mem_inf.mpr ⟨hg, Subgroup.mem_comap.mpr (by rw [hρg]; exact hy)⟩
    exact ⟨⟨g, hgW⟩, Subtype.ext hρg⟩
  let ι := Subgroup.equivMapOfInjective W' M.subtype M.subtype_injective
  refine ⟨W'.map M.subtype, Wb, φ'.comp ι.symm.toMonoidHom, ?_, ?_, hWbs, hWbna, hWb3⟩
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun h hh => ?_, w.2⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc' : (w : G) * b = b * (w : G) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hw.1)
    exact (Commute.zpow_left (Commute.symm (show Commute (w : G) b from hc')) k).eq
  · exact hφ'.comp ι.symm.surjective

end CFSG.LocalAnalysis.RankThreeTheoremC
