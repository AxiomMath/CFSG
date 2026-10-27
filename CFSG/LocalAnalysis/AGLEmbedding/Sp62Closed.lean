module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62MSide
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Lift
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Data

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem exists_sp62Data_of (hKF : KFactSp62Local) {G : Type} [Group G] [Finite G]
    [Fact (Nat.Prime 3)] {P : Sylow 3 G} {M H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hglob : CFSG.AGLEmbeddingD2.AGLGlobal G) (hext : D1Extremal 3 P M H R)
    (hrbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
    (hred : ReducedNongeneration 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))))
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K)
    (hC : Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) = ⊥)
    (hKD : ¬ HasKlingenData 3 Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))))
    {d : TauCeti.ValidLieTypeIndex} (hd : IsSpSixTwoIndex d) (eK : K ≃* CatGroup d) :
    ∃ V : Subgroup G, D1Sp62Data P M H R V := by
  obtain ⟨V₀, hS⟩ := hKF _ K d hd (normal_of_forall_isComponentOf_eq hK huniq) ⟨eK⟩ hC
    Rbar _ hred.three_le_pRank hred.weakCore_le hred.ne_top hKD
  rw [hrbar] at hS
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hRH : R ≤ H := hext.le_H
  have hR3 : IsPGroup 3 R := hext.isPGroup
  have hcardR : Nat.card R = 3 ^ 4 := by
    have hRp : IsPGroup 3 (R.subgroupOf H) := hR3.comap_subtype
    rw [← hS.card_T, card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime 3) hRp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv]
  have hR1 : R ≠ ⊥ := by
    intro h1
    rw [h1, Subgroup.card_bot] at hcardR
    norm_num at hcardR
  have hsurv : D1SurvivorData 3 P M H R R := by
    refine hext.survivorData_of_map hglob le_rfl hR1 (fun W hW hWn hWc => ?_)
      (fun W hW hWn => (hS.dichotomy W hW hWn).imp_right fun h1 => hS.T_le.trans h1)
      hS.centralizer_le
    rcases hS.dichotomy W hW ((Subgroup.normal_subgroupOf_iff_le_normalizer hW).mp hWn) with
      h1 | h1
    · exact h1
    · exfalso
      have hdvd := Subgroup.card_dvd_of_le (hS.T_le.trans h1)
      rw [hS.card_T] at hdvd
      have h3 : 3 ∣ Nat.card W := (dvd_pow_self 3 (by norm_num)).trans hdvd
      exact absurd (Nat.Coprime.eq_one_of_dvd hWc h3) (by norm_num)
  have hKmem : H ⊓ M ∈ liftSet H (H ⊓ M) V₀ := ⟨le_rfl, Subgroup.le_normalizer, hS.V_le⟩
  obtain ⟨V, hV, hmin⟩ := exists_minimal_liftSet hKmem
  have hVV := perfect_of_minimal_liftSet hS.V_perfect hV hmin
  have hVmap := map_eq_of_minimal_liftSet inf_le_left hV hmin hS.V_normal
  refine ⟨V, ⟨hsurv, hcardR, u42Piece_of_map_eq hS hV.1 hVV hVmap, fun Y hYK hYn => ?_⟩⟩
  have hYH : Y ≤ H := hYK.trans inf_le_left
  set Wb := (Y.subgroupOf H).map π with hWb
  have hWbY : Wb ≤ ((H ⊓ M).subgroupOf H).map π := Subgroup.map_mono (Subgroup.comap_mono hYK)
  have hWbn : ((H ⊓ M).subgroupOf H).map π ≤
      Subgroup.normalizer (Wb : Set (H ⧸ primeComplementCore (G := H) 3)) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨k * y * k⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.mp (hYn (Subgroup.mem_subgroupOf.mp hk)) y).mp
        (Subgroup.mem_subgroupOf.mp hy)
    · rintro ⟨y, hy, hyx⟩
      refine ⟨k⁻¹ * y * k, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hYn (Subgroup.mem_subgroupOf.mp
          (((H ⊓ M).subgroupOf H).inv_mem hk))) y).mp (Subgroup.mem_subgroupOf.mp hy)
        simpa using this
      · rw [map_mul, map_mul, map_inv, hyx]
        group
  rcases hS.dichotomy Wb hWbY hWbn with h1 | h1
  · exact Or.inl (le_glbPrimeCore_of_map_eq_bot hYH h1)
  · exact Or.inr (le_of_minimal_liftSet hS.V_perfect hV hmin ⟨hYK, hYn, h1⟩)

theorem stmtSp62Data_of (hSoc : StmtChevTwoSocle) (hKF : KFactSp62Local) : StmtSp62Data := by
  intro G _ _ _ P M H R Rbar hcfg K hK huniq hcent hKD d hd e
  obtain ⟨hZ, -, ⟨eK⟩, -⟩ := hSoc G 3 P M H R Rbar hcfg K hK huniq hcent d (Or.inl ⟨rfl, hd⟩) e
  exact exists_sp62Data_of hKF hcfg.glob hcfg.ext hcfg.rbar hcfg.red hK huniq
    (hcfg.centralizer_eq_bot hK huniq hcent hZ) hKD hd eK

theorem d1CaseThreeSp62_of' (hDat : StmtSp62Data) (hM : StmtSp62MSide)
    (hres : D1Sp62BlockResidue) : D1CaseThreeSp62 := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e
  obtain ⟨hp3, hd'⟩ := hd
  subst hp3
  obtain ⟨V, hV⟩ := hDat G P M H R Rbar hcfg K hK huniq hcent hKD d hd' e
  obtain ⟨L, hL⟩ := hM hV
  exact hres G 3 P M H R Rbar hcfg K hK huniq hnc hcent hKD d rfl hd' e L hL

theorem d1CaseThreeSp62_closed (hSchur : KFactChevTwoSurvivorSchur) (hKF : KFactSp62Local)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) (hLevi : KFactBlockLeviU42) (hres : D1Sp62BlockResidue) :
    D1CaseThreeSp62 :=
  d1CaseThreeSp62_of' (stmtSp62Data_of (stmtChevTwoSocle_of hSchur) hKF)
    (stmtSp62MSide_of h84 h85 h86 h93 hD2 hB3 hb hLevi) hres

end CFSG.AGLEmbedding
