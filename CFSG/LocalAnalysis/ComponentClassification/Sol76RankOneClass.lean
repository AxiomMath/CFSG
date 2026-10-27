module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76RankOneClassChain
public import CFSG.Alternating.Multipliers.Main
public import CFSG.GH74.KGroups.M11

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

namespace RankOneClass

theorem footeFamilyType_of_pRank_le_one
    {K : Subgroup G}
    (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) (hrank : CFSG.pRank 2 ↥K ≤ 1) :
    FooteFamilyType K := by
  have hAn : IsQuasisimple (↥K ⧸ CFSG.oddCore ↥K) := LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (oddCore_eq_pPrimeCore_two ↥K)).symm hKq
  obtain ⟨-, -, -, -, -, -, r, -, -, -, hTs, hTnab, hTsyl, -⟩ :=
    UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover.{0, 0} hrank hAn
  have : IsSimpleGroup ((↥K ⧸ CFSG.oddCore ↥K) ⧸ center (↥K ⧸ CFSG.oddCore ↥K)) := hTs
  obtain ⟨P⟩ : Nonempty (Sylow 2 ((↥K ⧸ CFSG.oddCore ↥K) ⧸ center (↥K ⧸ CFSG.oddCore ↥K))) :=
    inferInstance
  obtain ⟨⟨eP⟩, -, -⟩ := hTsyl P
  obtain ⟨e₁⟩ := nonempty_fusionZStar_quotient_equiv ↥K
  let eZ : ↥K ⧸ Open.fusionZStar ↥K ≃*
      (↥K ⧸ CFSG.oddCore ↥K) ⧸ center (↥K ⧸ CFSG.oddCore ↥K) :=
    e₁.trans (Sol78.centerQuotCongr
      (QuotientGroup.quotientMulEquivOfEq (oddCore_eq_pPrimeCore_two ↥K)).symm)
  rcases GorensteinWalter.gorenstein_walter _ hTnab P ⟨_, ⟨eP⟩⟩ with
    h7 | ⟨p, k, hp, hodd, h5, ⟨e⟩⟩
  · obtain ⟨e7⟩ := h7
    exact Or.inl ⟨eZ.trans e7⟩
  · refine Or.inr ⟨p, k, hp.out, fun h => ?_, Nat.pos_of_ne_zero fun h => ?_, h5,
      Or.inl ⟨by decide, Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv _ p k h5
        (eZ.trans e)⟩⟩
    · rw [h] at hodd
      exact absurd hodd (by decide)
    · rw [h, pow_zero] at h5
      omega

theorem oddLieType_fStar_of_classical
    (hCI : GSLit.ClassicalInvolutionInput)
    (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) {x : G} {Y : Subgroup G}
    (hY : IsTwoComponentAt x Y) (hxY : x ∈ Y) (hrank : CFSG.pRank 2 ↥Y ≤ 1) :
    Blueprint.OddLieType (GeneralizedFitting.subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hsF
  set F := GeneralizedFitting.subgroup G with hF
  have : F.Normal := GeneralizedFitting.normal G
  have hZF : center F = ⊥ := center_eq_bot_of_simple_nonab hnF
  have hCF : centralizer (F : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have hcF : c ∈ F := GeneralizedFitting.centralizer_le G hc
    have hcZ : (⟨c, hcF⟩ : F) ∈ center F :=
      mem_center_iff.mpr fun f => Subtype.ext ((mem_centralizer_iff.mp hc) f f.2)
    rw [hZF, mem_bot] at hcZ
    exact mem_bot.mpr (congrArg Subtype.val hcZ)
  have hFeq : Open.genFittingFStar G = F :=
    ClassicalInvolution.genFittingFStar_eq_of_normal_simple F hnF hCF
  let eF : Open.genFittingFStar G ≃* F := MulEquiv.subgroupCongr hFeq
  have : IsSimpleGroup (Open.genFittingFStar G) := eF.isSimpleGroup
  have hnF' : ∃ a b : Open.genFittingFStar G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnF
    refine ⟨eF.symm a, eF.symm b, fun h => hab (eF.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hYq := isQuasisimple_quotient_of_isPComponent hY.2.1 hY.2.2
  obtain ⟨hwit, r, hr, hSY⟩ := classicalInvolutionWitness_of_pRank_le_one Y hYq hrank
  obtain ⟨S⟩ : Nonempty (Sylow 2 Y) := inferInstance
  obtain ⟨eS⟩ := hSY S
  rcases (hCI G hnF' x hY.1 Y hxY (open_isSubnormal_of_isPComponent hY.2.1 hY.2.2) S
      ⟨r, hr, ⟨eS⟩⟩).1 hwit with h | h
  · exact (ClassicalInvolution.oddLieType_congr eF).1 h
  ·
    have hM : Blueprint.NativeSporadic.IsSporadic F .M11 :=
      (ClassicalInvolution.isSporadic_congr eF).1 h
    have hAut := GH74.KGroups.M11.card_mulAut hM
    have hinj : Function.Injective (MulAut.conjNormal (H := F)) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      rw [MonoidHom.mem_ker] at hg
      have hgC : g ∈ centralizer (F : Set G) := mem_centralizer_iff.mpr fun f hf => by
        have h1 := congrArg (fun φ : MulAut F => ((φ ⟨f, hf⟩ : F) : G)) hg
        simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
        calc f * g = g * f * g⁻¹ * g := by rw [h1]
          _ = g * f := by group
      rw [hCF] at hgC
      exact hgC
    have : Finite (MulAut F) := GH74.KGroups.M11.finite_mulAut hM
    have hcardG : Nat.card G ≤ 7920 := (Nat.card_le_card_of_injective _ hinj).trans hAut.le
    have hcardF : 7920 ≤ Nat.card F := by
      obtain ⟨e⟩ := hM
      rw [Nat.card_congr e.toEquiv]
      exact Sporadic.Bridge.M11.le_card_native
    have hFtop : F = ⊤ := Subgroup.eq_top_of_card_eq F
      (le_antisymm (Subgroup.card_le_card_group F) (hcardG.trans hcardF))
    have hxF : x ∈ F := by rw [hFtop]; exact mem_top x
    have hYF : Y ≤ F := by rw [hFtop]; exact le_top
    exact oddLieType_of_classical_in_subgroup hCI hnF hxF hY.1 hYF hY hxY hrank

end RankOneClass

theorem aschbacherRankOneInput_of_classicalInvolution
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels) :
    AschbacherRankOneInput := by
  intro G _ _ hsF hnF K hK hrank
  have hGC : TBLit.GriessMultipliersCentralCovers :=
    @CFSG.Milestones.cl_lit_griess_schur_multipliers_central_covers
  have hβ := card_center_le_two_of_footeFamilyType hGA hGC
    Alternating.Multipliers.schurAlternatingMultiplierInput G
  obtain ⟨t, ht, X, hX, hKX, hZX⟩ := exists_twoComponent_centralizer_center_ne_bot hK hrank
  have hXmax := isSolomonMaximal_of_solomonEquiv hK hKX
  have hKq := isQuasisimple_coreQuot_of_isSolomonMember hK.1
  have hKfam := RankOneClass.footeFamilyType_of_pRank_le_one hKq hrank
  obtain ⟨eKX⟩ := nonempty_fusionZStar_equiv_of_reflTransGen hKX.2
  have hXfam : FooteFamilyType X := footeFamilyType_of_equiv eKX.symm hKfam
  have hXq := isQuasisimple_quotient_of_isPComponent hX.1 hX.2
  have hXt : IsTwoComponentAt t X := ⟨ht, hX.1, hX.2⟩
  have hXrank := pRank_le_one_of_center_ne_bot hXq hXfam (hβ X ⟨t, hXt⟩ hXfam) hZX
  obtain ⟨x, Y, hY, hxY, hYrank⟩ :=
    exists_classical_of_isSolomonMaximal hβ hXmax hXt hXfam hXrank
  exact RankOneClass.oddLieType_fStar_of_classical hCI hsF hnF hY hxY hYrank

end CFSG.ComponentClassification.Sol76
