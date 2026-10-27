module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxCfg

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_core {f : ℕ} {F Fs : Subgroup G} (hFFs : F ≤ Fs) {H : Subgroup G}
    (hHcore : GLBCore f 2 Fs ≤ H) {S₀ : Subgroup G} (hS₀F : S₀ ≤ F)
    (hS₀2 : 2 ≤ CFSG.Open.pRank f S₀) : normalizer (S₀ : Set G) ≤ H :=
  (le_sSup ⟨S₀, hS₀F.trans hFFs, hS₀2, rfl⟩ : normalizer (S₀ : Set G) ≤ GLBCore f 2 Fs).trans
    hHcore

namespace KxCfg

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G} {T S L : Subgroup G}

theorem false_of_le_core {f : ℕ} (c : KxCfg p P M x z T S L) {F : Subgroup G}
    (hFsyl : CFSG.ABGLocalTools.IsSylowOf f F L) {Fs : Sylow f G} (hFFs : F ≤ (Fs : Subgroup G))
    {H : Subgroup G} (hHloc : IsTwoLocal H) (hHcore : GLBCore f 2 (Fs : Subgroup G) ≤ H)
    (hFrank : 2 ≤ CFSG.Open.pRank f F) (hLH : L ≤ H) : False := by
  have hxF : x ∈ normalizer (F : Set G) :=
    Subgroup.centralizer_le_normalizer (F : Set G) (mem_centralizer_iff.mpr fun h hh =>
      mem_centralizer_singleton_iff.mp (c.le_C (hFsyl.le hh)))
  have hxH : x ∈ H := normalizer_le_of_core hFFs hHcore le_rfl hFrank hxF
  have hzH : z ∈ H := hLH c.z_mem
  have hBH : zpowers x ⊔ zpowers z ≤ H := sup_le (zpowers_le.mpr hxH) (zpowers_le.mpr hzH)
  have hRL : ⁅zpowers z, S⁆ ≤ L := c.commutator_le
  have hRM : ⁅zpowers z, S⁆ ≤ M := c.conf.R_le_S.trans c.conf.S_le_M
  have hRC : ⁅zpowers z, S⁆ ≤ centralizer ({x} : Set G) := hRL.trans c.le_C
  have hBR : zpowers x ⊔ zpowers z ≤ normalizer ((⁅zpowers z, S⁆ : Subgroup G) : Set G) :=
    c.conf.B_le_normalizer_of_z hRC c.conf.z_le_normalizer_R
  have hHM : H ≤ M := c.conf.config.prop614 H hHloc hBH
    ⟨⁅zpowers z, S⁆, le_inf (hRL.trans hLH) hRM, c.conf.R_ne_bot, c.conf.R_isPGroup, hBR⟩
  exact c.not_le (hLH.trans hHM)

theorem false_of_gen {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (c : KxCfg p P M x z T S L)
    (hU : ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      4 ≤ CFSG.Open.pRank f (normalizer (U : Set G) ⊓ L))
    (hgen : ∀ F : Subgroup G, CFSG.ABGLocalTools.IsSylowOf f F L → ∀ J : Subgroup G,
      (∀ S₀ : Subgroup G, S₀ ≤ F → 2 ≤ CFSG.Open.pRank f S₀ → normalizer (S₀ : Set G) ⊓ L ≤ J) →
        L ≤ J) : False := by
  haveI : Fact f.Prime := ⟨hf⟩
  have hS := c.conf.config.situation
  obtain ⟨U, hUL, hU1, hU2, hU4⟩ := hU
  have hrk : 4 ≤ CFSG.Open.pRank f (normalizer (U : Set G)) :=
    hU4.trans (CFSG.SectionRank.pRank_mono hf.one_lt inf_le_left)
  have hfdvd : f ∣ Nat.card G :=
    prime_dvd_card_of_pRank_pos f (normalizer (U : Set G)) (by omega)
  have h4 : 4 ≤ GLBTwoLocalRank f G :=
    hrk.trans (local_pRank_le_localRank f hf.one_lt (normalizer (U : Set G)) ⟨U, hU1, hU2, rfl⟩)
  have hβ : f ∈ GLBBetaFour G := ⟨hf, hf2, hfdvd, h4⟩
  obtain ⟨F, hFsyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf f L
  obtain ⟨Fs, hFFs⟩ := hFsyl.isPGroup.exists_le_sylow
  obtain ⟨H, hHloc, hHcore⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.deltaOne_of_fullCore hS.toGlobal.d1Global.pre
      hS.toGlobal.fullCore f hβ Fs
  have hLH : L ≤ H := hgen F hFsyl H fun S₀ hS₀F hS₀2 =>
    inf_le_left.trans (normalizer_le_of_core hFFs hHcore hS₀F hS₀2)
  have hLrank : 4 ≤ CFSG.Open.pRank f L :=
    hU4.trans (CFSG.SectionRank.pRank_mono hf.one_lt inf_le_right)
  have hFrank : 2 ≤ CFSG.Open.pRank f F := by
    rw [pRank_eq_of_isSylowOf hf hFsyl]
    omega
  exact c.false_of_le_core hFsyl hFFs hHloc hHcore hFrank hLH

end KxCfg

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
