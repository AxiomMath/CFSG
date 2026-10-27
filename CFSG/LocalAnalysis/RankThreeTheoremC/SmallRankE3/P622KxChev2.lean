module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxEmb
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Sylow
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxChev2
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (KFact131 KFactParabolicGen KFact2715
  KFactParabolicCover IsParabolicTwo normalizer_le_normalizer_rankThreePrimeCore
  s622_isSylowOf_inf)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T S L : Subgroup G}

namespace P622KxCfg

theorem z_mem_normalizer_inf (c : P622KxCfg p P M x z T S L) :
    z ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
  inf_normalizer_le_normalizer_inf ⟨c.conf.z_le_normalizer (mem_zpowers z),
    Subgroup.le_normalizer c.z_mem⟩

theorem isSylowOf_inf_primeCore (c : P622KxCfg p P M x z T S L) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ rankThreePrimeCore p (L ⊓ M))
      (rankThreePrimeCore p (L ⊓ M)) := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  set K₀ : Subgroup G := L ⊓ M with hK₀
  set D : Subgroup G := rankThreePrimeCore p K₀ with hD
  obtain ⟨hDK, hKD, hcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p K₀
  have hDC : D ≤ centralizer ({x} : Set G) := hDK.trans (inf_le_left.trans c.le_C)
  have hxD : x ∈ normalizer (D : Set G) :=
    Subgroup.centralizer_le_normalizer (D : Set G) (mem_centralizer_iff.mpr fun h hh =>
      mem_centralizer_singleton_iff.mp (hDC hh))
  have hzK₀ : z ∈ K₀ := ⟨c.z_mem, c.B_le_M (mem_sup_right (mem_zpowers z))⟩
  have hzD : z ∈ normalizer (D : Set G) := hKD hzK₀
  have hBD : zpowers x ⊔ zpowers z ≤ normalizer (D : Set G) :=
    sup_le (zpowers_le.mpr hxD) (zpowers_le.mpr hzD)
  set H' : Subgroup G := centralizer ({x} : Set G) ⊓ normalizer (D : Set G) with hH'
  have hDH' : D ≤ H' := le_inf hDC Subgroup.le_normalizer
  have hDn : (D.subgroupOf H').Normal :=
    (normal_subgroupOf_iff_le_normalizer hDH').mpr inf_le_right
  have hpD : ¬ p ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd c.prime).mp hcop
  have hBp : IsPGroup p ↥(zpowers x ⊔ zpowers z) := P.isPGroup'.to_le c.conf.B_le_P
  have hSK₀ : S ≤ normalizer (K₀ : Set G) :=
    fun s hs => inf_normalizer_le_normalizer_inf ⟨c.S_le_normalizer hs,
      Subgroup.le_normalizer (c.S_le_M hs)⟩
  have hSD : S ≤ normalizer (D : Set G) :=
    hSK₀.trans (normalizer_le_normalizer_rankThreePrimeCore K₀)
  have hSH' : S ≤ H' := le_inf c.conf.S_le_centralizer hSD
  have hmax : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H' S := by
    refine ⟨⟨hSH', c.conf.S_isPGroup, c.conf.B_le_normalizer⟩, fun S' hS' hSS' => ?_⟩
    exact c.conf.isMax.2 S' ⟨hS'.1.trans inf_le_left, hS'.2.1, hS'.2.2⟩ hSS'
  exact s622_isSylowOf_inf c.prime c.ne_two hBp hDH' hDn hpD hBD hmax

theorem false_of_chev2 (hL613 : P622L613) (hp3 : p ≠ 3) (h131 : KFact131)
    (hgen : KFactParabolicGen) (h2715 : KFact2715) (hcov : KFactParabolicCover)
    (c : P622KxCfg p P M x z T S L) (hC : IsChevSimple 2 ↥L) : False := by
  have hp := c.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := c.ne_two
  have hp5 : 5 ≤ p := by
    have h2 : 2 ≤ p := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  have hS2 : IsPGroup 2 S := c.conf.S_isPGroup
  have hSM : S ≤ M := c.S_le_M
  have hzM : z ∈ M := c.B_le_M (mem_sup_right (mem_zpowers z))
  set R : Subgroup G := ⁅zpowers z, S⁆ with hR
  have hRL : R ≤ L := c.commutator_le
  have hRM : R ≤ M := c.conf.R_le_S.trans hSM
  have hzR : z ∈ normalizer (R : Set G) := c.conf.z_le_normalizer_R (mem_zpowers z)
  obtain ⟨K₁, hpar, hRO, hNK⟩ :=
    h131 G L R hC hRL c.conf.R_isPGroup (c.conf.R_ne_bot c.setting)
  have hzK₁ : z ∈ K₁ := hNK ⟨hzR, c.z_mem⟩
  have hQ₁K : pCoreOf 2 K₁ ≤ K₁ := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 K₁
  have hQ₁2 : IsPGroup 2 (pCoreOf 2 K₁) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 K₁
  have hK₁N : K₁ ≤ normalizer (pCoreOf 2 K₁ : Set G) := by
    have hnorm : ((pCoreOf 2 K₁).subgroupOf K₁).Normal :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 K₁ K₁ le_rfl
        (by rw [Subgroup.subgroupOf_self]; infer_instance)
    exact le_normalizer_of_normal_subgroupOf hQ₁K
  have hK₁M : K₁ ≤ M := by
    refine hK₁N.trans (c.normalizer_le (hQ₁K.trans hpar.1) hQ₁2 (hK₁N hzK₁) ?_)
    intro h
    apply c.conf.R_ne_bot c.setting
    exact le_bot_iff.mp (h ▸ le_inf hRO hRM)
  set K₀ : Subgroup G := L ⊓ M with hK₀
  have hK₁K₀ : K₁ ≤ K₀ := le_inf hpar.1 hK₁M
  have hK₀par : IsParabolicTwo G L K₀ := by
    obtain ⟨U, hU, hUN⟩ := hpar.2
    exact ⟨inf_le_left, U, hU, hUN.trans hK₁K₀⟩
  have hK₀ne : K₀ ≠ L := fun h => c.not_le (h.symm.le.trans inf_le_right)
  set W : Subgroup G := S ⊓ L with hW
  have hW2 : IsPGroup 2 W := hS2.to_le inf_le_left
  have hzW : z ∈ normalizer (W : Set G) := c.z_mem_normalizer_inf
  have hWK₀ : W ≤ K₀ := le_inf inf_le_right (inf_le_left.trans hSM)
  by_cases hWs : CFSG.ABGLocalTools.IsSylowOf 2 W L
  ·
    have hgenJ : ∀ Q₂ : Subgroup G, Q₂ ≤ W → Q₂ ≠ ⊥ →
        normalizer (W : Set G) ⊓ L ≤ normalizer (Q₂ : Set G) →
        normalizer (Q₂ : Set G) ⊓ L ≤ M ⊓ L := by
      intro Q₂ hQ₂W hQ₂1 hBor
      have hzQ₂ : z ∈ normalizer (Q₂ : Set G) := hBor ⟨hzW, c.z_mem⟩
      have hQ₂L : Q₂ ≤ L := hQ₂W.trans inf_le_right
      have hQ₂M : Q₂ ≤ M := hQ₂W.trans (hWK₀.trans inf_le_right)
      have hne : Q₂ ⊓ M ≠ ⊥ := by rwa [inf_eq_left.mpr hQ₂M]
      exact inf_le_inf_right L (c.normalizer_le hQ₂L (hW2.to_le hQ₂W) hzQ₂ hne)
    by_cases hB : fusionIsBenderGroup ↥L
    · have hLJ := h2715 G L W z p hB hWs c.z_mem hzW c.orderOf_z hp hp2 (M ⊓ L)
        (le_inf c.normalizer_zpowers_le inf_le_right)
        (le_inf (hWK₀.trans inf_le_right) inf_le_right)
      exact c.not_le (hLJ.trans inf_le_left)
    · have hLJ := hgen G L W hC hB hWs (M ⊓ L) hgenJ
      exact c.not_le (hLJ.trans inf_le_left)
  ·
    have hSyl : ∀ U : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 U K₀ →
        ¬ U ≤ rankThreePrimeCore p K₀ := by
      intro U hU hUD
      obtain ⟨hDK₀, -, -⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p K₀
      have hW1 := c.isSylowOf_inf_primeCore
      have hUD' := hU.of_le hUD hDK₀
      have hcardW1 : Nat.card ↥(S ⊓ rankThreePrimeCore p K₀) = Nat.card U := by
        rw [hW1.card_eq, hUD'.card_eq]
      obtain ⟨U₁, hU₁, hU₁N⟩ := hK₀par.2
      have hU₁K₀ : U₁ ≤ K₀ := fun u hu => hU₁N ⟨Subgroup.le_normalizer hu, hU₁.le hu⟩
      have hU₁K₀syl := hU₁.of_le hU₁K₀ inf_le_left
      have hcardU₁ : Nat.card U₁ = Nat.card U := by rw [hU₁K₀syl.card_eq, hU.card_eq]
      have hSDL : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ rankThreePrimeCore p K₀) L :=
        CFSG.ABGLocalTools.isSylowOf_of_card (inf_le_right.trans (hDK₀.trans inf_le_left))
          (by rw [hcardW1, ← hcardU₁, hU₁.card_eq])
      have hSDW : S ⊓ rankThreePrimeCore p K₀ ≤ W :=
        le_inf inf_le_left (inf_le_right.trans (hDK₀.trans inf_le_left))
      have hWeq : W = S ⊓ rankThreePrimeCore p K₀ := hSDL.eq_of_le hSDW inf_le_right hW2
      exact hWs (by rw [hWeq]; exact hSDL)
    obtain ⟨f, hf, hf2, hfp, ⟨H, N, hH, hs, hzH, hzN, hfd⟩, g, hgL, hgK₀, hgf⟩ :=
      hcov G L K₀ z p hC hp hp5 c.rank c.orderOf_z ⟨c.z_mem, hzM⟩ hK₀par hK₀ne hSyl
    have hsE := c.stronglyEmbedded hL613 hp3 (hH.trans inf_le_left) (hH.trans inf_le_right) hs
      hzH hzN hf hf2 hfp hfd
    have hgM : g ∉ M := fun hgM => hgK₀ ⟨hgL, hgM⟩
    refine hsE.2.2 g hgM (hgf.trans (Subgroup.card_dvd_of_le ?_))
    exact inf_le_inf (inf_le_right : K₀ ≤ M) (Subgroup.map_mono (inf_le_right : K₀ ≤ M))

end P622KxCfg

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
