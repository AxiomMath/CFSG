module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxChev2
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (KFact131 KFactParabolicGen KFact2715
  IsParabolicTwo)

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M : Subgroup G} {x z : G}
  {T S L : Subgroup G}

namespace P622KxCfg

theorem false_of_chev2_three (hL62 : P622Lemma62Three) (hexit : P622L27Exit) (h131 : KFact131)
    (hgen : KFactParabolicGen) (h2715 : KFact2715) (hsec : KFactParabolicSectionThree)
    (hbot : rankThreePrimeCore 3 (centralizer ({x} : Set G)) = ⊥)
    (c : P622KxCfg 3 P M x z T S L) (hC : IsChevSimple 2 ↥L) : False := by
  have hp := c.prime
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : (3 : ℕ) ≠ 2 := c.ne_two
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
  have hK₁K₀ : K₁ ≤ L ⊓ M := le_inf hpar.1 hK₁M
  have hK₀par : IsParabolicTwo G L (L ⊓ M) := by
    obtain ⟨U, hU, hUN⟩ := hpar.2
    exact ⟨inf_le_left, U, hU, hUN.trans hK₁K₀⟩
  have hK₀ne : L ⊓ M ≠ L := fun h => c.not_le (h.symm.le.trans inf_le_right)
  set W : Subgroup G := S ⊓ L with hW
  have hW2 : IsPGroup 2 W := hS2.to_le inf_le_left
  have hzW : z ∈ normalizer (W : Set G) := c.z_mem_normalizer_inf
  have hWK₀ : W ≤ L ⊓ M := le_inf inf_le_right (inf_le_left.trans hSM)
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
    · have hLJ := h2715 G L W z 3 hB hWs c.z_mem hzW c.orderOf_z hp hp2 (M ⊓ L)
        (le_inf c.normalizer_zpowers_le inf_le_right)
        (le_inf (hWK₀.trans inf_le_right) inf_le_right)
      exact c.not_le (hLJ.trans inf_le_left)
    · have hLJ := hgen G L W hC hB hWs (M ⊓ L) hgenJ
      exact c.not_le (hLJ.trans inf_le_left)
  ·
    have hSyl : ∀ U : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 U (L ⊓ M) →
        ¬ U ≤ rankThreePrimeCore 3 (L ⊓ M) := by
      intro U hU hUD
      obtain ⟨hDK₀, -, -⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 (L ⊓ M)
      have hW1 := c.isSylowOf_inf_primeCore
      have hUD' := hU.of_le hUD hDK₀
      have hcardW1 : Nat.card ↥(S ⊓ rankThreePrimeCore 3 (L ⊓ M)) = Nat.card U := by
        rw [hW1.card_eq, hUD'.card_eq]
      obtain ⟨U₁, hU₁, hU₁N⟩ := hK₀par.2
      have hU₁K₀ : U₁ ≤ L ⊓ M := fun u hu => hU₁N ⟨Subgroup.le_normalizer hu, hU₁.le hu⟩
      have hU₁K₀syl := hU₁.of_le hU₁K₀ inf_le_left
      have hcardU₁ : Nat.card U₁ = Nat.card U := by rw [hU₁K₀syl.card_eq, hU.card_eq]
      have hSDL : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ rankThreePrimeCore 3 (L ⊓ M)) L :=
        CFSG.ABGLocalTools.isSylowOf_of_card (inf_le_right.trans (hDK₀.trans inf_le_left))
          (by rw [hcardW1, ← hcardU₁, hU₁.card_eq])
      have hSDW : S ⊓ rankThreePrimeCore 3 (L ⊓ M) ≤ W :=
        le_inf inf_le_left (inf_le_right.trans (hDK₀.trans inf_le_left))
      have hWeq : W = S ⊓ rankThreePrimeCore 3 (L ⊓ M) := hSDL.eq_of_le hSDW inf_le_right hW2
      exact hWs (by rw [hWeq]; exact hSDL)
    by_cases h168 : Nonempty (↥L ≃* PSL(3, ZMod 2))
    ·
      exact c.conf.failure.fails ⟨rfl, Or.inl (hexit G P M x z T S L c hbot h168)⟩
    · obtain ⟨H, N, hH, hs, hzH, hzN, -⟩ :=
        hsec G L (L ⊓ M) z hC c.rank h168 c.orderOf_z ⟨c.z_mem, hzM⟩ hK₀par hK₀ne hSyl
      exact c.false_of_section_three hL62 (hH.trans inf_le_right) hs hzH hzN

end P622KxCfg

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
