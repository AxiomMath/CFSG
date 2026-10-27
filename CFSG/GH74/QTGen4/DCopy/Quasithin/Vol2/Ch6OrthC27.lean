module

public import CFSG.Quasithin.Vol2.Ch6OrthC27
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C2Seven
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative commutatorElement Matrix

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611

theorem not_oTwoFstarIn_le_of_orth_ch6_F4
    (hC27 : ∀ (G' : Type) [Group G'] [CFSG.GH74.QTGen4.Finite4 G'], ASC27Statement_F4 G') (h432 : Stmt4_3_2_F4)
    (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4) {M₁ : Subgroup G}
    (hM₁ : quasithinIsMaxTwoLocal M₁) (hTM₁ : T ≤ M₁) (hne : M₁ ≠ M) :
    ¬ oTwoFstarIn M₁ ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hF
  set Q₁ := pCoreOf 2 M₁ with hQ₁def
  have hOX : Q₁ ≤ oTwoFstarIn M₁ := pCoreOf_le_oTwoFstarIn M₁
  have hXHK : oTwoFstarIn M₁ ≤ M₁ ⊓ M := le_inf (oTwoFstarIn_le M₁) hF
  have hA := a44Hyp_oTwoFstarIn M₁
  have h1 : pCoreOf 2 (M₁ ⊓ M) = Q₁ := a4_4_1 hOX hXHK hA
  have h2 : CKQ M (pCoreOf 2 (M₁ ⊓ M)) ≤ M₁ ⊓ M := a4_4_2 hOX hXHK hA hM₁
  rw [h1] at h2
  have hQ₁M : Q₁ ≤ M := hOX.trans hF
  have hNQ : Subgroup.normalizer (Q₁ : Set G) = M₁ := eq_normalizer_pCoreOf_of_isMaxTwoLocal hM₁
  have hQ₁ne : Q₁ ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hM₁.1
  have hcc : conjClosure Q₁ (M ⊓ M₁) = Q₁ := by
    apply le_antisymm
    · exact conjClosure_le fun g hg z hz =>
        (Subgroup.mem_normalizer_iff.mp
          ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₁) hg.2) z).mp hz
    · exact le_conjClosure _ _
  have hyp : HypC23 M Q₁ (M ⊓ M₁) :=
    { sqtk := sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian
        (pCoreOf_ne_bot_of_isTwoLocal h.maxTwoLocal.1)
      radical := ⟨hQ₁M, hQ₁ne, by rw [hNQ, inf_comm, h1]⟩
      le := inf_le_left
      cgs := by rw [inf_comm]; exact h2
      sylow := by
        rw [hcc]
        exact ⟨le_rfl, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₁, by simp⟩ }
  by_cases hLM₁ : L ≤ M ⊓ M₁
  · exact hne ((h.isUniqueM_F4 h432).2 M₁ ⟨hM₁, sup_le (hLM₁.trans inf_le_right) hTM₁⟩)
  have hLc := h.mem_cComp_ch6
  have hLchar : CharTwo L := (quasithinGenFitting_eq_pCoreOf_iff L 2).mp h.faithful.2.2.1
  obtain ⟨-, -, h3⟩ := hC27 G M Q₁ (M ⊓ M₁) L _ hyp hLc h.toHyp5_0_1.isQuasisimple hLchar hLM₁
    (hQ₁M.trans h.normal) rfl

  have hOW : pCoreOf 2 L ≤
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (L ⊔ Q₁)) : Set G) := by
    have hOO : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ Q₁) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
        (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
          ((hQ₁M.trans h.normal).trans
            (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact ((Subgroup.mem_centralizer_iff.mp (A4.omegaOneCenterOf_le_centerOf _ hw).2 x
      (hOO hx))).symm
  rcases h3 with ⟨hchi, -⟩ | ⟨⟨k, α, -, -, -, hwith, -⟩, -⟩ | ⟨⟨-, hhat, -⟩, -⟩ |
      ⟨⟨-, ⟨α, hαs, hαk⟩, -⟩, -⟩ | ⟨⟨-, α, hwith6⟩ | ⟨-, F, _, _, hF4, α, hαs, hαk, -⟩, -⟩ |
      ⟨⟨-, hpsu, -⟩, -⟩ | ⟨⟨k, F, _, _, -, hFc, ⟨e⟩⟩, -⟩ | ⟨he | he, -⟩
  · exact h.not_isChiBlock2_ch6 horth M hchi
  · exact card_alternatingGroup_ne_4080_ch6 k (h.card_eq_of_surjective_ch6 α hwith.1 hwith.2.1)
  · have h3 := hhat.2.1
    rw [h.center_quot_eq_bot_ch6, Subgroup.card_bot] at h3
    exact absurd h3 (by norm_num)
  · exact card_alternatingGroup_ne_4080_ch6 7 (h.card_eq_of_surjective_ch6 α hαs hαk)
  · exact card_alternatingGroup_ne_4080_ch6 6
      (h.card_eq_of_surjective_ch6 α hwith6.1 hwith6.2.1)
  · exact card_statedSp_ne_4080_ch6 hF4 (h.card_eq_of_surjective_ch6 α hαs hαk)
  · exact card_ne_4080_of_isPSU_ch6 hpsu h.card_quot_four_ch6
  · have : CharP F 2 := charP_of_card_eq_prime_pow hFc
    obtain ⟨J, hJ4, hJ2⟩ := exists_statedSL3_pow_four_ch6 F
    exact h.false_of_pow_four_ch6 horth hOW e hJ4 hJ2
  · obtain ⟨e⟩ := he
    obtain ⟨J, hJ4, hJ2⟩ := exists_statedSL_two_pow_four_ch6 4 (Or.inl rfl)
    exact h.false_of_pow_four_ch6 horth hOW e hJ4 hJ2
  · obtain ⟨e⟩ := he
    obtain ⟨J, hJ4, hJ2⟩ := exists_statedSL_two_pow_four_ch6 5 (Or.inr rfl)
    exact h.false_of_pow_four_ch6 horth hOW e hJ4 hJ2

end Hyp611

end CFSG.Quasithin.H13
