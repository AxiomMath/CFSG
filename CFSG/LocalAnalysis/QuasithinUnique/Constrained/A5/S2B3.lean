module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLem125
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.GammaLemmas
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2B1

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.S2 CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC Equiv

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

namespace S2

namespace Ctx

variable {t : G} (c : Ctx T M H S L t)
include c

theorem star {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd) (hI : P₂.im (s2I S L) = Estd)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (hP1 : CompChi0Block)
    (hP2 : NoProperA5Block) (H₁ : Subgroup G) (hH₁c : CharTwo H₁)
    (hLSI : L ⊔ s2SI S L ≤ H₁) (hH₁φ : H₁ ≤ Subgroup.normalizer (s2Phi S L : Set G))
    (hex : ∃ S₁ : Subgroup G, IsSylowTwoOf S₁ H₁ ∧ s2SI S L ≤ S₁ ∧ H₁ = L ⊔ S₁) :
    quasithinIsCComponent L H₁ := by
  obtain ⟨S₁, hS₁, hSI₁, hH₁eq⟩ := hex
  have h := c.data
  have hLH₁ : L ≤ H₁ := le_sup_left.trans hLSI
  have hSIH₁ : s2SI S L ≤ H₁ := le_sup_right.trans hLSI
  by_cases hS₁N : S₁ ≤ Subgroup.normalizer (L : Set G)
  · have hN : (L.subgroupOf H₁).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hLH₁).2 ?_
      rw [hH₁eq]
      exact sup_le Subgroup.le_normalizer hS₁N
    have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
      h.isShort.2.2.2.1.resolve_right (L238.card_ne_three_of_isAltType le_rfl h.alt5)
    exact C1GN.mem_cComp_of_short h.isShort hq (A3.subnormal_of_normal hLH₁ hN)
  · have hSIlt : s2SI S L < S₁ :=
      lt_of_le_of_ne hSI₁ fun heq => hS₁N (heq ▸ Data.SI_le_normalizer_L)
    have hcardS : Nat.card S = 2 * Nat.card (s2SI S L) :=
      GammaExtra.card_eq_two_mul_of_relIndex_eq_two s2SI_le_S h.relIndex_SI
    have hS₁ge : 2 * Nat.card (s2SI S L) ≤ Nat.card S₁ := GammaExtra.two_mul_card_le_of_lt hSIlt
    have htwo : twoPart H ≤ twoPart H₁ := by
      rw [← h.cs.sylow.card_eq, ← hS₁.card_eq]
      omega
    have hφH₁ : s2Phi S L ≤ H₁ :=
      phi_le_I.trans (s2I_le_baum.trans (c.R_le_SI.trans hSIH₁))
    have hpH₁ : pCoreOf 2 H₁ ≠ ⊥ := by
      intro hbot
      apply c.phi_ne hE hI
      have : s2Phi S L ≤ pCoreOf 2 H₁ :=
        le_pCoreOf_of_normalizes hφH₁ hH₁φ c.phi_isPGroup
      rw [hbot] at this
      exact le_bot_iff.1 this
    have hpair : IsWitnessPair M (s2SI S L) H₁ :=
      ⟨c.SI_conf, hSIH₁, hpH₁, hH₁c, fun hle => h.cs.not_le (hLH₁.trans hle)⟩
    obtain ⟨heq, hΓ₀, -, -⟩ :=
      IsGamma0.of_isWitnessPair_of_twoPart_le h.cs.setting h.cs.gamma0 hpair htwo
    have hcardS₁ : Nat.card S₁ = Nat.card S := by
      rw [hS₁.card_eq, heq, h.cs.sylow.card_eq]
    have hidx : (s2SI S L).relIndex S₁ = 2 := by
      have h1 := Subgroup.relIndex_mul_card (s2SI S L) S₁
      rw [inf_eq_left.mpr hSI₁] at h1
      have hpos : 0 < Nat.card (s2SI S L) := Nat.card_pos
      have : Nat.card (s2SI S L) * (s2SI S L).relIndex S₁ = Nat.card (s2SI S L) * 2 := by
        rw [mul_comm (Nat.card (s2SI S L)) 2, ← hcardS, ← hcardS₁, ← h1]
        ring
      exact Nat.eq_of_mul_eq_mul_left hpos this
    obtain ⟨K, ⟨hKc, hLK⟩, -⟩ := Vol2Native.lemma_1_2_5 h.cs.setting.qtke.1 h37 h39 hpH₁ hS₁
      hSI₁ hidx.le c.local_SI hLH₁
    have hKM : ¬ K ≤ M := fun hle => h.cs.not_le (hLK.trans hle)
    have hKblock := hP1 G T M H₁ K h.cs.setting hΓ₀ hH₁c hKc hKM
    have hLKeq := hP2 G H₁ S₁ (s2SI S L) K L hH₁c hS₁ hSI₁ hidx hKc hKblock h.isShort h.alt5
      hLK Data.SI_le_normalizer_L c.local_SI
    rw [hLKeq]
    exact hKc

end Ctx

end S2

end CFSG.QuasithinUnique.A5
