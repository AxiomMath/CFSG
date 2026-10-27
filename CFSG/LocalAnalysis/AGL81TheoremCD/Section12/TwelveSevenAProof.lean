module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSevenSylow
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.CondAKSylow
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenSeven
import CFSG.LieType.PSp43Local.Transport
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNine

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]
variable {M Q H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

theorem twelveSevenData (h : TwelveCtx G M p Q H)
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) (h6 : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃)
    (h3 : CFSG.Open.pRank 3 M ≤ 3) (hcard : (weakBlockSet M H).ncard = 3) :
    p = 3 ∧ Q ≤ kSub p M H ∧ CFSG.ABGLocalTools.IsSylowOf 3 Q (kSub p M H) ∧
      CFSG.ABGLocalTools.IsSylowOf 3 Q M ∧ TwelveSevenA M H Q := by
  have hp3 : p = 3 := h6.p_eq_three hd
  subst p
  have hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1 :=
    ⟨h6.n₁_eq_one hd, h6.n₂_eq_one hd, h6.n₃_eq_one hd⟩
  have hQK_syl : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ kSub 3 M H) (kSub 3 M H) :=
    h.isSylowOf_inf_kSub
  obtain ⟨e₀⟩ :=
    CFSG.LieType.PSp43Local.nonempty_mulEquiv_W3_of_quotient_pCore_two
      (h6.part_five hd) hQK_syl
  have hcardQK : Nat.card (Q ⊓ kSub 3 M H : Subgroup G) = 81 := by
    rw [← CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435.card_W3]
    exact Nat.card_congr e₀.toEquiv
  have hcardQ : Nat.card Q ≤ 81 :=
    TwelveFiveData.card_le_eighty_one hd hn h3 hcard h.Q_le_M h.Q_isPGroup
  have hQeq : Q ⊓ kSub 3 M H = Q :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  have hQK : Q ≤ kSub 3 M H := hQeq ▸ inf_le_right
  have hQK_syl' : CFSG.ABGLocalTools.IsSylowOf 3 Q (kSub 3 M H) := hQeq ▸ hQK_syl
  have hcardQ81 : Nat.card Q = 81 := hQeq ▸ hcardQK
  have hQMsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q M := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨h.Q_le_M, h.Q_isPGroup, ?_⟩
    intro hdvd
    have h3dvdM : 3 ^ 5 ∣ Nat.card M := by
      have hmul : Nat.card M = Q.relIndex M * 81 := by
        rw [← Subgroup.relIndex_mul_card (H := Q) (K := M),
          inf_eq_left.mpr h.Q_le_M, hcardQ81]
      obtain ⟨k, hk⟩ := hdvd
      rw [hmul, hk]
      exact ⟨k, by ring⟩
    obtain ⟨K, hKcard, _, hKM⟩ :=
      Sylow.exists_subgroup_card_pow_prime_le_le (p := 3) (n := 5) (H := Q) (L := M)
        Nat.prime_three (by rw [hcardQ81]; norm_num) h3dvdM h.Q_le_M
    have hKpg : IsPGroup 3 K := IsPGroup.of_card hKcard
    have hle := TwelveFiveData.card_le_eighty_one hd hn h3 hcard hKM hKpg
    have h243 : Nat.card K = 243 := by rw [hKcard]; norm_num
    omega
  have hJ_syl : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ jSub M H) (jSub M H) :=
    hQMsyl.inf_of_le_normalizer (jSub_le M H) hd.le_normalizer_jSub
  obtain ⟨hcardJ, hcommJ⟩ :=
    TwelveFiveData.card_eq_and_comm_of_isSylowOf_jSub hd hn h3 hcard hJ_syl
  refine ⟨rfl, hQK, hQK_syl', hQMsyl, ?_⟩
  exact ⟨(MulEquiv.subgroupCongr hQeq).symm.trans e₀, hcommJ, hcardJ⟩

theorem isSylowOf_three_inf (h : TwelveCtx G M p Q H)
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) (h6 : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃)
    (h3 : CFSG.Open.pRank 3 M ≤ 3) (hcard : (weakBlockSet M H).ncard = 3) :
    CFSG.ABGLocalTools.IsSylowOf 3 Q (kSub p M H ⊓ M) := by
  obtain ⟨hp3, hQK, -, hQMsyl, -⟩ := twelveSevenData h hd h6 h3 hcard
  subst p
  exact hQMsyl.of_le (le_inf hQK h.Q_le_M) inf_le_right

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
