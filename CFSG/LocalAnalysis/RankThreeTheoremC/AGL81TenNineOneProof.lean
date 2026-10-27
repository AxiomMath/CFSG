module

import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenThreeAt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81NineThreeXCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → d1PlusCore p H K ≤ M

@[expose] def AGL81TenNineNormalCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → p ≠ 3 → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)) → (L.subgroupOf M).Normal

@[expose] def AGL81TenNineOneThreeCfg : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    AGL81CfgData 3 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    IsEmpty (↥(barM M L) ≃* alternatingGroup (Fin 7))

variable {G}

theorem false_of_centralizes_cfg (hS : Setting G) (hCGT : AschbacherLocalCGTBlock)
    (hNX : NoXBlockFor G) {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    (hXM : d1PlusCore p H K ≤ M) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hLn : (L.subgroupOf M).Normal)
    (hQL : ∀ b ∈ Q, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) : False := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hM : GLBIsMaxTwoLocal M := hesc.maxTwoLocal_M
  have hQM : Q ≤ M := hd.base.1
  have hQS : Q ≤ normalizer (pCoreOf 2 H : Set G) :=
    hd.le_H.trans (localGroup_le_normalizer_pCoreOf 2 H)
  obtain ⟨R, hSR, hR⟩ := TwoRest3A6.exists_isMaxInvariantTwoIn_ge
    (hd.b3 _ (pCoreOf_isPGroup 2 H) (pCoreOf_le 2 H) hQS) (pCoreOf_isPGroup 2 H) hQS
  have hR1 : R ≠ ⊥ := fun h1 =>
    pCoreOf_two_ne_bot hd.maxH.1 (le_bot_iff.mp (h1 ▸ hSR))
  obtain ⟨hCGS, hRmax⟩ := hd.star R hR hR1
  have hRM : R ≤ M := hR.1.trans hXM
  have hMn : M ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hRL : R ≤ normalizer (L : Set G) := hRM.trans hMn
  have hOR : pCoreOf 2 M ≤ R :=
    TwoRest3A6.le_of_isMaxInvariantTwo hRmax (pCoreOf_isPGroup 2 M)
      (hRM.trans (localGroup_le_normalizer_pCoreOf 2 M))
      (hQM.trans (localGroup_le_normalizer_pCoreOf 2 M))
  have hsyl := TwoRest3A6.not_two_dvd_index_inf_of_isMaxInvariantTwo hRmax hOR hRL hQL
  have hLH : L ≤ H := le_of_normal_block_of_local (aglGlobal_of_setting hS) hCGT hNX hM
    hd.not_le hL.le hLn hRM hRmax.1 hOR hRL hsyl (normalizer_le_of_cgs_le hCGS)
  exact hL.not_le_normalizer (hLH.trans (localGroup_le_normalizer_pCoreOf 2 H))

theorem coprime_six_orderOf_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {B : Subgroup G} (hB : IsPGroup p B) {b : G} (hb : b ∈ B) : Nat.Coprime (orderOf b) 6 := by
  obtain ⟨k, hk⟩ := hB ⟨b, hb⟩
  have hdvd : orderOf b ∣ p ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  rw [hi]
  refine Nat.Coprime.pow_left _ ?_
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_right]
  exact ⟨(Nat.coprime_primes hp Nat.prime_two).mpr hp2,
    (Nat.coprime_primes hp Nat.prime_three).mpr hp3⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
