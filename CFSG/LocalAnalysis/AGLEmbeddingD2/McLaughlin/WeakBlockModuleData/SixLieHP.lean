module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieRest
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieHPModels
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieHPFive
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviFam
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieModels

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.AGLEmbedding.ParabHub CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

theorem isElemAbelian_map {A B : Type*} [Group A] [Group B] (f : A →* B) {p : ℕ}
    {V : Subgroup A} (h : IsElemAbelian p V) : IsElemAbelian p (V.map f) :=
  CFSG.SectionRank.isElemAbelian_map h _

theorem pRank_image_eq {Q : Type} [Group Q] [Finite Q] (Lb P : Subgroup Q) (hPL : P ≤ Lb)
    (hZ3 : Nat.Coprime 3 (Nat.card (Subgroup.center ↥Lb))) :
    CFSG.Open.pRank 3 ((P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb))) =
      CFSG.Open.pRank 3 P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set f := (QuotientGroup.mk' (Subgroup.center ↥Lb)).subgroupMap (P.subgroupOf Lb) with hf
  have hfs : Function.Surjective f :=
    (QuotientGroup.mk' (Subgroup.center ↥Lb)).subgroupMap_surjective (P.subgroupOf Lb)
  have hfker : f.ker = (Subgroup.center ↥Lb).subgroupOf (P.subgroupOf Lb) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    have h1 : Nat.card ((Subgroup.center ↥Lb).subgroupOf (P.subgroupOf Lb)) =
        Nat.card ((Subgroup.center ↥Lb ⊓ P.subgroupOf Lb : Subgroup ↥Lb)) := by
      rw [← Subgroup.card_map_of_injective (P.subgroupOf Lb).subtype_injective,
        Subgroup.subgroupOf_map_subtype]
    rw [hfker, h1]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hZ3
  have hrk := CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel 3
    Nat.prime_three f hfs hcop
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← hrk,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (P.subgroupOf Lb)]
  have hmap := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three
    Lb.subtype Lb.subtype_injective (P.subgroupOf Lb)
  rw [Subgroup.map_subgroupOf_eq_of_le hPL] at hmap
  exact hmap.symm

theorem kFactBlockSixLieHP_proved (hG : GriessAllModelsStatement) : KFactBlockSixLieHP := by
  classical
  intro G _ _ M S L hK hAsc hL h2 hsolv hF hrk T hTP hT3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hY, hpar, hS⟩ := h2
  set Lb := barM M L with hLb
  set P := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hP
  have hPL : P ≤ Lb := barM_mono inf_le_right
  have hperfX : Group.IsPerfect ↥Lb := Subgroup.isPerfect_iff.mpr (barM_perfect hL.le hL.perfect)
  have hZ3 := three_coprime_center_of_isFiveList hG hperfX hF
  have hcases := isFiveList_cases hF
  set ρ := QuotientGroup.mk' (Subgroup.center ↥Lb) with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have key : ∀ V : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb),
      V ≤ (P.subgroupOf Lb).map ρ → IsPGroup 3 V → IsElemAbelian 3 V := by
    by_cases hsyl : IsSylowTwoOf (pCoreOf 2 P) Lb
    · intro V hV hV3
      have hT' : IsSylowTwoOf ((pCoreOf 2 P).subgroupOf Lb) ⊤ := by
        have := L246C127.isSylowTwoOf_top_map_subgroupOf (MulEquiv.refl ↥Lb) hsyl
        simpa using this
      obtain ⟨S2, hS2⟩ := exists_sylow_of_isSylowTwoOf_top hT'
      have hPN : P.subgroupOf Lb ≤ Subgroup.normalizer ((S2 : Subgroup ↥Lb) : Set ↥Lb) := by
        intro x hx
        rw [hS2, Subgroup.mem_normalizer_iff]
        intro z
        have hx' := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 P
          (Subgroup.mem_subgroupOf.mp hx)) (z : ↥M ⧸ CFSG.pCore 2 ↥M)
        simpa [Subgroup.mem_subgroupOf] using hx'
      refine isElemAbelian_of_le_normalizer_fiveList hcases (S2.mapSurjective hρs) V ?_ hV3
      rw [Sylow.coe_mapSurjective]
      exact hV.trans ((Subgroup.map_mono hPN).trans (Subgroup.le_normalizer_map ρ))
    · intro V hV hV3
      obtain ⟨T0, hT0, hNJ, hJne, hJperf⟩ := exists_overgroup_quotient_map _ _ hpar hsyl hsolv
      obtain ⟨T', hT'⟩ := exists_sylow_of_isSylowTwoOf_top hT0
      rw [← hT'] at hNJ hJne
      rcases hcases with h | h | h | h | h
      · exact isElemAbelian_of_model_psp_two h T' _ hNJ hJne hJperf V hV hV3
      · exact isElemAbelian_of_model_psp_two h T' _ hNJ hJne hJperf V hV hV3
      · exact isElemAbelian_of_model_pomegaMinus_two h T' _ hNJ hJne hJperf V hV hV3
      · obtain ⟨-, F, hFf, hFfin, hcard, ⟨e⟩⟩ := id h
        have := Fintype.ofFinite F
        have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
          (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
        obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
        have hB := borelQuotient_su hcard (by norm_num) ζ hζ e
        exact isElemAbelian_of_su_even hcard (by norm_num) (by decide) _ hB.surj
          (fun z hz => hB.ker_central z hz) T' _ hNJ hJne hJperf V hV hV3
      · exfalso
        obtain ⟨-, F, hFf, hFfin, hcard, ⟨e⟩⟩ := id h
        have := Fintype.ofFinite F
        have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
          (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
        have h3 := three_le_pRank_su_five hcard e T' _ hNJ hJne hJperf
        rw [pRank_image_eq Lb P hPL hZ3] at h3
        omega
  have hTL : T ≤ Lb := hTP.trans hPL
  have hTsub : IsPGroup 3 (T.subgroupOf Lb) :=
    hT3.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  have hVJ : (T.subgroupOf Lb).map ρ ≤ (P.subgroupOf Lb).map ρ :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr (hTP (Subgroup.mem_subgroupOf.mp hx))
  have hel := key _ hVJ (hTsub.map ρ)
  have hinj : ∀ x ∈ T.subgroupOf Lb, ρ x = 1 → x = 1 := by
    intro x hx hx1
    have hxc : x ∈ Subgroup.center ↥Lb := (QuotientGroup.eq_one_iff x).mp hx1
    obtain ⟨k, hk⟩ := hTsub ⟨x, hx⟩
    have h3 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ Nat.card (Subgroup.center ↥Lb) := Subgroup.orderOf_dvd_natCard _ hxc
    have := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hZ3) h3 h2
    exact orderOf_eq_one_iff.mp this
  have hab := isElemAbelian_of_map ρ hinj hel
  have := isElemAbelian_map Lb.subtype hab
  rwa [Subgroup.map_subgroupOf_eq_of_le hTL] at this

theorem kFactBlockSixLie_of_noSwap (hG : GriessAllModelsStatement)
    (hN : KFactBlockSixLieNoSwap) : KFactBlockSixLie :=
  kFactBlockSixLie_of_parts (kFactBlockSixLieHP_proved hG) hN

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
