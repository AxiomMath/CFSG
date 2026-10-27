module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinPair
public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuasisimpleCore
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadical

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

section Abstract

variable {G : Type} [Group G] [Finite G]

theorem charTwo_inf_normalizer_of_le_charTwo {K R P : Subgroup G} (hPK : P ≤ K)
    (hNP : K ⊓ Subgroup.normalizer (R : Set G) ≤ P) (hRP : R ≤ pCoreOf 2 P) (hP : CharTwo P)
    (hrad : pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) = R) :
    CharTwo (K ⊓ Subgroup.normalizer (R : Set G)) := by
  have hX2 : IsPGroup 2 ↥(pCoreOf 2 P) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 P
  have hXP : pCoreOf 2 P ≤ P := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 P
  have hPX : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 P
  have hXR : pCoreOf 2 P ≤ R := by
    by_contra hne
    obtain ⟨x, ⟨hxX, hxN⟩, hxR⟩ := exists_mem_inf_normalizer_not_mem hX2 hRP hne
    have hxK : x ∈ K ⊓ Subgroup.normalizer (R : Set G) := ⟨hPK (hXP hxX), hxN⟩
    set N : Subgroup G := K ⊓ Subgroup.normalizer (R : Set G) with hN
    have hNX : N ≤ Subgroup.normalizer (pCoreOf 2 P : Set G) := hNP.trans hPX
    have hXN : N ≤ Subgroup.normalizer ((pCoreOf 2 P ⊓ N : Subgroup G) : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf N _ N hNX
        Subgroup.le_normalizer
    have h1 : pCoreOf 2 P ⊓ N ≤ pCoreOf 2 N :=
      le_pCoreOf_of_normal_pGroup inf_le_right hXN (hX2.to_le inf_le_left)
    rw [hrad] at h1
    exact hxR (h1 ⟨hxX, hxK⟩)
  have hReq : pCoreOf 2 P = R := le_antisymm hXR hRP
  have hPN : P ≤ K ⊓ Subgroup.normalizer (R : Set G) := by
    refine le_inf hPK ?_
    rw [← hReq]
    exact hPX
  have hN : K ⊓ Subgroup.normalizer (R : Set G) = P := le_antisymm hNP hPN
  rw [hN]
  exact hP

end Abstract

section BorelTits

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_map_subtype_sylow {K : Subgroup G} (P : Sylow 2 ↥K) :
    IsSylowTwoOf ((P : Subgroup ↥K).map K.subtype) K := by
  refine ⟨Subgroup.map_subtype_le _, (P.isPGroup').map K.subtype, ?_⟩
  have h : ((P : Subgroup ↥K).map K.subtype).subgroupOf K = (P : Subgroup ↥K) :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  rw [h]
  exact P.not_dvd_index

theorem map_pCoreOf_le_pCoreOf_map_subtype {K : Subgroup G} (P' : Subgroup ↥K) :
    (pCoreOf 2 P').map K.subtype ≤ pCoreOf 2 (P'.map K.subtype) :=
  le_pCoreOf_of_normal_pGroup (Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 P'))
    ((Subgroup.map_mono (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P')).trans
      (Subgroup.le_normalizer_map _))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P').map K.subtype)

theorem exists_borelTits_of_holds {K R : Subgroup G} (hH : CFSG.LieType.BorelTits.Holds ↥K 2)
    (hRK : R ≤ K) (hR2 : IsPGroup 2 ↥R) (hR : R ≠ ⊥) :
    ∃ S P : Subgroup G, IsSylowTwoOf S K ∧ P ≤ K ∧ P ≠ K ∧
      K ⊓ Subgroup.normalizer (R : Set G) ≤ P ∧ R ≤ pCoreOf 2 P ∧
      K ⊓ Subgroup.normalizer (S : Set G) ≤ P := by
  have hU2 : IsPGroup 2 ↥(R.subgroupOf K) := hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRK).symm
  have hURmap : (R.subgroupOf K).map K.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRK
  have hU : R.subgroupOf K ≠ ⊥ := by
    intro h
    apply hR
    rw [← hURmap, h, Subgroup.map_bot]
  obtain ⟨S, P', hP', hNU, -, hUP, hS⟩ := hH _ hU hU2
  have hSG : IsSylowTwoOf ((S : Subgroup ↥K).map K.subtype) K := isSylowTwoOf_map_subtype_sylow S
  have hSsub : ((S : Subgroup ↥K).map K.subtype).subgroupOf K = (S : Subgroup ↥K) :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  refine ⟨(S : Subgroup ↥K).map K.subtype, P'.map K.subtype, hSG, Subgroup.map_subtype_le _, ?_, ?_,
    ?_, ?_⟩
  · intro h
    apply hP'
    have h2 : P'.map K.subtype = (⊤ : Subgroup ↥K).map K.subtype := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
      exact h
    exact Subgroup.map_injective K.subtype_injective h2
  · rw [← map_subtype_normalizer hRK]
    exact Subgroup.map_mono hNU
  · rw [← hURmap]
    exact (Subgroup.map_mono hUP).trans (map_pCoreOf_le_pCoreOf_map_subtype P')
  · rw [← map_subtype_normalizer hSG.le, hSsub]
    exact Subgroup.map_mono hS

theorem exists_borelTits_of_holds_quotient {K R : Subgroup G}
    (hH : CFSG.LieType.BorelTits.Holds (↥K ⧸ CFSG.pCore 2 ↥K) 2)
    (hq : CFSG.IsQuasisimple ↥K) (hRK : R ≤ K) (hR2 : IsPGroup 2 ↥R)
    (hRC : ¬ R ≤ Subgroup.centralizer (K : Set G)) :
    ∃ S P : Subgroup G, IsSylowTwoOf S K ∧ P ≤ K ∧ P ≠ K ∧
      K ⊓ Subgroup.normalizer (R : Set G) ≤ P ∧ R ≤ pCoreOf 2 P ∧
      K ⊓ Subgroup.normalizer (S : Set G) ≤ P := by
  have hZn : (CFSG.pCore 2 ↥K).Normal := inferInstance
  have hZ2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup
  have hZc : CFSG.pCore 2 ↥K ≤ Subgroup.center ↥K :=
    CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_center_of_quasisimple
      ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩ 2 Nat.prime_two _ hZn hZ2
  let π : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ x : ↥K, π x = 1 → x ∈ CFSG.pCore 2 ↥K := fun x hx => (QuotientGroup.eq_one_iff x).mp hx
  have hU2 : IsPGroup 2 ↥(R.subgroupOf K) := hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRK).symm
  have hURmap : (R.subgroupOf K).map K.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRK
  have hUbar2 : IsPGroup 2 ↥((R.subgroupOf K).map π) := hU2.map π
  have hUbar : (R.subgroupOf K).map π ≠ ⊥ := by
    intro h
    apply hRC
    intro r hr
    have hrU : (⟨r, hRK hr⟩ : ↥K) ∈ R.subgroupOf K := hr
    have hπr : π ⟨r, hRK hr⟩ ∈ (R.subgroupOf K).map π := Subgroup.mem_map_of_mem π hrU
    rw [h, Subgroup.mem_bot] at hπr
    have hcent := hZc (hker _ hπr)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcent ⟨k, hk⟩)
  obtain ⟨Sbar, Pbar, hPbar, hNU, -, hUP, hSbar⟩ := hH _ hUbar hUbar2
  obtain ⟨S0, hS0⟩ := Sylow.mapSurjective_surjective hπ 2 Sbar
  have hS0map : (Sbar : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) = (S0 : Subgroup ↥K).map π := by
    rw [← hS0, Sylow.coe_mapSurjective]
  have hSG : IsSylowTwoOf ((S0 : Subgroup ↥K).map K.subtype) K := isSylowTwoOf_map_subtype_sylow S0
  have hSsub : ((S0 : Subgroup ↥K).map K.subtype).subgroupOf K = (S0 : Subgroup ↥K) :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hP'N : (Subgroup.normalizer ((R.subgroupOf K : Subgroup ↥K) : Set ↥K)) ≤ Pbar.comap π := by
    intro x hx
    exact hNU ((Subgroup.le_normalizer_map π) (Subgroup.mem_map_of_mem π hx))
  have hP'S : (Subgroup.normalizer ((S0 : Subgroup ↥K) : Set ↥K)) ≤ Pbar.comap π := by
    intro x hx
    have := (Subgroup.le_normalizer_map π) (Subgroup.mem_map_of_mem π hx)
    rw [← hS0map] at this
    exact hSbar this
  have hQ2 : IsPGroup 2 ↥((pCoreOf 2 Pbar).comap π) := by
    refine isPGroup_of_forall_pow fun q hq' => ?_
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Pbar ⟨π q, hq'⟩
    have hk' : (π q) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hqk : q ^ 2 ^ k ∈ CFSG.pCore 2 ↥K := hker _ (by rw [map_pow]; exact hk')
    obtain ⟨j, hj⟩ := hZ2 ⟨_, hqk⟩
    exact ⟨k + j, by
      have := congrArg Subtype.val hj
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [pow_add, pow_mul]
      exact this⟩
  have hQP : (pCoreOf 2 Pbar).comap π ≤ Pbar.comap π :=
    Subgroup.comap_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 Pbar)
  have hQn : Pbar.comap π ≤ Subgroup.normalizer (((pCoreOf 2 Pbar).comap π : Subgroup ↥K) : Set ↥K) := by
    rw [← Subgroup.comap_normalizer_eq_of_surjective _ hπ]
    exact Subgroup.comap_mono (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Pbar)
  have hQcore : (pCoreOf 2 Pbar).comap π ≤ pCoreOf 2 (Pbar.comap π) :=
    le_pCoreOf_of_normal_pGroup hQP hQn hQ2
  refine ⟨(S0 : Subgroup ↥K).map K.subtype, (Pbar.comap π).map K.subtype, hSG,
    Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hPbar
    have h2 : (Pbar.comap π).map K.subtype = (⊤ : Subgroup ↥K).map K.subtype := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
      exact h
    have h3 := Subgroup.map_injective K.subtype_injective h2
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ Pbar, h3, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr hπ
  · rw [← map_subtype_normalizer hRK]
    exact Subgroup.map_mono hP'N
  · rw [← hURmap]
    refine (Subgroup.map_mono ?_).trans (map_pCoreOf_le_pCoreOf_map_subtype _)
    intro u hu
    exact hQcore (hUP (Subgroup.mem_map_of_mem π hu))
  · rw [← map_subtype_normalizer hSG.le, hSsub]
    exact Subgroup.map_mono hP'S

theorem charTwo_inf_normalizer_of_borelTits (hBT : RankTwoBorelFacts) {K R : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) (hrt : IsRankTwoEvenType K)
    (hex : ∃ S P : Subgroup G, IsSylowTwoOf S K ∧ P ≤ K ∧ P ≠ K ∧
      K ⊓ Subgroup.normalizer (R : Set G) ≤ P ∧ R ≤ pCoreOf 2 P ∧
      K ⊓ Subgroup.normalizer (S : Set G) ≤ P)
    (hrad : pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) = R) :
    CharTwo (K ⊓ Subgroup.normalizer (R : Set G)) := by
  obtain ⟨S, P, hS, hPK, hPne, hNP, hRP, hSP⟩ := hex
  obtain ⟨hB, P₁, P₂, h1, h2, h3, h4, h5, -, hall, hc1, hc2⟩ := hBT G K S hq hrt hS
  have hP : CharTwo P := by
    rcases eq_or_lt_of_le hSP with hEq | hlt
    · rw [← hEq]
      exact hB
    · rcases hall P hlt (lt_of_le_of_ne hPK hPne) with rfl | rfl
      · exact hc1
      · exact hc2
  exact charTwo_inf_normalizer_of_le_charTwo hPK hNP hRP hP hrad

theorem charTwo_inf_normalizer_of_holds (hBT : RankTwoBorelFacts) {K R : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) (hrt : IsRankTwoEvenType K)
    (hH : CFSG.LieType.BorelTits.Holds ↥K 2) (hRK : R ≤ K) (hR2 : IsPGroup 2 ↥R) (hR : R ≠ ⊥)
    (hrad : pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) = R) :
    CharTwo (K ⊓ Subgroup.normalizer (R : Set G)) :=
  charTwo_inf_normalizer_of_borelTits hBT hq hrt (exists_borelTits_of_holds hH hRK hR2 hR) hrad

theorem charTwo_inf_normalizer_of_holds_quotient (hBT : RankTwoBorelFacts) {K R : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) (hrt : IsRankTwoEvenType K)
    (hH : CFSG.LieType.BorelTits.Holds (↥K ⧸ CFSG.pCore 2 ↥K) 2) (hRK : R ≤ K)
    (hR2 : IsPGroup 2 ↥R) (hRC : ¬ R ≤ Subgroup.centralizer (K : Set G))
    (hrad : pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) = R) :
    CharTwo (K ⊓ Subgroup.normalizer (R : Set G)) :=
  charTwo_inf_normalizer_of_borelTits hBT hq hrt
    (exists_borelTits_of_holds_quotient hH hq hRK hR2 hRC) hrad

end BorelTits

end CFSG.QuasithinUnique.Fin253
