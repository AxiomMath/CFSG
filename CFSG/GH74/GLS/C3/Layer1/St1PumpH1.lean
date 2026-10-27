module

public import CFSG.GH74.GLS.C3.Layer1.St1P47Rank
public import CFSG.GH74.GLS.C3.Layer1.St1Prop51
public import CFSG.GH74.GLS.C3.Layer1.BkIv81Aux

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpH1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.Uniqueness.SU.SU1 CFSG.GH74.GLS.C3.Layer1.Bk CFSG.GH74.GLS.C3.Layer1.P47
  CFSG.GH74.GLS.IVK.Proofs2

section Elementary

variable {G : Type} [Group G] [Finite G]

theorem eq_of_mem_CxK_of_pRank_le_one {x t : G} {K : Subgroup G} (hpair : IsIL2Pair x K)
    (ht : t ∈ CxK x K) (ht2 : orderOf t = 2) (h1 : pRank 2 ↥(CxK x K) ≤ 1) : t = x := by
  by_contra hne
  have hx : orderOf x = 2 := hpair.1
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    omega
  have hxt : x * t = t * x := (mem_centralizer_singleton_iff.1 ht.1).symm
  have hle : zpowers x ⊔ zpowers t ≤ CxK x K :=
    sup_le ((zpowers_le).2 hpair.x_mem_CxK) ((zpowers_le).2 ht)
  have hel : Open.IsElemAbelian 2 (zpowers x ⊔ zpowers t) := P89.isElemAbelian_pair hx2 ht2' hxt
  have hcard : Nat.card ↥(zpowers x ⊔ zpowers t) = 4 :=
    P89.card_klein hx2 ht2' hxt hx1 ht1 (Ne.symm hne)
  have hEA : CFSG.IsElementaryAbelian 2 ↥(zpowers x ⊔ zpowers t) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mpr hel
  have := le_pRank_of_elem hle hEA (k := 2) (by rw [hcard]; norm_num)
  omega

theorem pLayerOf_self {X K : Subgroup G} (hK : IsPCompIn 2 X K) : pLayerOf 2 K = K :=
  le_antisymm (sSup_le fun _ hL => hL.1) (le_sSup (isPCompIn_of_le hK le_rfl hK.1))

theorem pumpUp_self {x : G} {K : Subgroup G} (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) :
    pumpUp 2 K x = K := by
  unfold pumpUp
  rw [inf_eq_left.2 hK.1, pLayerOf_self hK]
  have hn := pLayerOf_le_normalizer hK
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    have := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hn hg)
    exact this.le
  · refine le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) ?_
    intro k hk
    exact ⟨k, hk, by simp⟩

theorem eq_of_isPCompIn_self {K K' : Subgroup G} (hK : IsPCompIn 2 K K) (hK' : IsPCompIn 2 K K') :
    K' = K := by
  have h := (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
    2 Nat.prime_two (K'.subgroupOf K) (K.subgroupOf K) hK'.2 hK.2).1
    (fun a _ => Subgroup.mem_subgroupOf.2 a.2)
  have h4 := Subgroup.subgroupOf_inj.mp h
  rwa [inf_eq_left.mpr hK'.1, inf_eq_left.mpr hK.1] at h4

theorem pumpUpLT_self {x t : G} {K K' : Subgroup G} (hpair : IsIL2Pair x K)
    (h1 : pRank 2 ↥(CxK x K) ≤ 1) (h : PumpUpLT 2 x K t K') : t = x ∧ K' = K := by
  obtain ⟨-, hILo', htC, htS, hK'⟩ := h
  have ht : t = x := eq_of_mem_CxK_of_pRank_le_one hpair ⟨htC, htS⟩ hILo'.1 h1
  rw [ht, pumpUp_self hpair.2] at hK'
  exact ⟨ht, eq_of_isPCompIn_self (isPCompIn_of_le hpair.2 le_rfl hpair.2.1) hK'⟩

theorem isTrivialPumpupAt_self {x : G} {K : Subgroup G} (hpair : IsIL2Pair x K)
    (h1 : pRank 2 ↥(CxK x K) ≤ 1) : IsTrivialPumpupAt x K x := by
  intro K' hK'
  obtain ⟨-, rfl⟩ := pumpUpLT_self hpair h1 hK'
  exact ⟨hpair.x_mem_CxK.2.1, ⟨MulEquiv.refl _⟩⟩

theorem pumpUpLT_refl {x : G} {K : Subgroup G} (hpair : IsIL2Pair x K)
    (hrank : 3 ≤ pRank 2 ↥(centralizer ({x} : Set G))) : PumpUpLT 2 x K x K := by
  have hILo : IsILo 2 x K := ⟨hpair.1, by simpa [oBound] using hrank, hpair.2⟩
  refine ⟨hILo, hILo, mem_centralizer_singleton_iff.2 rfl, hpair.x_mem_CxK.2, ?_⟩
  rw [pumpUp_self hpair.2]
  exact isPCompIn_of_le hpair.2 le_rfl hpair.2.1

theorem isTerminallyUnbalancing_of_pRank_le_one {x y : G} {K : Subgroup G}
    (hu : IsUnbalancingTriple x y K) (h1 : pRank 2 ↥(CxK x K) ≤ 1) :
    IsTerminallyUnbalancing x y K where
  unbalancing := hu
  trivialPumpups z hz2 hzC _ := by
    rw [eq_of_mem_CxK_of_pRank_le_one hu.1 hzC hz2 h1]
    exact isTrivialPumpupAt_self hu.1 h1
  sylow Q hQ z _ hz2 _ _ K' hK' := by
    obtain ⟨rfl, rfl⟩ := pumpUpLT_self hu.1 h1 hK'
    exact hQ

end Elementary

section Reductions

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_forall_comm {Q : Type} [Group Q] (hcen : center Q = ⊥) :
    ∀ z : Q, (∀ w : Q, z * w = w * z) → z = 1 := by
  intro z hz
  have : z ∈ center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact (hz g).symm
  rw [hcen, Subgroup.mem_bot] at this
  exact this

theorem three_le_pRank_centralizer
    (hL34 : B_gen4_noL34_elem) (hG : Gen4 G) {x : G} {K : Subgroup G} (hpair : IsIL2Pair x K)
    (hU2 : InU2 (kBar K)) : 3 ≤ pRank 2 ↥(centralizer ({x} : Set G)) := by
  have hq : CFSG.IsQuasisimple (kBar K) := hU2.1
  have hcen : center (kBar K) = ⊥ := center_kBar_eq_bot hL34 hG hpair hU2
  have hZ := eq_one_of_forall_comm hcen
  obtain ⟨V, hVel, hV4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq
      (by rw [hcen, Subgroup.card_bot]; exact odd_one))
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := (isElemAbelian_iff.1 hVel).2 v hv
    rwa [sq] at this
  obtain ⟨P, hPK, hPsq, hP4⟩ := exists_lift_klein K V hVsq (by rw [hV4])
  have hx2 : orderOf x = 2 := hpair.1
  have hxsq : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, sq] at this
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    omega
  have hKX : K ≤ centralizer ({x} : Set G) := hpair.2.1
  obtain ⟨-, hBsq, hBcard⟩ := zpowers_sup_facts hxsq hx1 (hPK.trans hKX) hPsq
    (x_not_mem_of_le hpair hZ hPK)
  have hBea : CFSG.IsElementaryAbelian 2 ↥(zpowers x ⊔ P) :=
    isElementaryAbelian_two_of_mul_self _ hBsq
  have hBle : zpowers x ⊔ P ≤ centralizer ({x} : Set G) :=
    sup_le ((Subgroup.zpowers_le).2 (mem_centralizer_singleton_iff.2 rfl)) (hPK.trans hKX)
  have hBpg : IsPGroup 2 ↥(zpowers x ⊔ P) := by
    have := hBea
    exact CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨j, hj⟩ := hBpg.exists_card_eq
  have hP4' : 4 ≤ Nat.card ↥P := Nat.le_of_dvd Nat.card_pos hP4
  have hj3 : 3 ≤ j := by
    by_contra hlt
    have hlt' : j < 3 := not_le.mp hlt
    have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hj3.trans (le_pRank_of_elem hBle hBea hj)

end Reductions

end CFSG.GH74.GLS.C3.Layer1.PumpH1

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1.PumpH1

@[expose] def B_st1_prop51_pumpup_h2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G → St1Prop41 G →
    ∀ (x y : G) (K R : Subgroup G), IsUnbalancingTriple x y K → IsStar2 x →
      IsSylowOf 2 R (NxK x K) → y ∈ R → 2 ≤ pRank 2 ↥(CxK x K) →
        ∃ (z : G) (J : Subgroup G), PumpUpLT 2 x K z J ∧ IsTrivialPumpupAt x K z ∧
          IsTerminallyUnbalancing z y J ∧ z ∈ R ∧ (∀ r ∈ R, z * r = r * z) ∧ z ∈ CxK x K ∧
          IsStar2 z

theorem b_st1_prop51_pumpup_of_h2 (h : B_st1_prop51_pumpup_h2) : B_st1_prop51_pumpup := by
  intro G _ _ hG hN T7 P41 x y K R hu hstar hR hyR
  by_cases h2 : 2 ≤ pRank 2 ↥(CxK x K)
  · exact h G hG hN T7 P41 x y K R hu hstar hR hyR h2
  · have h1 : pRank 2 ↥(CxK x K) ≤ 1 := by omega
    have hrank : 3 ≤ pRank 2 ↥(centralizer ({x} : Set G)) := by
      have h4 := hG.pRank_eq_four
      have := hstar.2
      omega
    have hxN : x ∈ NxK x K := ⟨mem_centralizer_singleton_iff.2 rfl, hu.1.x_mem_CxK.2.1⟩
    have hxR : x ∈ R := C3.Layer1.Back.mem_of_isSylowOf_of_central hR hxN
      (fun s hs => mem_centralizer_singleton_iff.1 hs.1) hu.1.1
    refine ⟨x, K, pumpUpLT_refl hu.1 hrank, isTrivialPumpupAt_self hu.1 h1,
      isTerminallyUnbalancing_of_pRank_le_one hu h1, hxR, fun r hr => ?_, hu.1.x_mem_CxK, hstar⟩
    exact (mem_centralizer_singleton_iff.1 (hR.le hr).1).symm

@[expose] def B_st1_prop41_h2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G →
    (∀ (x y : G) (K : Subgroup G), Hyp4A x y K → 2 ≤ pRank 2 ↥(CxK x K) → 5 ≤ pRank 2 G) ∧
    (∀ (x y : G) (K : Subgroup G), Hyp4B x y K → 2 ≤ pRank 2 ↥(CxK x K) → 5 ≤ pRank 2 G)

theorem b_st1_prop41_of_h2
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem) (h : B_st1_prop41_h2) : B_st1_prop41 := by
  intro G _ _ hG hN T7
  obtain ⟨hA, hB⟩ := h G hG hN T7
  refine ⟨fun x y K h4 => ?_, fun x y K h4 => ?_⟩
  · by_cases h2 : 2 ≤ pRank 2 ↥(CxK x K)
    · exact hA x y K h4 h2
    · exfalso
      have h1 : pRank 2 ↥(CxK x K) ≤ 1 := by omega
      obtain ⟨t, K', hpump, hnt⟩ := h4.nontrivial
      apply hnt
      have ht := (pumpUpLT_self h4.unbalancing.1 h1 hpump).1
      rw [ht] at hpump
      exact isTrivialPumpupAt_self h4.unbalancing.1 h1 K' hpump
  · by_cases h2 : 2 ≤ pRank 2 ↥(CxK x K)
    · exact hB x y K h4 h2
    · exfalso
      have h1 : pRank 2 ↥(CxK x K) ≤ 1 := by omega
      apply h4.notTerminal
      have hpair : IsIL2Pair x K := h4.unbalancing.1
      have hU2 : InU2 (kBar K) := h102 G hG x y K h4.unbalancing.isLocallyUnbalancing
      have hrank := three_le_pRank_centralizer hL34 hG.gen4 hpair hU2
      refine ⟨⟨hpair.1, by simpa [oBound] using hrank, hpair.2⟩, ?_, ?_⟩
      · intro x' K' hpump
        have ht := (pumpUpLT_self hpair h1 hpump).1
        rw [ht] at hpump
        exact isTrivialPumpupAt_self hpair h1 K' hpump
      · intro Q hQ x' K' hpump _ _
        obtain ⟨rfl, rfl⟩ := pumpUpLT_self hpair h1 hpump
        exact hQ

end CFSG.GH74.GLS
