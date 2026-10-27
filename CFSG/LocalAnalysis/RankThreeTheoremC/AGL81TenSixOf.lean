module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFiveXOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenCfgOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightCondA
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneComp
import CFSG.Quasithin.Vol2.Ch3Sec3Comp
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup
open scoped commutatorElement

namespace TenFiveX

section Generic

variable {Γ : Type*} [Group Γ]

theorem mul_mem_of_pow_eq_one {A : Subgroup Γ} {k n : Γ} (hk : k ∈ A)
    (hn : n ∈ normalizer (A : Set Γ)) {m : ℕ} (hnm : n ^ m = 1)
    (hcop : Nat.Coprime m (orderOf (k * n))) : k * n ∈ A := by
  have key : ∀ j : ℕ, ∃ a ∈ A, (k * n) ^ j = a * n ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, A.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨a, ha, he⟩ := ih
      have hconj : n ^ j * k * (n ^ j)⁻¹ ∈ A := by
        have hnj : n ^ j ∈ normalizer (A : Set Γ) := Subgroup.pow_mem _ hn j
        exact (Subgroup.mem_normalizer_iff.mp hnj k).mp hk
      refine ⟨a * (n ^ j * k * (n ^ j)⁻¹), A.mul_mem ha hconj, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨a, ha, he⟩ := key m
  rw [hnm, mul_one] at he
  obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hc, he]
  exact A.pow_mem ha c

end Generic

section Cfg

variable {G : Type} [Group G] [Finite G]

theorem commute_of_perfect {H J : Subgroup G} {N₀ : Subgroup H} [N₀.Normal] (hJH : J ≤ H)
    (hperf : ⁅J, J⁆ = J)
    (hJN : ∀ g (hg : g ∈ J), ∀ n ∈ N₀,
      Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨g, hJH hg⟩)
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) n))
    {z : G} (hz : z ∈ H)
    (hJz : ∀ g (hg : g ∈ J),
      ((⟨g, hJH hg⟩ : H) * ⟨z, hz⟩ * (⟨g, hJH hg⟩ : H)⁻¹ * (⟨z, hz⟩ : H)⁻¹ : H) ∈ N₀) :
    ∀ g (hg : g ∈ J), Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨g, hJH hg⟩)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨z, hz⟩) := by
  set π₂ := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ₂
  set Nh := N₀.map π₂ with hNhdef
  haveI hNh : Nh.Normal := Subgroup.Normal.map inferInstance π₂ (QuotientGroup.mk'_surjective _)
  have hmem : ∀ g (hg : g ∈ J),
      π₂ ⟨g, hJH hg⟩ * π₂ ⟨z, hz⟩ * (π₂ ⟨g, hJH hg⟩)⁻¹ * (π₂ ⟨z, hz⟩)⁻¹ ∈ Nh := by
    intro g hg
    refine ⟨_, hJz g hg, ?_⟩
    simp only [map_inv, map_mul]
  have hcen : ∀ g (hg : g ∈ J), ∀ n' ∈ Nh, Commute (π₂ ⟨g, hJH hg⟩) n' := by
    rintro g hg _ ⟨n, hn, rfl⟩
    exact hJN g hg n hn
  have hC : ⁅J, J⁆ ≤ ((Subgroup.centralizer {π₂ ⟨z, hz⟩}).comap π₂).map H.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⟨a, hJH ha⟩ * ⟨b, hJH hb⟩ * (⟨a, hJH ha⟩ : H)⁻¹ * (⟨b, hJH hb⟩ : H)⁻¹, ?_, rfl⟩
    have key := commute_commutatorElement (hcen a ha) (hcen b hb) (hmem a ha) (hmem b hb)
    show π₂ _ ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_singleton_iff, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [commutatorElement_def] at key
    exact key.eq
  rw [hperf] at hC
  intro g hg
  obtain ⟨g', hg', hgg⟩ := hC hg
  have : g' = ⟨g, hJH hg⟩ := Subtype.ext hgg
  rw [this] at hg'
  exact Subgroup.mem_centralizer_singleton_iff.mp hg'

theorem le_normalizer_map_primeComplementCore {H : Subgroup G} (p : ℕ) :
    H ≤ Subgroup.normalizer
      (((primeComplementCore (G := H) p).map H.subtype : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨⟨h, hh⟩ * n * (⟨h, hh⟩ : H)⁻¹, ?_, rfl⟩
    exact (inferInstance : (primeComplementCore (G := H) p).Normal).conj_mem n hn _
  · rintro ⟨n, hn, hng⟩
    refine ⟨(⟨h, hh⟩ : H)⁻¹ * n * ⟨h, hh⟩, ?_, ?_⟩
    · have := (inferInstance : (primeComplementCore (G := H) p).Normal).conj_mem n hn
        (⟨h, hh⟩ : H)⁻¹
      simpa using this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hng ⊢
      rw [hng]
      group

theorem commutator_mem_of_nineTwelve (h912 : AGL81NineTwelveOneCfg G) (hS : Setting G)
    {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    (hp3 : p ≠ 3) {x : G} (hx : x ∈ d1PlusCore p H K) (hxH : x ∈ H) {Y : Subgroup G}
    (hY : RankThreeUC.AGL81C.IsPComponentIn p Y H) (hYM : ¬ Y ≤ M) {y : G} (hy : y ∈ Y) :
    y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hp : p.Prime := hesc.prime
  have hYc := h912 hS p P M H Q K hd hp3 Y hY hYM
  set N₀ := primeComplementCore (G := H) p with hN₀
  have hYH : Y ≤ H := hY.1
  have hperf : ⁅Y, Y⁆ = Y := Subgroup.isPerfect_iff.1 (hY.isPerfect hp)
  have hsubY : IsSubnormal Y H := (IsSubnormal.iff_subgroupOf hYH).2 hYc.2.1
  have hq : Open.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    ⟨hYc.2.2.1.1.commutator_eq_top, hYc.2.2.1.2.1⟩
  rcases CFSG.Quasithin.H13.Ch3Sec3.le_or_commutator_le_pCoreOf hsubY hperf hq
      (Subgroup.map_subtype_le _) (le_normalizer_map_primeComplementCore p) with hle | hcomm
  · exfalso
    obtain ⟨K', hKc, -, hYK, -⟩ := hY.2
    have hbot : (Y.subgroupOf H).map (QuotientGroup.mk' N₀) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      intro w hw
      obtain ⟨n, hn, hnw⟩ := hle hw
      have : n = w := Subtype.ext hnw
      rwa [← this]
    have hK'bot : K' = ⊥ :=
      (hYK : (Y.subgroupOf H).map (QuotientGroup.mk' N₀) = K').symm.trans hbot
    obtain ⟨-, hs, -⟩ := hKc.1
    subst hK'bot
    obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    congr 1
    exact Subtype.ext ((Subgroup.mem_bot.mp a'.2).trans (Subgroup.mem_bot.mp b'.2).symm)
  · have h := commute_of_perfect (N₀ := N₀) hYH hperf
      (fun g hg n hn => commute_of_mem_pCoreOf n.2 (hYH hg)
        (hcomm (Subgroup.commutator_mem_commutator hg ⟨n, hn, rfl⟩))) hxH
      (fun g hg => commutator_mem_of_cfg hd hx hxH hY hYM hg (hYH hg)) y hy
    exact mem_pCoreOf_of_commute hxH (hYH hy) h

theorem commute_of_twoPrime (h1031 : AGL81TenThreeOneAt G) (h98 : AGL81NineEightFour G)
    (hS : Setting G) {P : Sylow 3 G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hd : AGL81CfgData 3 P M H Q K)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {I₀ : Subgroup G}
    (hI₀ : I₀ ∈ cZero (H ⊓ L)) (ha : IsTwoPrimeComponent I₀ I₀) (hI₀H : I₀ ≤ H) :
    ∀ g (hg : g ∈ I₀), ∀ n ∈ primeComplementCore (G := H) 3,
      Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨g, hI₀H hg⟩)
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) n) := by
  set N₀ := primeComplementCore (G := H) 3 with hN₀
  obtain ⟨hV, -, -⟩ := hd.nineEightFour' hS h98
  have hN3 : Nat.Coprime 3 (Nat.card N₀) := primeComplementCore_coprime 3
  have hN₀X : N₀.map H.subtype ≤ H ⊓ M := le_inf (Subgroup.map_subtype_le _) hd.primeCore_le
  have hsub2 : IsSubnormal (H ⊓ L) (H ⊓ M) := by
    have h := hL.subnormal.inf H
    rwa [inf_comm L H, inf_comm M H] at h
  have hI₀sub : IsSubnormal I₀ (H ⊓ M) := hI₀.subnormal.trans hsub2
  have hq := isQuasisimple_of_isTwoPrimeComponent_self ha
  rcases CFSG.Quasithin.H13.Ch3Sec3.le_or_commutator_le_pCoreOf hI₀sub ha.perfect hq hN₀X
      (inf_le_left.trans (le_normalizer_map_primeComplementCore 3)) with hle | hcomm
  · exfalso
    have h3I := h1031 hS 3 P M H Q K hd L hL I₀ hI₀
    have hdvd : Nat.card (CFSG.ComponentClassification.AS76b.oUpperTwo I₀) ∣ Nat.card N₀ := by
      rw [← Subgroup.card_map_of_injective H.subtype_injective]
      exact Subgroup.card_dvd_of_le ((oUpperTwo_le_self I₀).trans hle)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3 (h3I.trans hdvd)
  · intro g hg n hn
    have hgn : g * (n : G) * g⁻¹ * (n : G)⁻¹ ∈ pCoreOf 2 H := by
      rw [← hV]
      exact hcomm (Subgroup.commutator_mem_commutator hg ⟨n, hn, rfl⟩)
    exact commute_of_mem_pCoreOf n.2 (hI₀H hg) hgn

theorem commutator_mem_of_mem_kbar {p : ℕ} {H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {x b : G}
    (hx : x ∈ d1PlusCore p H K) (hxH : x ∈ H) (hbH : b ∈ H)
    (hb : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨b, hbH⟩ ∈ K) :
    ((⟨x, hxH⟩ : H) * ⟨b, hbH⟩ * (⟨x, hxH⟩ : H)⁻¹ * (⟨b, hbH⟩ : H)⁻¹ : H) ∈
      primeComplementCore (G := H) p := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hxC : π ⟨x, hxH⟩ ∈ Subgroup.centralizer (K : Set _) := by
    obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp hx
    have : x' = ⟨x, hxH⟩ := Subtype.ext hxx
    rw [← this]
    exact hx'
  have hc : π ⟨b, hbH⟩ * π ⟨x, hxH⟩ = π ⟨x, hxH⟩ * π ⟨b, hbH⟩ :=
    Subgroup.mem_centralizer_iff.mp hxC _ hb
  rw [← QuotientGroup.eq_one_iff]
  show π _ = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
  group

end Cfg

end TenFiveX

open TenFiveX

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81TenSixTwelveSolvThreeCfg : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    AGL81CfgData 3 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L), ¬ IsTwoPrimeComponent I₀ I₀ → I₀ ≤ d1PlusCore 3 H K →
      ∀ b ∈ d1LiftX 3 H Q K, ∀ x ∈ I₀, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 H

variable {G}

theorem agl81TenSixTwelveCfg_of (h1031 : AGL81TenThreeOneAt G) (h912 : AGL81NineTwelveOneCfg G)
    (h98 : AGL81NineEightFour G) (hres : AGL81TenSixTwelveSolvThreeCfg G) :
    AGL81TenSixTwelveCfg G := by
  intro hS p P M H Q K hd L hL I₀ hI₀ hIX b hb x hx
  have hI₀H : I₀ ≤ H := hI₀.le.trans inf_le_left
  have hxH : x ∈ H := hI₀H hx
  obtain ⟨⟨b', hb'H⟩, ⟨hbQ, hbK⟩, rfl⟩ := hb
  have hbQ' : b' ∈ Q := hbQ
  have hbK' : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨b', hb'H⟩ ∈ K := hbK
  by_cases hp3 : p = 3
  · subst hp3
    by_cases ha : IsTwoPrimeComponent I₀ I₀
    · have h := commute_of_perfect hI₀H ha.perfect
        (commute_of_twoPrime h1031 h98 hS hd hL hI₀ ha hI₀H) hb'H
        (fun g hg => commutator_mem_of_mem_kbar (hIX hg) (hI₀H hg) hb'H hbK') x hx
      exact mem_pCoreOf_of_commute hxH hb'H h.symm
    · exact hres hS P M H Q K hd L hL I₀ hI₀ ha hIX _ ⟨⟨b', hb'H⟩, ⟨hbQ, hbK⟩, rfl⟩ x hx
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hp : p.Prime := hesc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Y₀, hY₀, hY₀M⟩ := exists_pComponent_not_le_of_cfg hd
  have hJ : ¬ RankThreeUC.AGL81C.pLayerIn p H ≤ M := by
    intro hle
    refine hY₀M (le_trans ?_ hle)
    intro y hy
    refine ⟨⟨y, hY₀.1 hy⟩, ?_, rfl⟩
    exact Subgroup.mem_sSup_of_mem hY₀.2 hy
  set N₀ := primeComplementCore (G := H) p with hN₀
  set kS := (RankThreeUC.AGL81C.kSub p M H).subgroupOf H with hkS
  have hbk : (⟨b', hb'H⟩ : H) ∈ kS := by
    have hK : K = RankThreeUC.AGL81C.kStar p M H := by
      rw [hd.kbar, kStar_eq_d1KBar hJ hd.primeCore_le]
    rw [hK] at hbK'
    obtain ⟨k, hk, hkb⟩ := Subgroup.mem_map.mp hbK'
    have hn : k⁻¹ * ⟨b', hb'H⟩ ∈ N₀ := by
      rw [← QuotientGroup.eq_one_iff]
      show QuotientGroup.mk' N₀ (k⁻¹ * ⟨b', hb'H⟩) = 1
      rw [map_mul, map_inv, hkb, inv_mul_cancel]
    have hnorm := Hyp111.NineEightCondA.primeComplementCore_le_normalizer_kSub hJ hn
    have hpow : (k⁻¹ * ⟨b', hb'H⟩) ^ Nat.card N₀ = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard N₀ hn)
    have hQp : IsPGroup p Q := hd.base.2.1
    obtain ⟨e, he⟩ := hQp ⟨b', hbQ'⟩
    have hbe : (⟨b', hb'H⟩ : H) ^ (p ^ e) = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val he
    have hcop : Nat.Coprime (Nat.card N₀) (orderOf (k * (k⁻¹ * ⟨b', hb'H⟩))) := by
      rw [mul_inv_cancel_left]
      have h1 : orderOf (⟨b', hb'H⟩ : H) ∣ p ^ e := orderOf_dvd_of_pow_eq_one hbe
      have h2 : Nat.Coprime p (Nat.card N₀) := primeComplementCore_coprime p
      exact (Nat.Coprime.pow_left e h2).symm.coprime_dvd_right h1
    have := mul_mem_of_pow_eq_one hk hnorm hpow hcop
    rwa [mul_inv_cancel_left] at this
  set π₂ := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ₂
  have hKC : RankThreeUC.AGL81C.kSub p M H ≤
      ((Subgroup.centralizer {π₂ ⟨x, hxH⟩}).comap π₂).map H.subtype := by
    unfold RankThreeUC.AGL81C.kSub
    rw [if_neg hJ]
    refine sSup_le fun Y ⟨hY, hYM⟩ y hy => ?_
    have hyH : y ∈ H := hY.1 hy
    have h := commutator_mem_of_nineTwelve h912 hS hd hp3 (hIX hx) hxH hY hYM hy
    refine ⟨⟨y, hyH⟩, ?_, rfl⟩
    show π₂ ⟨y, hyH⟩ ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_mem_pCoreOf hxH hyH h).eq
  obtain ⟨b'', hb'', hbb⟩ := hKC (show b' ∈ RankThreeUC.AGL81C.kSub p M H from hbk)
  have : b'' = ⟨b', hb'H⟩ := Subtype.ext hbb
  rw [this] at hb''
  exact mem_pCoreOf_of_commute hxH hb'H (Subgroup.mem_centralizer_singleton_iff.mp hb'')

end CFSG.LocalAnalysis.RankThreeTheoremC
