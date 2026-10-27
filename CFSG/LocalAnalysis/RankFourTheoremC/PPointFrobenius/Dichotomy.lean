module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Fpf
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MLayer
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

open Subgroup

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC (exists_isSylowOf_ge_of_le isSylowOf_of_sylow_le_of_le)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem fr_centralizer_U_le [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    centralizer ((frU P x : Subgroup G) : Set G) ≤ M :=
  (centralizer_le_normalizer _).trans (fr_normalizer_le hG hl le_rfl (frU_ne_bot hG hl))

theorem fr_dichotomy_N [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {N : Subgroup G} (hUN : frU P x ≤ N) :
    IsSylowOf p (frU P x) N ∨
      ∃ d ∈ centralizer ((frU P x : Subgroup G) : Set G), d * x * d⁻¹ ∈ N := by
  set U := frU P x
  set Z := centralizer ((layerOf x : Subgroup G) : Set G)
  have hUP : U ≤ P := inf_le_left
  obtain ⟨Q, hQN, hUQ⟩ := exists_isSylowOf_ge_of_le hUN (P.isPGroup'.to_le hUP)
  by_cases hQU : Q = U
  · exact Or.inl (hQU ▸ hQN)
  right
  obtain ⟨q, hqQ, hqU⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hUQ (Ne.symm hQU))
  have hPab := hl.abel
  have hQab : IsMulCommutative Q := fr_pGroup_abelian hl Q hQN.isPGroup
  have hPC : (P : Subgroup G) ≤ centralizer (U : Set G) := fun g hg => mem_centralizer_iff.mpr
    fun u hu => congrArg Subtype.val (hPab.is_comm.comm ⟨u, hUP hu⟩ ⟨g, hg⟩)
  have hQC : Q ≤ centralizer (U : Set G) := fun g hg => mem_centralizer_iff.mpr
    fun u hu => congrArg Subtype.val (hQab.is_comm.comm ⟨u, hUQ hu⟩ ⟨g, hg⟩)
  obtain ⟨S, hS, hQS⟩ := exists_isSylowOf_ge_of_le hQC hQN.isPGroup
  obtain ⟨k, hk, hkS⟩ := (isSylowOf_of_sylow_le_of_le P hPC).exists_mem_conj hS
  obtain ⟨hdec, -⟩ := fr_P_eq_sup hG hl
  have hUnorm : U ≤ normalizer (((P : Subgroup G) ⊓ Z : Subgroup G) : Set G) := fun u hu =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz =>
      (mem_centralizer_iff.mp (hPC hz.1) u hu).symm)
  have hmem : k⁻¹ * q * k ∈ ((U ⊔ ((P : Subgroup G) ⊓ Z) : Subgroup G) : Set G) := by
    rw [← hdec]
    exact (hkS q).mp (hQS hqQ)
  rw [coe_mul_of_left_le_normalizer_right _ _ hUnorm] at hmem
  obtain ⟨u, hu, z, hz, huz⟩ := hmem
  have huz : u * z = k⁻¹ * q * k := huz
  have hku : Commute k u⁻¹ := (Commute.inv_right (mem_centralizer_iff.mp hk u hu).symm)
  have hc : k * z * k⁻¹ = u⁻¹ * q := by
    calc k * z * k⁻¹ = k * (u⁻¹ * (u * z)) * k⁻¹ := by group
      _ = k * (u⁻¹ * (k⁻¹ * q * k)) * k⁻¹ := by rw [huz]
      _ = (k * u⁻¹) * k⁻¹ * q := by group
      _ = u⁻¹ * q := by rw [hku.eq, mul_inv_cancel_right]
  have hcQ : k * z * k⁻¹ ∈ Q := hc ▸ Q.mul_mem (Q.inv_mem (hUQ hu)) hqQ
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [mul_one, mul_inv_cancel] at hc
    rw [(inv_mul_eq_one.mp hc.symm).symm] at hqU
    exact hqU hu
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (P.isPGroup'.to_le (zpowers_le.mpr hz.1))
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_zpowers, orderOf_eq_one_iff] at hn
    exact hz1 hn
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p (hn ▸ dvd_pow_self p hn0)
  rw [← orderOf_coe] at hy
  have hyx : zpowers (y : G) = zpowers x :=
    fr_Z0_unique hl (zpowers_le.mpr (zpowers_le.mpr hz y.2)) (by rw [Nat.card_zpowers, hy])
  have hxz : x ∈ zpowers z := zpowers_le.mpr y.2 (hyx ▸ mem_zpowers x)
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hxz
  have hxQ : k * z ^ m * k⁻¹ ∈ Q := by
    rw [← conj_zpow]
    exact Q.zpow_mem hcQ m
  exact ⟨k, hk, hQN.le hxQ⟩

theorem fr_fpf_gen [Fact p.Prime] (hK : FrobKFacts) (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {v : G} (hv1 : v ≠ 1) (hvZ : v ∈ centralizer ((layerOf x : Subgroup G) : Set G))
    (hvp : ¬ p ∣ orderOf v) :
    CFSG.Open.pCoreOf 2 M ⊓ centralizer ({v} : Set G) = ⊥ := by
  have hvU : ∀ u ∈ frU P x, u * v = v * u := fun u hu => mem_centralizer_iff.mp hvZ u hu.2
  have hUN : frU P x ≤ centralizer ({v} : Set G) := fun u hu =>
    mem_centralizer_singleton_iff.mpr (hvU u hu)
  rcases fr_dichotomy_N hG hl hUN with hSyl | ⟨d, hd, hdx⟩
  · exact fr_cT_eq_bot hK hG hl hv1 hvZ (Or.inl hSyl)
  ·
    have hp : p.Prime := Fact.out
    have hdM : d ∈ M := fr_centralizer_U_le hG hl hd
    obtain ⟨v', hv'⟩ : ∃ v' : G, v' = d⁻¹ * v * d := ⟨_, rfl⟩
    have hxv : x * v' = v' * x := by
      have h := mem_centralizer_singleton_iff.mp hdx
      calc x * v' = d⁻¹ * (d * x * d⁻¹ * v) * d := by rw [hv']; group
        _ = d⁻¹ * (v * (d * x * d⁻¹)) * d := by rw [h]
        _ = v' * x := by rw [hv']; group
    have hv'1 : v' ≠ 1 := fun h => hv1 (by
      have : v = d * v' * d⁻¹ := by rw [hv']; group
      rw [this, h]; group)
    have hv'p : ¬ p ∣ orderOf v' := by
      have : v' = MulAut.conj d⁻¹ v := by simp [hv', MulAut.conj_apply]
      rwa [this, MulEquiv.orderOf_eq]
    have hv'U : ∀ u ∈ frU P x, u * v' = v' * u := by
      intro u hu
      have hud : Commute u d := mem_centralizer_iff.mp hd u hu
      have huv : Commute u v := hvU u hu
      rw [hv']
      exact ((hud.inv_right.mul_right huv).mul_right hud).eq
    have hv'Z : v' ∈ centralizer ((layerOf x : Subgroup G) : Set G) := by
      refine fr_lemmaQ hG hl (Y := zpowers v') ?_ ?_ ?_ (mem_zpowers v')
      · rw [Nat.card_zpowers]
        exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hv'p
      · exact zpowers_le.mpr
          (fr_layer_normal_in_centralizer x (mem_centralizer_singleton_iff.mpr hxv.symm))
      · intro u hu
        refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun g hg => ?_)
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hg
        exact ((Commute.zpow_right (show Commute u v' from hv'U u hu) j).eq).symm
    have hbot' := fr_cT_eq_bot hK hG hl hv'1 hv'Z (Or.inr (mem_centralizer_singleton_iff.mpr hxv))
    have hMT : M ≤ normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
    rw [eq_bot_iff]
    intro k hk
    have hk' : d⁻¹ * k * d ∈ CFSG.Open.pCoreOf 2 M ⊓ centralizer ({v'} : Set G) := by
      refine ⟨(mem_normalizer_iff''.mp (hMT hdM) k).mp hk.1, mem_centralizer_singleton_iff.mpr ?_⟩
      have hkv : k * v = v * k := mem_centralizer_singleton_iff.mp hk.2
      calc d⁻¹ * k * d * v' = d⁻¹ * (k * v) * d := by rw [hv']; group
        _ = d⁻¹ * (v * k) * d := by rw [hkv]
        _ = v' * (d⁻¹ * k * d) := by rw [hv']; group
    rw [hbot', mem_bot] at hk'
    have hk1 : k = 1 := by
      have h2 : k = d * (d⁻¹ * k * d) * d⁻¹ := by group
      rw [h2, hk']
      group
    exact mem_bot.mpr hk1

theorem fr_isCyclic_of_le_Z [Fact p.Prime] (hK : FrobKFacts) (hG : FrobGlobal G)
    (hl : FrobLocal p P M x) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) {S : Subgroup G}
    (hSZ : S ≤ centralizer ((layerOf x : Subgroup G) : Set G)) (hS : IsPGroup q S) :
    IsCyclic S := by
  have : Fact q.Prime := ⟨hq⟩
  have hp : p.Prime := Fact.out
  by_contra hnc
  have : Fact (IsPGroup q S) := ⟨hS⟩
  obtain ⟨E, -, hEc, hEel⟩ := CFSG.lemma_4_5_a hq2 hnc
  have hEZ : E.map S.subtype ≤ centralizer ((layerOf x : Subgroup G) : Set G) :=
    (map_subtype_le E).trans hSZ
  have hpow : ∀ e : E.map S.subtype, e ^ q = 1 := by
    rintro ⟨_, e, he, rfl⟩
    exact Subtype.ext (by
      simpa using congrArg Subtype.val (CFSG.elemPow_eq_one_of_isElementaryAbelian e he))
  have hcard : Nat.card (E.map S.subtype) = q ^ 2 := by
    rw [card_map_of_injective S.subtype_injective, hEc]
  have hT2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hTq : ¬ q ∣ Nat.card (CFSG.Open.pCoreOf 2 M) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
    rw [hn]
    exact fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  have hEN : E.map S.subtype ≤ normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    hEZ.trans ((fr_centralizer_layer_le hG hl).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane q
    hq _ _ hpow hcard hTq hEN
  refine CFSG.LocalAnalysis.RankThreeTheoremC.pCoreOf_two_ne_bot hl.loc.maxLocal.1 ?_
  rw [hgen]
  refine iSup_eq_bot.mpr fun e => iSup_eq_bot.mpr fun he1 => eq_bot_iff.mpr fun k hk => ?_
  have he1' : (e : G) ≠ 1 := fun h => he1 (Subtype.ext h)
  have heq : orderOf (e : G) ∣ q := orderOf_dvd_of_pow_eq_one (by
    simpa using congrArg Subtype.val (hpow e))
  have hcop' : ¬ p ∣ orderOf (e : G) := fun h =>
    hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp (h.trans heq)).symm
  have hbot := fr_fpf_gen hK hG hl he1' (hEZ e.2) hcop'
  rw [← hbot]
  exact hk

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
