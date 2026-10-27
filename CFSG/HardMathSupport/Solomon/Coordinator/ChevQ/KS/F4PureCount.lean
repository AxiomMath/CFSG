module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4SU3Rank
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4InnerEx
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSF4Pure

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Pure

theorem inf_zpowers_c3_eq_bot {F : Type} [Field F] {G : Type*} [Group G] (φ : SL(2, F) →* G)
    (hφ : Function.Injective φ) {S : Subgroup G} (hS : ∀ s ∈ S, Commute s (φ u1)) :
    S ⊓ Subgroup.zpowers (φ c3) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzS, hzc⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hzc
  have hcomm : Commute (φ c3 ^ n) (φ u1) := hS _ hzS
  have hcomm' : Commute ((c3 : SL(2, F)) ^ n) u1 := by
    apply hφ
    rw [map_mul, map_mul, map_zpow]
    exact hcomm.eq
  have h1 := F4InnerExAux.c3_zpow_commute_u1 hcomm'
  rw [Subgroup.mem_bot, ← map_zpow, h1, map_one]

theorem exists_rank_three_data {G : Type*} [Group G] {F : Type} [Field F] (h2 : (2 : F) = 0)
    {H : Subgroup G} (ψ : Fin 4 → SL(2, F) →* G) (hψ : ∀ i, Function.Injective (ψ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hH : ∀ i A, ψ i A ∈ H) :
    ∃ (T : Subgroup G) (u : G), T ≤ H ∧ IsElemAbelian 3 T ∧ Nat.card T = 27 ∧ u ∈ H ∧
      u ^ 2 = 1 ∧ u ≠ 1 ∧ ∀ t ∈ T, Commute t u := by
  have hx0 : ψ 0 c3 ^ 3 = 1 := by rw [← map_pow, c3_pow_three, map_one]
  have hx1 : ψ 1 c3 ^ 3 = 1 := by rw [← map_pow, c3_pow_three, map_one]
  have hx2 : ψ 2 c3 ^ 3 = 1 := by rw [← map_pow, c3_pow_three, map_one]
  have hu2 : ψ 3 u1 ^ 2 = 1 := by rw [← map_pow, F4InnerExAux.u1_sq h2, map_one]
  have hu1 : ψ 3 u1 ≠ 1 := fun h =>
    F4InnerExAux.u1_ne_one (hψ 3 (h.trans (map_one (ψ 3)).symm))
  have hx01 : ψ 0 c3 ≠ 1 := fun h => c3_ne_one (hψ 0 (h.trans (map_one (ψ 0)).symm))
  have hx11 : ψ 1 c3 ≠ 1 := fun h => c3_ne_one (hψ 1 (h.trans (map_one (ψ 1)).symm))
  have hx21 : ψ 2 c3 ≠ 1 := fun h => c3_ne_one (hψ 2 (h.trans (map_one (ψ 2)).symm))
  have h01 : Commute (ψ 0 c3) (ψ 1 c3) := hc 0 1 (by decide) _ _
  have h02 : Commute (ψ 0 c3) (ψ 2 c3) := hc 0 2 (by decide) _ _
  have h12 : Commute (ψ 1 c3) (ψ 2 c3) := hc 1 2 (by decide) _ _
  have h0u : Commute (ψ 0 c3) (ψ 3 u1) := hc 0 3 (by decide) _ _
  have h1u : Commute (ψ 1 c3) (ψ 3 u1) := hc 1 3 (by decide) _ _
  have h2u : Commute (ψ 2 c3) (ψ 3 u1) := hc 2 3 (by decide) _ _
  have hind01 : Subgroup.zpowers (ψ 0 c3) ⊓ Subgroup.zpowers (ψ 1 c3) = ⊥ := by
    refine inf_zpowers_c3_eq_bot (ψ 1) (hψ 1) (fun s hs => ?_)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    exact (hc 0 1 (by decide) c3 u1).zpow_left n
  have hle01 : Subgroup.zpowers (ψ 0 c3) ⊔ Subgroup.zpowers (ψ 1 c3) ≤
      Subgroup.centralizer ({ψ 2 u1} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc 0 2 (by decide) c3 u1).eq
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc 1 2 (by decide) c3 u1).eq
  have hind012 : (Subgroup.zpowers (ψ 0 c3) ⊔ Subgroup.zpowers (ψ 1 c3)) ⊓
      Subgroup.zpowers (ψ 2 c3) = ⊥ :=
    inf_zpowers_c3_eq_bot (ψ 2) (hψ 2) fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.1 (hle01 hs)
  have hcomm01 : ∀ a ∈ Subgroup.zpowers (ψ 0 c3), ∀ b ∈ Subgroup.zpowers (ψ 1 c3),
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (h01.zpow_zpow i j).eq
  have hle012 : Subgroup.zpowers (ψ 0 c3) ⊔ Subgroup.zpowers (ψ 1 c3) ≤
      Subgroup.centralizer ({ψ 2 c3} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact h02.eq
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact h12.eq
  have hcomm012 : ∀ a ∈ Subgroup.zpowers (ψ 0 c3) ⊔ Subgroup.zpowers (ψ 1 c3),
      ∀ b ∈ Subgroup.zpowers (ψ 2 c3), a * b = b * a := by
    intro a ha b hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hax : Commute a (ψ 2 c3) := Subgroup.mem_centralizer_singleton_iff.1 (hle012 ha)
    exact (hax.zpow_right j).eq
  have hz0 : Nat.card (Subgroup.zpowers (ψ 0 c3)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx0 hx01]
  have hz1 : Nat.card (Subgroup.zpowers (ψ 1 c3)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx1 hx11]
  have hz2 : Nat.card (Subgroup.zpowers (ψ 2 c3)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx2 hx21]
  refine ⟨(Subgroup.zpowers (ψ 0 c3) ⊔ Subgroup.zpowers (ψ 1 c3)) ⊔ Subgroup.zpowers (ψ 2 c3),
    ψ 3 u1, ?_, ?_, ?_, hH 3 _, hu2, hu1, ?_⟩
  · exact sup_le (sup_le (Subgroup.zpowers_le.2 (hH 0 _)) (Subgroup.zpowers_le.2 (hH 1 _)))
      (Subgroup.zpowers_le.2 (hH 2 _))
  · exact F4InnerExAux.isElemAbelian_sup_of_comm
      (F4InnerExAux.isElemAbelian_sup_of_comm (F4InnerExAux.isElemAbelian_zpowers hx0)
        (F4InnerExAux.isElemAbelian_zpowers hx1) hcomm01)
      (F4InnerExAux.isElemAbelian_zpowers hx2) hcomm012
  · rw [i224_card_sup hcomm012 hind012, i224_card_sup hcomm01 hind01, hz0, hz1, hz2]
  · have hle : (Subgroup.zpowers (ψ 0 c3) ⊔ Subgroup.zpowers (ψ 1 c3)) ⊔
        Subgroup.zpowers (ψ 2 c3) ≤ Subgroup.centralizer ({ψ 3 u1} : Set G) := by
      refine sup_le (sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_))
        (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact h0u.eq
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact h1u.eq
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact h2u.eq
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle ht)

theorem card_innerPart_ge_27_of_data
    {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hBel : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hrank : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B)
    (hZ : Subgroup.center ↥K = ⊥)
    (Θ : MulAut ↥K →* Multiplicative (ZMod (2 * 3)))
    (hΘ : Θ.ker ≤ (MulAut.conj : ↥K →* MulAut ↥K).range)
    {x : X} (hxB : x ∈ B) (hxI : ¬ Bal209F4Aux.InnerAt K x)
    {T : Subgroup X} {u : X} (hTK : T ≤ K) (hTel : IsElemAbelian 3 T) (hTcard : Nat.card T = 27)
    (hTx : ∀ t ∈ T, Commute t x) (hTu : ∀ t ∈ T, Commute t u)
    (huK : u ∈ K) (hxu : Commute x u) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    27 ≤ Nat.card ↥(KSF4Rank.innerPart hBN) := by
  classical
  have hZ' : ∀ z ∈ K, z ∈ Subgroup.centralizer (K : Set X) → z = 1 := by
    intro z hz hzc
    have hmem : (⟨z, hz⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzc (g : X) g.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hx3 : x ^ 3 = 1 := hBel.2 x hxB
  have hx1 : x ≠ 1 := by
    intro h
    apply hxI
    rw [h]
    exact ⟨1, K.one_mem, by simp⟩
  set D : Subgroup X := B ⊓ Subgroup.centralizer (K : Set X)
  have hDel : IsElemAbelian 3 D := i271_isElemAbelian_of_le hBel inf_le_left
  obtain ⟨c₀, hc₀⟩ := i271_exists_card_eq Nat.prime_three hDel
  obtain ⟨m, hm⟩ := i271_exists_card_eq Nat.prime_three hBel
  have hrk : CFSG.Open.pRank 3 B = m := i271_pRank_eq Nat.prime_three hBel hm
  have hTD : ∀ a ∈ T, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 a (hTK ha)
  have hTDbot : T ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzT, hzD⟩ := Subgroup.mem_inf.1 hz
    exact Subgroup.mem_bot.2 (hZ' z (hTK hzT) (Subgroup.mem_inf.1 hzD).2)
  have hTDel : IsElemAbelian 3 (T ⊔ D) := F4InnerExAux.isElemAbelian_sup_of_comm hTel hDel hTD
  have hTDcard : Nat.card ↥(T ⊔ D) = 3 ^ (3 + c₀) := by
    rw [i224_card_sup hTD hTDbot, hTcard, hc₀, pow_add]
    norm_num
  have hTDx : T ⊔ D ≤ Subgroup.centralizer ({x} : Set X) := by
    refine sup_le (fun t ht => ?_) (fun d hd => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hTx t ht).eq
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Bal209F4Aux.commute_of_elemAbelian hBel (Subgroup.mem_inf.1 hd).1 hxB).eq
  have hWcomm : ∀ a ∈ T ⊔ D, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hax : Commute a x := Subgroup.mem_centralizer_singleton_iff.1 (hTDx ha)
    exact (hax.zpow_right j).eq
  have hTDinner : T ⊔ D ≤ Bal209F4Aux.innerSub K := by
    refine sup_le (fun t ht => ?_) (fun d hd => ?_)
    · refine Bal209F4Aux.mem_innerSub.2 ⟨t, hTK ht, ?_⟩
      rw [inv_mul_cancel]
      exact Subgroup.one_mem _
    · refine Bal209F4Aux.mem_innerSub.2 ⟨1, K.one_mem, ?_⟩
      rw [inv_one, one_mul]
      exact (Subgroup.mem_inf.1 hd).2
  have hWbot : (T ⊔ D) ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz2
    rw [Subgroup.mem_bot]
    by_cases hj : (3 : ℤ) ∣ j
    · obtain ⟨l, rfl⟩ := hj
      have hx3z : x ^ (3 : ℤ) = 1 := by simpa using hx3
      rw [zpow_mul, hx3z, one_zpow]
    · exact absurd (Bal209F4Aux.mem_innerSub.1
        (Bal209F4Aux.mem_of_zpow_mem hx3 hx1 hj (hTDinner hz1))) hxI
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hWcard : Nat.card ↥((T ⊔ D) ⊔ Subgroup.zpowers x) = 3 ^ (3 + c₀ + 1) := by
    rw [i224_card_sup hWcomm hWbot, hTDcard, hxcard, pow_succ]
  have hWel : IsElemAbelian 3 ((T ⊔ D) ⊔ Subgroup.zpowers x) :=
    F4InnerExAux.isElemAbelian_sup_of_comm hTDel (F4InnerExAux.isElemAbelian_zpowers hx3) hWcomm
  have hWu : (T ⊔ D) ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({u} : Set X) := by
    refine sup_le (sup_le (fun t ht => ?_) (fun d hd => ?_)) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hTu t ht).eq
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hd).2 u huK).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hxu.eq
  have hWN : (T ⊔ D) ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers u : Set X) :=
    F4InnerExAux.le_normalizer_zpowers_of_commute fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.1 (hWu ht)
  have hPne : Subgroup.zpowers u ≠ ⊥ := fun h => hu1 (Subgroup.zpowers_eq_bot.1 h)
  have hP2 : IsPGroup 2 ↥(Subgroup.zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hu2 hu1, pow_one]
  have hloc : 3 + c₀ + 1 ≤ GLATwoLocalRank 3 X :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer
      (by norm_num) hPne hP2 hWel hWN hWcard
  have hmle : 3 + c₀ + 1 ≤ m := by
    have h := hloc.trans hrank
    rwa [hrk] at h
  have hdec := KSF4Rank.exists_pow_innerAt Θ hΘ hBel hBN hxB hxI
  have hkerD : Nat.card (KSF4Rank.actK hBN).ker ≤ Nat.card D := by
    rw [← Subgroup.card_map_of_injective (f := B.subtype) B.subtype_injective
      (K := (KSF4Rank.actK hBN).ker)]
    apply Subgroup.card_le_of_le
    rintro _ ⟨b, hb, rfl⟩
    refine Subgroup.mem_inf.2 ⟨b.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun β : MulAut ↥K => ((β ⟨y, hy⟩ : ↥K) : X))
      (MonoidHom.mem_ker.1 hb)
    simp only [KSF4Rank.coe_actK, MulAut.one_apply] at h1
    show y * (b : X) = (b : X) * y
    calc y * (b : X) = ((b : X) * y * (b : X)⁻¹) * b := by rw [h1]
      _ = (b : X) * y := by group
  have hBcard : Nat.card B = Nat.card (KSF4Rank.actK hBN).ker *
      Nat.card (KSF4Rank.actK hBN).range := (Subgroup.card_ker_mul_card_range _).symm
  have hR : Nat.card (KSF4Rank.actK hBN).range ≤ 3 * Nat.card ↥(KSF4Rank.innerPart hBN) := by
    have haR : KSF4Rank.actK hBN ⟨x, hxB⟩ ∈ (KSF4Rank.actK hBN).range := ⟨⟨x, hxB⟩, rfl⟩
    have ha3 : KSF4Rank.actK hBN ⟨x, hxB⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxB⟩ : ↥B) ^ 3 = 1 := Subtype.ext hx3
      rw [this, map_one]
    have hcard : Nat.card (Subgroup.zpowers (KSF4Rank.actK hBN ⟨x, hxB⟩)) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ha3)
    let g : ↥(Subgroup.zpowers (KSF4Rank.actK hBN ⟨x, hxB⟩)) × ↥(KSF4Rank.innerPart hBN) →
        ↥(KSF4Rank.actK hBN).range := fun p =>
      ⟨(p.1 : MulAut ↥K) * MulAut.conj (p.2 : ↥K),
        (KSF4Rank.actK hBN).range.mul_mem (Subgroup.zpowers_le.2 haR p.1.2)
          (Subgroup.mem_comap.1 p.2.2)⟩
    have hg : Function.Surjective g := by
      rintro ⟨_, b, rfl⟩
      obtain ⟨i, k, hkK, hkc⟩ := hdec b b.2
      have hb' : x ^ i * (b : X) ∈ B := B.mul_mem (B.pow_mem hxB i) b.2
      have hkE : (⟨k, hkK⟩ : ↥K) ∈ KSF4Rank.innerPart hBN :=
        KSF4Rank.mem_innerPart'.2 ⟨x ^ i * b, hb', fun y => KSF4Rank.conj_eq_of_inner hkc y.2⟩
      have hrel : KSF4Rank.actK hBN ⟨x, hxB⟩ ^ i * KSF4Rank.actK hBN b =
          MulAut.conj (⟨k, hkK⟩ : ↥K) := by
        rw [← map_pow, ← map_mul]
        refine MulEquiv.ext fun y => Subtype.ext ?_
        have hcoe : (((⟨x, hxB⟩ : ↥B) ^ i * b : ↥B) : X) = x ^ i * (b : X) := by simp
        rw [KSF4Rank.coe_actK, hcoe, MulAut.conj_apply]
        simpa using KSF4Rank.conj_eq_of_inner hkc y.2
      refine ⟨(⟨(KSF4Rank.actK hBN ⟨x, hxB⟩ ^ i)⁻¹,
        Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i)⟩, ⟨⟨k, hkK⟩, hkE⟩), ?_⟩
      apply Subtype.ext
      show (KSF4Rank.actK hBN ⟨x, hxB⟩ ^ i)⁻¹ * MulAut.conj (⟨k, hkK⟩ : ↥K) =
        KSF4Rank.actK hBN b
      rw [← hrel]
      group
    calc Nat.card (KSF4Rank.actK hBN).range
        ≤ Nat.card (↥(Subgroup.zpowers (KSF4Rank.actK hBN ⟨x, hxB⟩)) ×
            ↥(KSF4Rank.innerPart hBN)) := Nat.card_le_card_of_surjective g hg
      _ = Nat.card (Subgroup.zpowers (KSF4Rank.actK hBN ⟨x, hxB⟩)) *
            Nat.card ↥(KSF4Rank.innerPart hBN) := Nat.card_prod _ _
      _ ≤ 3 * Nat.card ↥(KSF4Rank.innerPart hBN) := Nat.mul_le_mul_right _ hcard
  have h1 : 3 ^ (3 + c₀ + 1) ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hmle
  have h2 : 3 ^ m ≤ 3 ^ c₀ * (3 * Nat.card ↥(KSF4Rank.innerPart hBN)) := by
    rw [← hm, hBcard, ← hc₀]
    exact Nat.mul_le_mul hkerD hR
  have h3 : 3 ^ (3 + c₀ + 1) = 3 ^ c₀ * 81 := by
    rw [show 3 + c₀ + 1 = c₀ + 4 by omega, pow_add]
    norm_num
  have h4 : 3 ^ c₀ * 81 ≤ 3 ^ c₀ * (3 * Nat.card ↥(KSF4Rank.innerPart hBN)) := by
    rw [← h3]
    exact h1.trans h2
  have h5 := Nat.le_of_mul_le_mul_left h4 (pow_pos (by norm_num) c₀)
  omega

end Pure

section Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem f4Two_equiv {F : Type} [Group F] [Finite F] (hs : IsSimpleGroup F)
    (hq : CFSG.Open.IsQuasisimple F) (hL : IsLieQuot F Bal209F4Aux.IsF4TwoIndex) :
    Nonempty (F ≃* adjointGroup Tag.F4 (GaloisField 2 1)) := by
  classical
  obtain ⟨d, hdF, ⟨eL⟩⟩ := hL
  obtain ⟨d1, hv⟩ := d
  have hq2 : ∃ q : TauCeti.PrimePower, d1 = TauCeti.LieTypeIndex.F4 q ∧ IsTwoPow q 1 := by
    cases d1 with
    | F4 q => exact ⟨q, rfl, hdF⟩
    | _ => simp [Bal209F4Aux.IsF4TwoIndex] at hdF
  obtain ⟨q, rfl, hq2', hqe⟩ := hq2
  have hZ : Subgroup.center F = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center F) with h | h
    · exact h
    · exfalso
      haveI := hs.toNontrivial
      have hcomm : ⁅(⊤ : Subgroup F), (⊤ : Subgroup F)⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro g _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        have hy : y ∈ Subgroup.center F := h ▸ Subgroup.mem_top y
        exact (Subgroup.mem_center_iff.1 hy g).symm
      rw [← _root_.commutator_def, hq.1] at hcomm
      exact top_ne_bot hcomm
  have hK'card : Nat.card (GaloisField 2 1) = q.card := by
    rw [GaloisField.card 2 1 (by norm_num), TauCeti.PrimePower.card_def, hq2', hqe]
  obtain ⟨eB⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).f4 q hv hq2' (GaloisField 2 1)
    hK'card
  let eKq : F ≃* F ⧸ Subgroup.center F :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact ⟨eKq.trans (eL.trans (eB.symm.trans (F4FixedAux.adjointEquiv Tag.F4 (GaloisField 2 1))))⟩

theorem card_innerPart_ge_27
    (hOut : KSF4Rank.F4OutStatement) (hFix : Bal209F4Aux.F4Fixed)
    {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hBSC : IsSCp 3 ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hrank : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B)
    (hLie : IsLieQuot ↥K IsF4EightIndex)
    {x : X} (hxB : x ∈ B) (hxI : ¬ Bal209F4Aux.InnerAt K x) :
    27 ≤ Nat.card ↥(KSF4Rank.innerPart hBN) := by
  classical
  have hBel : IsElemAbelian 3 B := hBSC.2.1
  obtain ⟨hZ, Θ, hΘ⟩ := hOut ↥K hK.2.2 hLie
  obtain ⟨hsimp, hquasi, -, hLieF⟩ := hFix X K x hK hLie (hBN hxB) (hBel.2 x hxB) hxI
  obtain ⟨eH⟩ := f4Two_equiv hsimp hquasi hLieF
  obtain ⟨ι, hinj, hc⟩ :=
    CFSG.RankThree.Chevalley.even_higher_ordinary_exceptional_four_commuting_faithful_SL2
      (GaloisField 2 1) Tag.F4 (Or.inl rfl)
  have h2 : (2 : GaloisField 2 1) = 0 := by
    have h := CharP.cast_eq_zero (GaloisField 2 1) 2
    simpa using h
  let H : Subgroup X := K ⊓ Subgroup.centralizer ({x} : Set X)
  let ψ : Fin 4 → SL(2, GaloisField 2 1) →* X := fun i =>
    H.subtype.comp (eH.symm.toMonoidHom.comp (ι i))
  have hψ : ∀ i, Function.Injective (ψ i) := fun i =>
    H.subtype_injective.comp (eH.symm.injective.comp (hinj i))
  have hψc : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B) := by
    intro i j hij A B
    have h := hc i j hij A B
    show (eH.symm (ι i A) : X) * (eH.symm (ι j B) : X) =
      (eH.symm (ι j B) : X) * (eH.symm (ι i A) : X)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h]
  have hψH : ∀ i A, ψ i A ∈ H := fun i A => (eH.symm (ι i A)).2
  obtain ⟨T, u, hTH, hTel, hTcard, huH, hu2, hu1, hTu⟩ := exists_rank_three_data h2 ψ hψ hψc hψH
  have hTx : ∀ t ∈ T, Commute t x := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hTH ht)).2
  have hxu : Commute x u :=
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 huH).2).symm
  exact card_innerPart_ge_27_of_data hBel hBN hrank hZ Θ hΘ hxB hxI (hTH.trans inf_le_left) hTel
    hTcard hTx hTu (Subgroup.mem_inf.1 huH).1 hxu hu2 hu1

end Chevalley

end KSF4Pure

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
