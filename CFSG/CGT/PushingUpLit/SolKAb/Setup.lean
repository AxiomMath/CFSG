module

public import CFSG.CGT.PushingUpLit.SolKAb.Vocab
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.RankThree.GF2n.Basic
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.LieType.BorelTits.Basic
import CFSG.GH74.EvenRank

public section

namespace CFSG.CGT.PushingUpLit.SolKAb

open CFSG CFSG.CGT.Timmesfeld75 CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.RankThree.GF2n (conjSubgroup_eq_self_iff)
open CFSG.Assembly (pCoreOf)

structure STSetting (G : Type) [Group G] [Finite G] (K : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  tight : TightlyEmbedded K
  max : IsMaximalTwoLocal (Subgroup.normalizer (K : Set G))
  fstar : Subgroup.normalizer (K : Set G) ⊓
      Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (K : Set G)) : Set G) ≤
    pCoreOf 2 (Subgroup.normalizer (K : Set G))

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

omit [Finite G] in
theorem pCoreOf_eq_inSubgroup_pCore (M : Subgroup G) :
    pCoreOf 2 M = inSubgroup (CFSG.pCore 2) M :=
  rfl

theorem STSetting.isCharacteristicP (S : STSetting G K) :
    IsCharacteristicP 2 ↥(Subgroup.normalizer (K : Set G)) := by
  have h := S.fstar
  rw [pCoreOf_eq_inSubgroup_pCore] at h
  exact (CFSG.GH74.inf_centralizer_map_subtype_le_iff _ (CFSG.pCore 2 _)).mp h

theorem pCore_two_eq_bot_of_simple_of_nonabelian [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : CFSG.pCore 2 G = ⊥ := by
  have : (CFSG.pCore 2 G).Normal := CFSG.pCore_normal (p := 2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 G) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 G := by
      have h1 := CFSG.pCore_isPGroup (p := 2) (G := G)
      rw [h] at h1
      exact h1.of_surjective (Subgroup.topEquiv (G := G)).toMonoidHom
        (Subgroup.topEquiv (G := G)).surjective
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent G := hp.isNilpotent
    have : IsCyclic G := inferInstance
    obtain ⟨a, b, hab⟩ := hnonab
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    exact hab (by rw [← hm, ← hn]; exact (zpow_mul_comm g m n).symm.symm)

open CFSG.LieType.BorelTits CFSG.RankThree.GF2n.Tim78 in
theorem STSetting.sylowImg_eq_pCoreOf (S : STSetting G K) (R : Sylow 2 K)
    (h : IsCommSubgroup (sylowImg R)) : sylowImg R = pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (K : Set G) with hM
  have hKM : K ≤ M := Subgroup.le_normalizer
  have hP2 : IsPGroup 2 (pCoreOf 2 K) := pCoreOf_isPGroup 2 K
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hQM : pCoreOf 2 M ≤ M := pCoreOf_le 2 M
  have hMQ : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := le_normalizer_pCoreOf 2 M
  have hKP : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K
  have hQK : pCoreOf 2 M ⊓ K ≤ pCoreOf 2 K := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (hQ2.to_le inf_le_left)
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxQ, hxK⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hMQ (hKM hk)) x).mp hxQ,
        K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk)⟩
    · rintro ⟨hxQ, hxK⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hMQ (hKM hk)) x).mpr hxQ, ?_⟩
      have := K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
      simpa [mul_assoc] using this
  have hodd : ∀ a ∈ K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G), Odd (orderOf a) → a = 1 := by
    rintro a ⟨haK, haC⟩ hao
    have hcommq : ∀ q ∈ pCoreOf 2 M, q * a = a * q := by
      intro q hq
      have hqM : q ∈ M := hQM hq
      have h1 : a⁻¹ * q * a ∈ pCoreOf 2 M := by
        have := (Subgroup.mem_normalizer_iff.mp (hMQ (hKM (K.inv_mem haK))) q).mp hq
        simpa [mul_assoc] using this
      have huQ : q⁻¹ * a⁻¹ * q * a ∈ pCoreOf 2 M := by
        have : q⁻¹ * a⁻¹ * q * a = q⁻¹ * (a⁻¹ * q * a) := by group
        rw [this]; exact mul_mem (inv_mem hq) h1
      have huK : q⁻¹ * a⁻¹ * q * a ∈ K := by
        have h2 : q⁻¹ * a⁻¹ * q ∈ K := by
          have := (Subgroup.mem_normalizer_iff.mp (M.inv_mem hqM) a⁻¹).mp (K.inv_mem haK)
          simpa [mul_assoc] using this
        exact K.mul_mem h2 haK
      have huP : q⁻¹ * a⁻¹ * q * a ∈ pCoreOf 2 K := hQK ⟨huQ, huK⟩
      generalize hu : q⁻¹ * a⁻¹ * q * a = u at huQ huK huP
      have hw : a⁻¹ * q * a = q * u := by rw [← hu]; group
      have hcu : u * a = a * u := Subgroup.mem_centralizer_iff.mp haC _ huP
      have hit : ∀ n : ℕ, a⁻¹ ^ n * q * a ^ n = q * u ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have hc : Commute u a := hcu
          have e1 : a⁻¹ * u ^ n * a = u ^ n := by
            calc a⁻¹ * u ^ n * a = a⁻¹ * (u ^ n * a) := by simp only [mul_assoc]
              _ = a⁻¹ * (a * u ^ n) := by rw [(hc.pow_left n).eq]
              _ = u ^ n := by group
          have hstep : a⁻¹ ^ (n + 1) * q * a ^ (n + 1) = a⁻¹ * (a⁻¹ ^ n * q * a ^ n) * a := by
            rw [pow_succ' a⁻¹ n, pow_succ a n]; simp only [mul_assoc]
          rw [hstep, ih]
          calc a⁻¹ * (q * u ^ n) * a = (a⁻¹ * q * a) * (a⁻¹ * u ^ n * a) := by group
            _ = (q * u) * u ^ n := by rw [hw, e1]
            _ = q * u ^ (n + 1) := by rw [pow_succ']; simp only [mul_assoc]
      have h0 := hit (orderOf a)
      simp only [inv_pow, pow_orderOf_eq_one, inv_one, one_mul, mul_one] at h0
      have hu1 : u ^ orderOf a = 1 := by
        have : q * u ^ orderOf a = q * 1 := by rw [mul_one]; exact h0.symm
        exact mul_left_cancel this
      have hou : Odd (orderOf u) := Odd.of_dvd_nat hao (orderOf_dvd_of_pow_eq_one hu1)
      have hu' : u = 1 := eq_one_of_odd_of_isPGroup hQ2 huQ hou
      have h2 : a⁻¹ * q * a = q := by rw [hw, hu', mul_one]
      calc q * a = a * (a⁻¹ * q * a) := by group
        _ = a * q := by rw [h2]
    have haQ : a ∈ pCoreOf 2 M := S.fstar ⟨hKM haK, Subgroup.mem_centralizer_iff.mpr hcommq⟩
    exact eq_one_of_odd_of_isPGroup hQ2 haQ hao
  set C := K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) with hC
  have hC2 : IsPGroup 2 C := by
    intro c
    obtain ⟨n, hn, hn'⟩ := exists_odd_orderOf_pow (c : G)
    have hcn : (c : G) ^ 2 ^ n ∈ C := C.pow_mem c.2 _
    have := hodd _ hcn hn
    obtain ⟨k, hk⟩ := hn' this
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hPR : pCoreOf 2 K ≤ sylowImg R := by
    have hnorm : (Open.pCore 2 K).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    have hle : Open.pCore 2 K ≤ (R : Subgroup K) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := K)).le_sylow_of_normal R
    exact Subgroup.map_mono hle
  have hRC : sylowImg R ≤ C := fun x hx =>
    ⟨(Subgroup.map_subtype_le _) hx,
      Subgroup.mem_centralizer_iff.mpr fun y hy => h y (hPR hy) x hx⟩
  have hCK : C ≤ K := inf_le_left
  have hCR : C = sylowImg R := by
    have h1 : IsPGroup 2 (C.subgroupOf K) := hC2.of_equiv (Subgroup.subgroupOfEquivOfLe hCK).symm
    have h2 : (R : Subgroup K) ≤ C.subgroupOf K := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]; exact hRC ⟨x, hx, rfl⟩
    have h3 := R.is_maximal' h1 h2
    rw [← Subgroup.map_subgroupOf_eq_of_le hCK, h3]
  have hnormC : (C.subgroupOf K).Normal := by
    constructor
    intro x hx k
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨K.mul_mem (K.mul_mem k.2 hx.1) (K.inv_mem k.2), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hy' : (k : G)⁻¹ * y * k ∈ pCoreOf 2 K := by
      have := (Subgroup.mem_normalizer_iff.mp (hKP (K.inv_mem k.2)) y).mp hy
      simpa [mul_assoc] using this
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hy'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc y * (↑k * ↑x * (↑k)⁻¹) = ↑k * (((k : G)⁻¹ * y * k) * ↑x) * (↑k)⁻¹ := by group
      _ = ↑k * (↑x * ((k : G)⁻¹ * y * k)) * (↑k)⁻¹ := by rw [hc]
      _ = (↑k * ↑x * (↑k)⁻¹) * y := by group
  refine le_antisymm ?_ hPR
  refine le_pCoreOf 2 (Subgroup.map_subtype_le _) ?_ (isPGroup_sylowImg R)
  rw [← hCR]
  exact hnormC


theorem STSetting.sylowImg_ne_bot (S : STSetting G K) (R : Sylow 2 K) : sylowImg R ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : (R : Subgroup K) ≠ ⊥ := R.ne_bot_of_dvd_card (even_iff_two_dvd.mp S.tight.1)
  intro h
  exact hne ((Subgroup.map_eq_bot_iff_of_injective (R : Subgroup K) K.subtype_injective).mp h)

open CFSG.LieType.BorelTits CFSG.RankThree.GF2n.Tim78 in
theorem STSetting.eq_bot_of_normal_of_odd_card (S : STSetting G K) {N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (K : Set G))
    (hNn : (N.subgroupOf (Subgroup.normalizer (K : Set G))).Normal)
    (hodd : Odd (Nat.card ↥N)) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (K : Set G) with hM
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hQM : pCoreOf 2 M ≤ M := pCoreOf_le 2 M
  have hMQ : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := le_normalizer_pCoreOf 2 M
  have hMN : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N := by
    intro m hm n hn
    have := hNn.conj_mem ⟨n, hN hn⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨m, hm⟩
    exact Subgroup.mem_subgroupOf.mp this
  rw [eq_bot_iff]
  intro n hn
  have hcomm : ∀ q ∈ pCoreOf 2 M, n * q = q * n := by
    intro q hq
    have h1 : n * q * n⁻¹ * q⁻¹ ∈ N := by
      have := N.mul_mem hn (hMN q (hQM hq) n⁻¹ (N.inv_mem hn))
      simpa [mul_assoc] using this
    have h2 : n * q * n⁻¹ * q⁻¹ ∈ pCoreOf 2 M := by
      have := (Subgroup.mem_normalizer_iff.mp (hMQ (hN hn)) q).mp hq
      exact mul_mem this (inv_mem hq)
    have h3 : n * q * n⁻¹ * q⁻¹ = 1 := by
      have hodd' : Odd (orderOf (n * q * n⁻¹ * q⁻¹)) :=
        Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N h1)
      exact eq_one_of_odd_of_isPGroup hQ2 h2 hodd'
    calc n * q = n * q * n⁻¹ * q⁻¹ * (q * n) := by group
      _ = q * n := by rw [h3, one_mul]
  have hnQ : n ∈ pCoreOf 2 M :=
    S.fstar ⟨hN hn, Subgroup.mem_centralizer_iff.mpr fun q hq => (hcomm q hq).symm⟩
  have hodd' : Odd (orderOf n) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hn)
  exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_isPGroup hQ2 hnQ hodd')


open CFSG.LieType.BorelTits in
theorem STSetting.normalizer_sylowImg_eq (S : STSetting G K) (R : Sylow 2 K)
    (h : IsCommSubgroup (sylowImg R)) :
    Subgroup.normalizer ((sylowImg R : Subgroup G) : Set G) =
      Subgroup.normalizer (K : Set G) := by
  have hP := S.sylowImg_eq_pCoreOf R h
  have hle : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((sylowImg R : Subgroup G) : Set G) := by
    rw [hP]; exact normalizer_le_normalizer_pCoreOf 2 K
  refine le_antisymm ?_ hle
  by_contra hnot
  exact S.max.2 _ (lt_of_le_of_ne hle (fun h' => hnot (h' ▸ le_rfl)))
    ⟨sylowImg R, S.sylowImg_ne_bot R, isPGroup_sylowImg R, rfl⟩

open CFSG.RankThree.GF2n.Tim78 in
theorem STSetting.isTI_sylowImg (S : STSetting G K) (R : Sylow 2 K)
    (h : IsCommSubgroup (sylowImg R)) : IsTI (sylowImg R) := by
  intro g
  by_cases hg : g ∈ Subgroup.normalizer (K : Set G)
  · right
    have hg' : g ∈ Subgroup.normalizer ((sylowImg R : Subgroup G) : Set G) := by
      rw [S.normalizer_sylowImg_eq R h]; exact hg
    rw [conjSubgroup_eq_self_iff.mpr hg', inf_idem]
  · left
    rw [eq_bot_iff]
    rintro x ⟨hxR, hxg⟩
    have hxg' : g⁻¹ * x * g ∈ sylowImg R := mem_conjSubgroup.mp hxg
    have hxK : x ∈ K := (Subgroup.map_subtype_le _) hxR
    have hgK : g⁻¹ * x * g ∈ K := (Subgroup.map_subtype_le _) hxg'
    have hg' : g⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun h' => hg (by simpa using inv_mem h')
    have hodd := S.tight.2 g⁻¹ hg'
    have hmem : x ∈ K ⊓ rightConjugate K g⁻¹ :=
      ⟨hxK, (mem_rightConjugate_iff K g⁻¹ x).mpr (by simpa using hgK)⟩
    have hox : Odd (orderOf x) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hmem)
    exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_isPGroup (isPGroup_sylowImg R) hxR hox)


theorem STSetting.eq_top_of_isCyclic_sylowImg (S : STSetting G K) (R : Sylow 2 K)
    (h : IsCyclic ↥(sylowImg R)) : (R : Subgroup K) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRc : IsCyclic ↥(R : Subgroup K) := by
    let e : ↥(R : Subgroup K) ≃* ↥(sylowImg R) :=
      (R : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hmin : (Nat.card K).minFac = 2 :=
    (Nat.minFac_eq_two_iff _).mpr (even_iff_two_dvd.mp S.tight.1)
  have hcompl := IsCyclic.isComplement' hmin hRc
  set N := (MonoidHom.transferSylow R (hRc.normalizer_le_centralizer hmin)).ker with hN
  have hcard : Nat.card ↥N * Nat.card ↥(R : Subgroup K) = Nat.card K := hcompl.card_mul_card
  obtain ⟨v, hv⟩ : ∃ v, v = (Nat.card K).factorization 2 := ⟨_, rfl⟩
  have hRcard : Nat.card ↥(R : Subgroup K) = 2 ^ v := by
    rw [hv]; exact R.card_eq_multiplicity
  have hNodd : Odd (Nat.card ↥N) := by
    rcases Nat.even_or_odd (Nat.card ↥N) with he | ho
    · exfalso
      have h2 : 2 ∣ Nat.card ↥N := even_iff_two_dvd.mp he
      have hKne : Nat.card K ≠ 0 := Nat.card_pos.ne'
      have h3 := Nat.pow_succ_factorization_not_dvd hKne Nat.prime_two
      rw [← hv] at h3
      apply h3
      have hK : Nat.card K = Nat.card ↥N * 2 ^ v := by rw [← hcard, hRcard]
      rw [hK, pow_succ, mul_comm (2 ^ v) 2]
      exact Nat.mul_dvd_mul h2 (dvd_refl _) |>.trans (by rw [mul_comm])
    · exact ho
  have hindex : N.index = Nat.card ↥(R : Subgroup K) := hcompl.symm.index_eq_card
  have hoddN : ∀ x : K, Odd (orderOf x) → x ∈ N := by
    intro x hx
    have h1 : orderOf (QuotientGroup.mk x : K ⧸ N) ∣ 2 ^ v := by
      have := orderOf_dvd_natCard (QuotientGroup.mk x : K ⧸ N)
      rwa [← Subgroup.index_eq_card, hindex, hRcard] at this
    have h2 : orderOf (QuotientGroup.mk x : K ⧸ N) ∣ orderOf x := by
      rw [← QuotientGroup.mk'_apply N x]
      exact orderOf_map_dvd (QuotientGroup.mk' N) x
    have h3 : Odd (orderOf (QuotientGroup.mk x : K ⧸ N)) := Odd.of_dvd_nat hx h2
    have h4 : orderOf (QuotientGroup.mk x : K ⧸ N) = 1 := by
      have := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      obtain ⟨k, -, hk⟩ := this
      rcases k with _ | k
      · simpa using hk
      · rw [hk] at h3
        exact absurd h3 (by rw [Nat.not_odd_iff_even]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩)
    exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h4)
  set M := Subgroup.normalizer (K : Set G) with hM
  have hNbot : N.map K.subtype = ⊥ := by
    refine S.eq_bot_of_normal_of_odd_card
      ((Subgroup.map_subtype_le _).trans Subgroup.le_normalizer) ?_ ?_
    · constructor
      intro y hy m
      obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy)
      rw [Subgroup.mem_subgroupOf]
      have hmK : (m : G) * n * (m : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp m.2 n).mp n.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hny]
      refine Subgroup.mem_map.mpr ⟨⟨(m : G) * n * (m : G)⁻¹, hmK⟩, hoddN _ ?_, rfl⟩
      have : orderOf (⟨(m : G) * n * (m : G)⁻¹, hmK⟩ : K) = orderOf n := by
        rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe n]
        exact orderOf_injective (MulAut.conj (m : G)).toMonoidHom (MulAut.conj (m : G)).injective _
      rw [this]
      exact Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hn)
    · rwa [Subgroup.card_map_of_injective K.subtype_injective]
  have hN1 : N = ⊥ := (Subgroup.map_eq_bot_iff_of_injective N K.subtype_injective).mp hNbot
  rw [hN1, Subgroup.card_bot, one_mul] at hcard
  exact Subgroup.card_eq_iff_eq_top _ |>.mp hcard

end CFSG.CGT.PushingUpLit.SolKAb
