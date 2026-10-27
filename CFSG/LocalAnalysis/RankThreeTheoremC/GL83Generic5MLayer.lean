module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5FPF
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5AlmostSimple
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup2
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup

section Elementary

variable {G : Type*} [Group G]

theorem mem_centralizer_of_pow_mem_of_coprime_totient {A : Subgroup G} [Finite A]
    (hAc : IsCyclic A) {g : G} (hg : g ∈ normalizer (A : Set G)) {n : ℕ}
    (hgn : g ^ n ∈ centralizer (A : Set G)) (hcop : Nat.Coprime n (Nat.card A).totient) :
    g ∈ centralizer (A : Set G) := by
  have hker : ∀ {h : normalizer (A : Set G)}, h ∈ A.normalizerMonoidHom.ker ↔
      (h : G) ∈ centralizer (A : Set G) := fun {h} => by
    rw [normalizerMonoidHom_ker, mem_subgroupOf]
  have h1 : A.normalizerMonoidHom ⟨g, hg⟩ ^ n = 1 := by
    rw [← map_pow]
    exact hker.mpr hgn
  have h2 : orderOf (A.normalizerMonoidHom ⟨g, hg⟩) ∣ (Nat.card A).totient := by
    rw [← IsCyclic.card_mulAut]
    exact orderOf_dvd_natCard _
  have h3 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) h2
  exact hker.mp (orderOf_eq_one_iff.mp h3)

theorem mul_mem_of_pow_eq_one_of_coprime {J : Subgroup G} {j o : G} (hj : j ∈ J)
    (ho : ∀ y ∈ J, o * y * o⁻¹ ∈ J) {n : ℕ} (hjo : (j * o) ^ n = 1)
    (hcop : Nat.Coprime n (orderOf o)) : j * o ∈ J := by
  have hok : ∀ k : ℕ, ∀ y ∈ J, o ^ k * y * (o ^ k)⁻¹ ∈ J := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro y hy
      have h : o ^ (k + 1) * y * (o ^ (k + 1))⁻¹ = o * (o ^ k * y * (o ^ k)⁻¹) * o⁻¹ := by
        group
      rw [h]
      exact ho _ (ih y hy)
  have hpow : ∀ k : ℕ, ∃ y ∈ J, (j * o) ^ k = y * o ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, J.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨y, hy, hk⟩ := ih
      refine ⟨y * (o ^ k * j * (o ^ k)⁻¹), J.mul_mem hy (hok k j hj), ?_⟩
      rw [pow_succ, hk, pow_succ]
      group
  obtain ⟨y, hy, hk⟩ := hpow (orderOf o)
  rw [pow_orderOf_eq_one, mul_one] at hk
  have hmem : j * o ∈ zpowers ((j * o) ^ orderOf o) := by
    rw [mem_zpowers_pow_iff]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hjo) hcop.symm
  exact zpowers_le.mpr (hk ▸ hy) hmem

theorem conj_mem_perfectCore {N : Subgroup G} {g : G} (hg : ∀ n ∈ N, g * n * g⁻¹ ∈ N) {k : G}
    (hk : k ∈ perfectCore N) : g * k * g⁻¹ ∈ perfectCore N := by
  have h : (perfectCore N).map (MulAut.conj g).toMonoidHom ≤ perfectCore N := by
    refine le_perfectCore ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact hg k (perfectCore_le N hk)
    · rw [← Subgroup.map_commutator, commutator_perfectCore]
  exact h ⟨k, hk, by simp⟩

theorem zpowers_eq_of_orderOf_eq_of_isCyclic {S : Subgroup G} [Finite S] (hS : IsCyclic S)
    {y z : G} (hy : y ∈ S) (hz : z ∈ S) (hyz : orderOf y = orderOf z) :
    zpowers y = zpowers z := by
  have heq : zpowers (⟨y, hy⟩ : S) = zpowers ⟨z, hz⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hyz]
  have h := congrArg (Subgroup.map S.subtype) heq
  rwa [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h

theorem le_normalizer_zpowers_of_mem_centralizer {U : Subgroup G} {g : G}
    (hg : g ∈ centralizer (U : Set G)) : U ≤ normalizer ((zpowers g : Subgroup G) : Set G) :=
  fun u hu => centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun h hh => by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hh
    exact ((show Commute u g from mem_centralizer_iff.mp hg u hu).zpow_right j).eq.symm)

variable [Finite G]

theorem coprime_totient_card_of_isPGroup {f m : ℕ} (hf : f.Prime) {F : Subgroup G}
    (hF : IsPGroup f F) (hm : ∀ q : ℕ, q.Prime → q ∣ m → f < q) :
    Nat.Coprime m (Nat.card F).totient := by
  have : Fact f.Prime := ⟨hf⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hF
  rw [ha]
  rcases a with _ | a
  · simp
  rw [Nat.totient_prime_pow_succ hf]
  refine Nat.coprime_of_dvd fun q hq hqm hqd => ?_
  have hfq := hm q hq hqm
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hq hf).mp (hq.dvd_of_dvd_pow h)
    omega
  · have := Nat.le_of_dvd (by have := hf.two_le; omega) h
    omega

theorem exists_orderOf_pow_eq (q : ℕ) (hq : q.Prime) (g : G) :
    ∃ c m : ℕ, ¬ q ∣ m ∧ orderOf g = q ^ c * m ∧ orderOf (g ^ m) = q ^ c ∧
      orderOf (g ^ (q ^ c)) = m := by
  obtain ⟨c, m, hm, hcm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' q hq.one_lt.ne'
  have hm0 : m ≠ 0 := fun h => by rw [h, mul_zero] at hcm; exact (orderOf_pos g).ne' hcm
  have hq0 : q ^ c ≠ 0 := pow_ne_zero _ hq.ne_zero
  refine ⟨c, m, hm, hcm, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd hm0 (hcm ▸ dvd_mul_left _ _), hcm, Nat.mul_div_cancel _ (by omega)]
  · rw [orderOf_pow_of_dvd hq0 (hcm ▸ dvd_mul_right _ _), hcm,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hq0)]

theorem mem_centralizer_of_mem_normalizer_of_minFac {R F : Subgroup G} {f : ℕ} [Fact f.Prime]
    (hFR : IsSylowOf f F R) (hFc : IsCyclic F)
    (hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card R → f ≤ q) {y : G} (hyR : y ∈ R)
    (hyN : y ∈ normalizer (F : Set G)) : y ∈ centralizer (F : Set G) := by
  have hf : f.Prime := Fact.out
  obtain ⟨c, m, hm, hcm, hmo, -⟩ := exists_orderOf_pow_eq f hf y
  have hyp : IsPGroup f (zpowers (y ^ m)) := IsPGroup.of_card (by rw [Nat.card_zpowers, hmo])
  have hW : IsPGroup f ↥(zpowers (y ^ m) ⊔ F) :=
    IsPGroup.to_sup_of_normal_right' hyp hFR.isPGroup (zpowers_le.mpr (pow_mem hyN m))
  have hWF := hFR.eq_of_le le_sup_right (sup_le (zpowers_le.mpr (pow_mem hyR m)) hFR.le) hW
  have hymF : y ^ m ∈ F := hWF ▸ (le_sup_left : zpowers (y ^ m) ≤ _) (mem_zpowers _)
  have hymC : y ^ m ∈ centralizer (F : Set G) := mem_centralizer_iff.mpr fun z hz =>
    congrArg Subtype.val (mul_comm' (⟨z, hz⟩ : F) ⟨y ^ m, hymF⟩)
  refine mem_centralizer_of_pow_mem_of_coprime_totient hFc hyN hymC
    (coprime_totient_card_of_isPGroup hf hFR.isPGroup fun q hq hqm => ?_)
  have hqR : q ∣ Nat.card R := hqm.trans ((hcm ▸ dvd_mul_left m _).trans
    (Subgroup.orderOf_dvd_natCard R hyR))
  exact lt_of_le_of_ne (hmin q hq hqR) fun h => hm (h ▸ hqm)

theorem exists_mem_normalizer_not_mem_of_isPGroup {f : ℕ} [Fact f.Prime] {F S : Subgroup G}
    (hFS : F ≤ S) (hne : F ≠ S) (hS : IsPGroup f S) :
    ∃ s ∈ S, s ∈ normalizer (F : Set G) ∧ s ∉ F := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : F.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hFS fun s hs => ?_)
    have : (⟨s, hs⟩ : S) ∈ F.subgroupOf S := h ▸ mem_top _
    exact this
  obtain ⟨s, hs, hsF⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨s, s.2, mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_, fun hh => ?_⟩,
    fun h => hsF (mem_subgroupOf.mpr h)⟩
  · exact mem_subgroupOf.mp ((mem_normalizer_iff.mp hs ⟨h, hFS hh⟩).mp (mem_subgroupOf.mpr hh))
  · have hhS : h ∈ S := by
      have := S.mul_mem (S.mul_mem (S.inv_mem s.2) (hFS hh)) s.2
      simpa [mul_assoc] using this
    exact mem_subgroupOf.mp ((mem_normalizer_iff.mp hs ⟨h, hhS⟩).mpr (mem_subgroupOf.mpr hh))

end Elementary

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem isSylowOf_of_sylow_le_of_le [Fact p.Prime] (Q : Sylow p G) {K : Subgroup G}
    (hQK : (Q : Subgroup G) ≤ K) : IsSylowOf p (Q : Subgroup G) K :=
  isSylowOf_iff.mpr ⟨hQK, Q.isPGroup', fun h =>
    Q.not_dvd_index (h.trans (relIndex_dvd_index_of_le hQK))⟩

omit [Finite G] in
theorem exists_isSylowOf_ge_of_le {Q K : Subgroup G} (hQK : Q ≤ K) (hQ : IsPGroup p Q) :
    ∃ S : Subgroup G, IsSylowOf p S K ∧ Q ≤ S := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun q hq =>
    Subgroup.mem_map.mpr ⟨⟨q, hQK hq⟩, hS hq, rfl⟩⟩

theorem gen5_dichotomy_N (hG : Gen5Global G) (hl : Gen5Local G p P M x) {N : Subgroup G}
    (hUN : gen5U (P : Subgroup G) x ≤ N) :
    IsSylowOf p (gen5U (P : Subgroup G) x) N ∨
      ∃ d ∈ centralizer ((gen5U (P : Subgroup G) x : Subgroup G) : Set G), d * x * d⁻¹ ∈ N := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  set U := gen5U (P : Subgroup G) x
  set Z := centralizer ((gen5L x : Subgroup G) : Set G)
  have hUP : U ≤ P := inf_le_left
  obtain ⟨Q, hQN, hUQ⟩ := exists_isSylowOf_ge_of_le hUN (P.isPGroup'.to_le hUP)
  by_cases hQU : Q = U
  · exact Or.inl (hQU ▸ hQN)
  right
  obtain ⟨q, hqQ, hqU⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hUQ (Ne.symm hQU))
  obtain ⟨-, hPab⟩ := gen5_P_abelian hG hl
  have hQab : IsMulCommutative Q := (gen5_pgroup hG hl hQN.isPGroup).1
  have hPC : (P : Subgroup G) ≤ centralizer (U : Set G) := fun g hg => mem_centralizer_iff.mpr
    fun u hu => congrArg Subtype.val (hPab.is_comm.comm ⟨u, hUP hu⟩ ⟨g, hg⟩)
  have hQC : Q ≤ centralizer (U : Set G) := fun g hg => mem_centralizer_iff.mpr
    fun u hu => congrArg Subtype.val (hQab.is_comm.comm ⟨u, hUQ hu⟩ ⟨g, hg⟩)
  obtain ⟨S, hS, hQS⟩ := exists_isSylowOf_ge_of_le hQC hQN.isPGroup
  obtain ⟨k, hk, hkS⟩ := (isSylowOf_of_sylow_le_of_le P hPC).exists_mem_conj hS
  obtain ⟨hdec, -, -, hgen⟩ := gen5_P_decomp hG hl
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
  have hy1 : (y : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact (Fact.out : p.Prime).one_lt.ne hy
  have hyp : (y : G) ^ p = 1 := hy ▸ pow_orderOf_eq_one _
  have hxz : x ∈ zpowers z :=
    zpowers_le.mpr y.2 (hgen (y : G) (zpowers_le.mpr hz y.2) hy1 hyp ▸ mem_zpowers x)
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hxz
  have hxQ : k * z ^ m * k⁻¹ ∈ Q := by
    rw [← conj_zpow]
    exact Q.zpow_mem hcQ m
  exact ⟨k, hk, hQN.le hxQ⟩

theorem gen5_isCyclic_of_le_Z (hG : Gen5Global G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (Sch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hK : GL83Generic5KFacts)
    (hExcl : NoExcludedSection3 G) (hl : Gen5Local G p P M x) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) {S : Subgroup G}
    (hSZ : S ≤ centralizer ((gen5L x : Subgroup G) : Set G)) (hS : IsPGroup q S) :
    IsCyclic S := by
  have : Fact q.Prime := ⟨hq⟩
  have hp := gen5_prime hl
  by_contra hnc
  have : Fact (IsPGroup q S) := ⟨hS⟩
  obtain ⟨E, -, hEc, hEel⟩ := CFSG.lemma_4_5_a hq2 hnc
  have hEZ : E.map S.subtype ≤ centralizer ((gen5L x : Subgroup G) : Set G) :=
    (map_subtype_le E).trans hSZ
  have hpow : ∀ e : E.map S.subtype, e ^ q = 1 := by
    rintro ⟨_, e, he, rfl⟩
    exact Subtype.ext (by
      simpa using congrArg Subtype.val (CFSG.elemPow_eq_one_of_isElementaryAbelian e he))
  have hcard : Nat.card (E.map S.subtype) = q ^ 2 := by
    rw [card_map_of_injective S.subtype_injective, hEc]
  have hT2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hTq : ¬ q ∣ Nat.card (pCoreOf 2 M) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
    rw [hn]
    exact fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  have hEN : E.map S.subtype ≤ normalizer (pCoreOf 2 M : Set G) :=
    hEZ.trans ((gen5_Z_le hG hl).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane q
    hq _ _ hpow hcard hTq hEN
  have hFPF := gl83GenericFPF_of_kfacts hG gl83Generic5CaseI_holds gl83Generic5CaseII_holds K1 Sch
      hK hExcl
  refine pCoreOf_two_ne_bot hl.core.1.1 ?_
  rw [hgen]
  refine iSup_eq_bot.mpr fun e => iSup_eq_bot.mpr fun he1 => eq_bot_iff.mpr fun k hk => ?_
  have he1' : (e : G) ≠ 1 := fun h => he1 (Subtype.ext h)
  have heq : orderOf (e : G) ∣ q := orderOf_dvd_of_pow_eq_one (by
    simpa using congrArg Subtype.val (hpow e))
  have hodd : Odd (orderOf (e : G)) :=
    Odd.of_dvd_nat (hq.eq_two_or_odd'.resolve_left hq2) heq
  have hcop : Nat.Coprime p (orderOf (e : G)) :=
    Nat.Coprime.coprime_dvd_right heq ((Nat.coprime_primes hp hq).mpr (Ne.symm hqp))
  exact mem_bot.mpr (hFPF p hl.sigma P M hl.core hl.fail hl.larger x hl.generic e (hEZ e.2) he1'
    hodd hcop k hk.1 (mem_centralizer_singleton_iff.mp hk.2))

end CFSG.LocalAnalysis.RankThreeTheoremC
