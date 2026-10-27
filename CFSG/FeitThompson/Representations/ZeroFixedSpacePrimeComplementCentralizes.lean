module

public import CFSG.FeitThompson.Local.FixedFreeComplementKernelActsTrivially
public import CFSG.FeitThompson.Local.InvariantHallPiSubgroupExtension
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
public import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
public import CFSG.FeitThompson.Foundations.PolynomialRootCountDegree
public import CFSG.FeitThompson.Representations.MinimalActionPrimeGroupElementary
public import CFSG.FeitThompson.Representations.ExtraspecialOddCentreFixedVector
public import CFSG.FeitThompson.Representations.SchurLemmaAlgebraicallyClosed
import CFSG.FeitThompson.Local.PrimeOrderFixedFreeKernelCoprime
import CFSG.FeitThompson.Local.FittingModuleFaithfulAction

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise Subgroup

section GroupTheory

variable {G : Type*} [Group G] {K R : Subgroup G}

theorem natCard_eq_pow_factorization_of_isComplement' [Finite G] {r : ℕ} (hr : r.Prime)
    (hKR : K.IsComplement' R) (hR : Nat.card R = r) (hK : ¬ r ∣ Nat.card K) :
    Nat.card R = r ^ (Nat.card G).factorization r := by
  have hG : Nat.card G = Nat.card K * r := by rw [← hR, hKR.card_mul_card]
  have hfac : (Nat.card G).factorization r = 1 := by
    rw [hG, Nat.factorization_mul Nat.card_pos.ne' hr.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hK, hr.factorization_self]
  rw [hR, hfac, pow_one]

theorem not_dvd_natCard_of_inf_eq_bot [Finite G] {r : ℕ} {N : Subgroup G} [N.Normal]
    (hr : r.Prime) (hKR : K.IsComplement' R) (hR : Nat.card R = r) (hK : ¬ r ∣ Nat.card K)
    (hNR : N ⊓ R = ⊥) (hR1 : R ≠ ⊥) : ¬ r ∣ Nat.card N := by
  have := Fact.mk hr
  intro hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) r hdvd
  set S : Subgroup G := Subgroup.zpowers ((y : G)) with hS
  have hycard : orderOf (y : G) = r := by rw [Subgroup.orderOf_coe, hy]
  have hScard : Nat.card S = r := by rw [hS, Nat.card_zpowers, hycard]
  have hSN : S ≤ N := by rw [hS, Subgroup.zpowers_le]; exact y.2
  have hSp : IsPGroup r S := IsPGroup.of_card (n := 1) (by rw [hScard, pow_one])
  obtain ⟨g, hg⟩ := exists_le_conj_smul_of_isPGroup
    (natCard_eq_pow_factorization_of_isComplement' hr hKR hR hK) hSp
  have hcard : Nat.card (MulAut.conj g • R : Subgroup G) = r := by rw [natCard_conj_smul, hR]
  have heq : S = (MulAut.conj g • R : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hg (by rw [hcard, hScard])
  have hRle : R ≤ N := by
    intro z hz
    have hmem : (MulAut.conj g) z ∈ (MulAut.conj g • R : Subgroup G) :=
      Subgroup.smul_mem_pointwise_smul z _ R hz
    have hconj : g * z * g⁻¹ ∈ N := hSN (heq ▸ hmem)
    simpa [mul_assoc] using ‹N.Normal›.conj_mem _ hconj g⁻¹
  exact hR1 (le_bot_iff.1 (hNR ▸ le_inf hRle le_rfl))

theorem le_of_not_dvd_natCard [Finite G] {r : ℕ} {N : Subgroup G} [K.Normal]
    (hr : r.Prime) (hKR : K.IsComplement' R) (hR : Nat.card R = r)
    (hN : ¬ r ∣ Nat.card N) : N ≤ K := by
  have hmap : Nat.card (N.map (QuotientGroup.mk' K)) ∣ Nat.card N := Subgroup.card_map_dvd _ _
  have hmap2 : Nat.card (N.map (QuotientGroup.mk' K)) ∣ Nat.card (G ⧸ K) :=
    Subgroup.card_subgroup_dvd_card _
  have hcardQ : Nat.card (G ⧸ K) = r := by
    rw [← Subgroup.index_eq_card, hKR.symm.index_eq_card, hR]
  have hone : Nat.card (N.map (QuotientGroup.mk' K)) = 1 := by
    rw [hcardQ] at hmap2
    rcases hr.eq_one_or_self_of_dvd _ hmap2 with h | h
    · exact h
    · exact absurd (h ▸ hmap) hN
  intro z hz
  have hz' : QuotientGroup.mk' K z ∈ N.map (QuotientGroup.mk' K) := ⟨z, hz, rfl⟩
  rw [Nat.card_eq_one_iff_unique] at hone
  have h2 : QuotientGroup.mk' K z = 1 :=
    congrArg Subtype.val (hone.1.elim (⟨_, hz'⟩ : N.map (QuotientGroup.mk' K)) 1)
  rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h2

theorem exists_isHallSubgroup_singleton_le_normalizer [Finite G] [Group.IsSolvable G] [K.Normal]
    (hKR : K ⊔ R = ⊤) (hcop : (Nat.card K).Coprime (Nat.card R)) (q : ℕ) :
    ∃ H : Subgroup G, H ≤ K ∧ IsHallSubgroup {q} (H.subgroupOf K) ∧
      R ≤ normalizer (H : Set G) := by
  obtain ⟨H, hHK, hHall, -, hRH⟩ := exists_isHallSubgroup_subgroupOf_ge_le_normalizer hKR hcop {q}
    (R := ⊥) bot_le (by simp [isPiNumber_one]) (fun g _ => by
      rw [Subgroup.mem_normalizer_iff]; simp)
  exact ⟨H, hHK, hHall, hRH⟩

theorem eq_of_le_of_forall_pow_factorization_dvd [Finite G] {S : Subgroup G} (hSK : S ≤ K)
    (h : ∀ q : ℕ, q.Prime → q ^ (Nat.card K).factorization q ∣ Nat.card S) : S = K := by
  refine Subgroup.eq_of_le_of_card_ge hSK (Nat.le_of_dvd Nat.card_pos ?_)
  rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne']
  intro q
  rcases Nat.eq_zero_or_pos ((Nat.card K).factorization q) with h0 | hpos
  · simp [h0]
  · have hq : q.Prime := Nat.prime_of_mem_primeFactors
      (Nat.support_factorization (Nat.card K) ▸ Finsupp.mem_support_iff.2 hpos.ne')
    exact (Nat.Prime.pow_dvd_iff_le_factorization hq Nat.card_pos.ne').1 (h q hq)

private theorem primeFactors_pow_subset {q a : ℕ} (hq : q.Prime) :
    (q ^ a).primeFactors ⊆ {q} := by
  intro p hp
  have h1 := Nat.prime_of_mem_primeFactors hp
  simp [(Nat.prime_dvd_prime_iff_eq h1 hq).1 (h1.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hp))]

theorem commutator_eq_bot_of_one_lt_card_primeFactors [Finite G] [Group.IsSolvable G] [K.Normal]
    (hKR : K ⊔ R = ⊤) (hcop : (Nat.card K).Coprime (Nat.card R))
    (hK2 : 1 < (Nat.card K).primeFactors.card)
    (hcent : ∀ L : Subgroup G, L ≤ K → L ≠ K → R ≤ normalizer (L : Set G) →
      L ≤ centralizer (R : Set G)) :
    (⁅K, R⁆ : Subgroup G) = ⊥ := by
  classical
  choose H hHK hHall hRH using
    exists_isHallSubgroup_singleton_le_normalizer (K := K) (R := R) hKR hcop
  have hproper : ∀ q : ℕ, q.Prime → H q ≠ K := by
    intro q hq hEq
    have hcardK : Nat.card K = q ^ (Nat.card K).factorization q := by
      have h := natCard_eq_pow_factorization_of_isHallSubgroup_singleton (N := K) hq (hHK q)
        (hHall q)
      rwa [hEq] at h
    have hsub : (Nat.card K).primeFactors ⊆ {q} := hcardK ▸ primeFactors_pow_subset hq
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    omega
  have hSeq : (⨆ q : ℕ, H q) = K := by
    refine eq_of_le_of_forall_pow_factorization_dvd (iSup_le hHK) fun q hq => ?_
    rw [← natCard_eq_pow_factorization_of_isHallSubgroup_singleton (N := K) hq (hHK q) (hHall q)]
    exact Subgroup.card_dvd_of_le (le_iSup H q)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← hSeq]
  refine iSup_le fun q => ?_
  by_cases hq : q.Prime
  · exact hcent (H q) (hHK q) (hproper q hq) (hRH q)
  ·
    have hp : IsPiNumber {q} (Nat.card (H q)) := by
      have h := (hHall q).natCard
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hHK q)).toEquiv] at h
    have hone : Nat.card (H q) = 1 := by
      by_contra hc
      obtain ⟨p, hpprime, hpdvd⟩ := (Nat.card (H q)).exists_prime_and_dvd hc
      have hmem := isPiNumber_iff.1 hp p
        (Nat.mem_primeFactors.2 ⟨hpprime, hpdvd, Nat.card_pos.ne'⟩)
      simp only [Set.mem_singleton_iff] at hmem
      exact hq (hmem ▸ hpprime)
    rw [Subgroup.card_eq_one.1 hone]
    exact bot_le

theorem isComplement'_subgroupOf_sup_of_le_normalizer {L : Subgroup G} (hLR : L ⊓ R = ⊥)
    (hR : R ≤ normalizer (L : Set G)) :
    (L.subgroupOf (L ⊔ R)).IsComplement' (R.subgroupOf (L ⊔ R)) := by
  have hnorm : (L.subgroupOf (L ⊔ R)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le le_normalizer (by simpa using hR))
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff]
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    refine ⟨fun h => ?_, fun h => by rw [h]; simp⟩
    have hy : (y : G) ∈ L ⊓ R := ⟨h.1, h.2⟩
    rw [hLR, Subgroup.mem_bot] at hy
    exact Subtype.ext hy
  · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self]
    rfl

theorem isComplement'_map_mk {N : Subgroup G} [K.Normal] [N.Normal] (hKR : K.IsComplement' R)
    (hNK : N ≤ K) :
    (K.map (QuotientGroup.mk' N)).IsComplement' (R.map (QuotientGroup.mk' N)) := by
  have hcm : (K.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = K :=
    Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff, eq_bot_iff]
    rintro y ⟨hy1, a, ha, rfl⟩
    have haK : a ∈ K := by rw [← hcm, Subgroup.mem_comap]; exact hy1
    have hmem : a ∈ K ⊓ R := ⟨haK, ha⟩
    rw [disjoint_iff.1 hKR.disjoint, Subgroup.mem_bot] at hmem
    simp [hmem]
  · rw [← Subgroup.normal_mul, ← Subgroup.map_sup, hKR.sup_eq_top,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    rfl

theorem natCard_map_mk_of_inf_eq_bot {N : Subgroup G} [N.Normal] (h : N ⊓ R = ⊥) :
    Nat.card (R.map (QuotientGroup.mk' N)) = Nat.card R := by
  have hker : ((QuotientGroup.mk' N).comp R.subtype).ker = ⊥ := by
    ext y
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_bot]
    refine ⟨fun hy => ?_, fun hy => by rw [hy]; simp⟩
    have hmem : (y : G) ∈ N ⊓ R := ⟨hy, y.2⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp R.subtype) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker
  have hrange : ((QuotientGroup.mk' N).comp R.subtype).range = R.map (QuotientGroup.mk' N) := by
    ext y; simp [MonoidHom.mem_range, Subgroup.mem_map]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem natCard_quotient_le [Finite G] {n : ℕ} {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥)
    (hn : Nat.card G ≤ n + 1) : Nat.card (G ⧸ N) ≤ n := by
  have hcard : Nat.card (G ⧸ N) * Nat.card N = Nat.card G :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
  have hN1 : 1 < Nat.card ↥N := by
    have hpos := Nat.card_pos (α := ↥N)
    rcases Nat.lt_or_ge 1 (Nat.card ↥N) with h | h
    · exact h
    · exact absurd (Subgroup.card_eq_one.1 (by omega)) hN
  have hq : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  nlinarith [hcard, hn]

theorem natCard_lt_of_le_of_ne [Finite G] {L : Subgroup G} (h : L ≤ K) (hne : L ≠ K) :
    Nat.card ↥L < Nat.card ↥K := by
  rcases Nat.lt_or_ge (Nat.card ↥L) (Nat.card ↥K) with h1 | h1
  · exact h1
  · exact absurd (Subgroup.eq_of_le_of_card_ge h h1) hne

theorem exists_orderOf_eq_zpowers_eq_top {A : Type*} [Group A] [Finite A] {r : ℕ}
    (hr : Nat.card A = r) (hrp : r.Prime) :
    ∃ h : A, orderOf h = r ∧ Subgroup.zpowers h = ⊤ := by
  have := Fact.mk hrp
  have hnt : Nontrivial A := Finite.one_lt_card_iff_nontrivial.1 (by rw [hr]; exact hrp.one_lt)
  obtain ⟨g, hg⟩ := exists_ne (1 : A)
  have h1 : Subgroup.zpowers g = ⊤ := zpowers_eq_top_of_prime_card hr hg
  refine ⟨g, ?_, h1⟩
  have h2 : Nat.card (Subgroup.zpowers g) = Nat.card A := by rw [h1]; simp
  rw [Nat.card_zpowers] at h2
  rw [h2, hr]

theorem exists_prime_pow_of_primeFactors_card_le_one {m : ℕ} (hm : m ≠ 0) (hm1 : m ≠ 1)
    (h : ¬ 1 < m.primeFactors.card) : ∃ q : ℕ, q.Prime ∧ ∃ j, 1 ≤ j ∧ m = q ^ j := by
  obtain ⟨q, hq, hqd⟩ := m.exists_prime_and_dvd hm1
  refine ⟨q, hq, ?_⟩
  have hmem : q ∈ m.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqd, hm⟩
  have hsub : m.primeFactors = {q} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨hmem, fun p hp => ?_⟩
    by_contra hne
    have hss : ({q, p} : Finset ℕ) ⊆ m.primeFactors := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have hc := Finset.card_le_card hss
    rw [Finset.card_insert_of_notMem (by simpa using Ne.symm hne), Finset.card_singleton] at hc
    omega
  have h2 : ∀ {d : ℕ}, d.Prime → d ∣ m → d = q := by
    intro d hd hdm
    have hd2 : d ∈ m.primeFactors := Nat.mem_primeFactors.2 ⟨hd, hdm, hm⟩
    rw [hsub] at hd2
    simpa using hd2
  have heq := Nat.eq_prime_pow_of_unique_prime_dvd hm h2
  refine ⟨_, ?_, heq⟩
  rcases Nat.eq_zero_or_pos m.primeFactorsList.length with h0 | hp
  · rw [h0, pow_zero] at heq; omega
  · exact hp

section ConjAction

abbrev conjAction (hRn : R ≤ normalizer (K : Set G)) : ↥R →* MulAut ↥K :=
  K.normalizerMonoidHom.comp (Subgroup.inclusion hRn)

theorem coe_conjAction_apply (hRn : R ≤ normalizer (K : Set G)) (b : ↥R) (y : ↥K) :
    ((conjAction hRn b y : ↥K) : G) = (b : G) * (y : G) * (b : G)⁻¹ := rfl

variable (hRn : R ≤ normalizer (K : Set G))

theorem actionCommutator_conjAction_top_eq_bot_iff :
    actionCommutator (conjAction hRn) (⊤ : Subgroup ↥R) = ⊥ ↔ (⁅K, R⁆ : Subgroup G) = ⊥ := by
  rw [actionCommutator_eq_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine ⟨fun h a ha => ?_, fun h b _ => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h3 : (b : G) * a * (b : G)⁻¹ = a := by
      rw [← coe_conjAction_apply hRn ⟨b, hb⟩ ⟨a, ha⟩, h ⟨b, hb⟩ (Subgroup.mem_top _)]; rfl
    calc b * a = ((b : G) * a * (b : G)⁻¹) * b := by group
      _ = a * b := by rw [h3]
  · ext y
    have hc : (b : G) * (y : G) = (y : G) * (b : G) :=
      Subgroup.mem_centralizer_iff.1 (h y.2) (b : G) b.2
    have hval : ((conjAction hRn b y : ↥K) : G) = (y : G) := by
      rw [coe_conjAction_apply, hc]; group
    change ((conjAction hRn b y : ↥K) : G) = _
    rw [hval]; rfl

theorem inf_centralizer_eq_bot_of_actionCentralizer_eq_bot
    (h : actionCentralizer (conjAction hRn) (⊤ : Subgroup ↥R) = ⊥) :
    K ⊓ centralizer (R : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzK, hzC⟩ : z ∈ K ∧ z ∈ centralizer (R : Set G) := hz
  have hmem : (⟨z, hzK⟩ : ↥K) ∈ actionCentralizer (conjAction hRn) (⊤ : Subgroup ↥R) := by
    rw [mem_actionCentralizer]
    exact fun d _ => Subtype.ext (by
      rw [coe_conjAction_apply, Subgroup.mem_centralizer_iff.1 hzC (d : G) d.2]; group)
  rw [h, Subgroup.mem_bot] at hmem
  simpa [Subgroup.mem_bot] using congrArg Subtype.val hmem

theorem forall_conjAction_apply_eq_of_ne_top
    (hcent : ∀ L : Subgroup G, L ≤ K → L ≠ K → R ≤ normalizer (L : Set G) →
      L ≤ centralizer (R : Set G)) :
    ∀ H : Subgroup ↥K, IsInvariantSubgroup (conjAction hRn) H → H ≠ ⊤ →
      ∀ d ∈ (⊤ : Subgroup ↥R), ∀ y ∈ H, conjAction hRn d y = y := by
  intro H hHinv hHtop d _ y hy
  have hmemL : ∀ z : G, z ∈ H.map K.subtype ↔ ∃ w : ↥K, w ∈ H ∧ (w : G) = z := by
    intro z; simp only [Subgroup.mem_map, Subgroup.coe_subtype]
  have hLK : H.map K.subtype ≤ K := Subgroup.map_subtype_le H
  have hLne : H.map K.subtype ≠ K := by
    intro hc
    refine hHtop (eq_top_iff.2 fun z _ => ?_)
    have hz : (z : G) ∈ H.map K.subtype := by rw [hc]; exact z.2
    obtain ⟨w, hw, hwz⟩ := (hmemL (z : G)).1 hz
    exact (Subtype.ext hwz : w = z) ▸ hw
  have hLnorm : R ≤ normalizer ((H.map K.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb z hz
    obtain ⟨w, hw, rfl⟩ := (hmemL z).1 hz
    exact (hmemL _).2 ⟨conjAction hRn ⟨b, hb⟩ w, hHinv.apply_mem ⟨b, hb⟩ hw,
      coe_conjAction_apply hRn _ _⟩
  have hcomm : (d : G) * (y : G) = (y : G) * (d : G) :=
    Subgroup.mem_centralizer_iff.1 (hcent _ hLK hLne hLnorm ((hmemL (y : G)).2 ⟨y, hy, rfl⟩))
      (d : G) d.2
  exact Subtype.ext (by rw [coe_conjAction_apply, hcomm]; group)

theorem actionCentralizer_le_frattini [Finite G]
    (h : actionCentralizer (frattiniQuotientAction (conjAction hRn)) (⊤ : Subgroup ↥R) = ⊥) :
    actionCentralizer (conjAction hRn) (⊤ : Subgroup ↥R) ≤ frattini ↥K := by
  intro y hy
  rw [mem_actionCentralizer] at hy
  have hmem : (QuotientGroup.mk y : ↥K ⧸ frattini ↥K)
      ∈ actionCentralizer (frattiniQuotientAction (conjAction hRn)) (⊤ : Subgroup ↥R) := by
    rw [mem_actionCentralizer]
    intro d hd
    rw [frattiniQuotientAction_mk, hy d hd]
  rw [h, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  exact hmem

theorem eq_one_of_forall_centerQuotAut_eq [Finite G]
    (hZΦ : Subgroup.center ↥K = frattini ↥K)
    (h : actionCentralizer (frattiniQuotientAction (conjAction hRn)) (⊤ : Subgroup ↥R) = ⊥) :
    ∀ y : ↥K ⧸ Subgroup.center ↥K,
      (∀ a : ↥R, centerQuotAut (conjAction hRn) a y = y) → y = 1 := by
  intro y hy
  induction y using QuotientGroup.induction_on with
  | H z =>
    have hmem : (QuotientGroup.mk z : ↥K ⧸ frattini ↥K)
        ∈ actionCentralizer (frattiniQuotientAction (conjAction hRn)) (⊤ : Subgroup ↥R) := by
      rw [mem_actionCentralizer]
      intro d _
      rw [frattiniQuotientAction_mk, QuotientGroup.eq]
      have h1 := hy d
      rw [centerQuotAut_mk, QuotientGroup.eq, hZΦ] at h1
      exact h1
    rw [h, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    rw [QuotientGroup.eq_one_iff, hZΦ]
    exact hmem

variable [K.Normal]

theorem map_center_le_center (hKR : K.IsComplement' R)
    (hcent : ∀ d : ↥R, ∀ y ∈ Subgroup.center ↥K, conjAction hRn d y = y) :
    (Subgroup.center ↥K).map K.subtype ≤ Subgroup.center G := by
  rintro z ⟨w, hw, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ ((K : Set G) * (R : Set G)) := by
    rw [← Subgroup.normal_mul, hKR.sup_eq_top]; trivial
  obtain ⟨y, hy, b, hb, rfl⟩ := hg
  have h1 : y * (w : G) = (w : G) * y := by
    simpa using congrArg (Subtype.val) (Subgroup.mem_center_iff.1 hw ⟨y, hy⟩)
  have h2 : b * (w : G) * b⁻¹ = (w : G) := by
    rw [← coe_conjAction_apply hRn ⟨b, hb⟩ w, hcent ⟨b, hb⟩ w hw]
  have h3 : b * (w : G) = (w : G) * b := by
    calc b * (w : G) = (b * (w : G) * b⁻¹) * b := by group
      _ = (w : G) * b := by rw [h2]
  simp only [Subgroup.coe_subtype]
  calc (y * b) * (w : G) = y * (b * (w : G)) := by group
    _ = y * ((w : G) * b) := by rw [h3]
    _ = (y * (w : G)) * b := by group
    _ = ((w : G) * y) * b := by rw [h1]
    _ = (w : G) * (y * b) := by group

end ConjAction

end GroupTheory

section Stabilizer

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

def repStabilizer (ρ : Representation k G V) (S : Submodule k V) : Subgroup G where
  carrier := {g : G | ∀ v ∈ S, ρ g v = v}
  one_mem' := by intro v _; simp
  mul_mem' := by
    intro a b ha hb v hv
    rw [map_mul, Module.End.mul_apply, hb v hv, ha v hv]
  inv_mem' := by
    intro a ha v hv
    have h : ρ a⁻¹ (ρ a v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha v hv] at h

theorem mem_repStabilizer {ρ : Representation k G V} {S : Submodule k V} {g : G} :
    g ∈ repStabilizer ρ S ↔ ∀ v ∈ S, ρ g v = v := Iff.rfl

theorem repStabilizer_normal (ρ : Representation k G V) {S : Submodule k V}
    (hS : ∀ g : G, ∀ v ∈ S, ρ g v ∈ S) : (repStabilizer ρ S).Normal := by
  constructor
  intro n hn g v hv
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    mem_repStabilizer.1 hn _ (hS g⁻¹ v hv), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, Module.End.one_apply]

theorem repStabilizer_top (ρ : Representation k G V) :
    repStabilizer ρ ⊤ = MonoidHom.ker ρ := by
  ext g
  rw [mem_repStabilizer, MonoidHom.mem_ker]
  exact ⟨fun h => LinearMap.ext fun v => by simpa using h v Submodule.mem_top,
    fun h v _ => by rw [h]; simp⟩

theorem invariants_subrepresentation_comp_subtype_eq_bot (ρ : Representation k G V)
    {S : Submodule k V} (hS : ∀ g : G, S ≤ S.comap (ρ g)) {R : Subgroup G}
    (hCV : Representation.invariants (ρ.comp R.subtype) = ⊥) :
    Representation.invariants ((ρ.subrepresentation S hS).comp R.subtype) = ⊥ := by
  refine le_antisymm (fun w hw => ?_) bot_le
  rw [Representation.mem_invariants] at hw
  have hw' : (w : V) ∈ Representation.invariants (ρ.comp R.subtype) := by
    refine (Representation.mem_invariants _ _).2 fun a => ?_
    have h := congrArg (fun y : ↥S => (y : V)) (hw a)
    simpa [Representation.subrepresentation_apply, LinearMap.coe_restrict_apply] using h
  rw [hCV, Submodule.mem_bot] at hw'
  simpa [Submodule.mem_bot] using Subtype.ext hw'

theorem mem_repStabilizer_iff_subrepresentation_eq_one (ρ : Representation k G V)
    {S : Submodule k V} (hS : ∀ g : G, S ≤ S.comap (ρ g)) (g : G) :
    g ∈ repStabilizer ρ S ↔ (ρ.subrepresentation S hS) g = 1 := by
  rw [mem_repStabilizer]
  refine ⟨fun h => LinearMap.ext fun w => Subtype.ext ?_, fun h w hw => ?_⟩
  · simpa [Representation.subrepresentation_apply, LinearMap.coe_restrict_apply]
      using h (w : V) w.2
  · have h2 := congrArg (fun T : Module.End k ↥S => ((T ⟨w, hw⟩ : ↥S) : V)) h
    simpa [Representation.subrepresentation_apply, LinearMap.coe_restrict_apply] using h2

instance isTrivial_comp_ker_subtype (ρ : Representation k G V) :
    Representation.IsTrivial (ρ.comp (MonoidHom.ker ρ).subtype) :=
  ⟨fun g => by
    have h := MonoidHom.mem_ker.mp g.2
    change ρ (g : G) = LinearMap.id
    rw [h]; rfl⟩

def quotKerRep (ρ : Representation k G V) : Representation k (G ⧸ MonoidHom.ker ρ) V :=
  Representation.ofQuotient ρ (MonoidHom.ker ρ)

@[simp]
theorem quotKerRep_mk (ρ : Representation k G V) (g : G) :
    quotKerRep ρ (QuotientGroup.mk g) = ρ g :=
  LinearMap.ext fun x => Representation.ofQuotient_coe_apply ρ _ g x

theorem quotKerRep_injective (ρ : Representation k G V) : Function.Injective (quotKerRep ρ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker, quotKerRep_mk] at hy
    exact hy

theorem invariants_quotKerRep_comp_subtype (ρ : Representation k G V) {R : Subgroup G} :
    Representation.invariants
        ((quotKerRep ρ).comp (R.map (QuotientGroup.mk' (MonoidHom.ker ρ))).subtype)
      = Representation.invariants (ρ.comp R.subtype) := by
  ext w
  simp only [Representation.mem_invariants, MonoidHom.comp_apply, Subgroup.coe_subtype]
  refine ⟨fun h a => ?_, fun h y => ?_⟩
  · have hmem : (QuotientGroup.mk' (MonoidHom.ker ρ)) (a : G)
        ∈ R.map (QuotientGroup.mk' (MonoidHom.ker ρ)) := ⟨a, a.2, rfl⟩
    simpa [QuotientGroup.mk'_apply] using h ⟨_, hmem⟩
  · obtain ⟨a, ha, hy⟩ := y.2
    rw [show (y : G ⧸ MonoidHom.ker ρ) = QuotientGroup.mk a from hy.symm, quotKerRep_mk]
    exact h ⟨a, ha⟩

theorem invariants_comp_subtype_subgroupOf (ρ : Representation k G V) {R U : Subgroup G}
    (hRU : R ≤ U) :
    Representation.invariants ((ρ.comp U.subtype).comp (R.subgroupOf U).subtype)
      = Representation.invariants (ρ.comp R.subtype) := by
  ext w
  simp only [Representation.mem_invariants, MonoidHom.comp_apply, Subgroup.coe_subtype]
  exact ⟨fun h a => h ⟨⟨(a : G), hRU a.2⟩, Subgroup.mem_subgroupOf.2 a.2⟩,
    fun h y => h ⟨_, Subgroup.mem_subgroupOf.1 y.2⟩⟩

theorem inf_ker_eq_bot_of_invariants_eq_bot [Finite G] [Nontrivial V] {R : Subgroup G}
    (hr : (Nat.card R).Prime) (ρ : Representation k G V)
    (hCV : Representation.invariants (ρ.comp R.subtype) = ⊥) :
    MonoidHom.ker ρ ⊓ R = ⊥ := by
  have := Fact.mk hr
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨ha1, ha2⟩ : a ∈ MonoidHom.ker ρ ∧ a ∈ R := ha
  rw [Subgroup.mem_bot]
  by_contra hne
  have hgen : ∀ b : ↥R, b ∈ Submonoid.powers (⟨a, ha2⟩ : ↥R) := fun b => by
    rw [powers_eq_top_of_prime_card (G := ↥R) rfl (g := (⟨a, ha2⟩ : ↥R))
      (by simpa [Subtype.ext_iff] using hne)]
    exact Submonoid.mem_top b
  rw [MonoidHom.mem_ker] at ha1
  have hall : ∀ b : ↥R, ρ (b : G) = 1 := by
    intro b
    obtain ⟨m, hm⟩ := hgen b
    have hb : (b : G) = a ^ m := by rw [← hm]; push_cast; rfl
    rw [hb, map_pow, ha1, one_pow]
  obtain ⟨w, hw⟩ := exists_ne (0 : V)
  have hmem : w ∈ Representation.invariants (ρ.comp R.subtype) := by
    refine (Representation.mem_invariants _ _).2 fun b => ?_
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [hall b]; simp
  rw [hCV, Submodule.mem_bot] at hmem
  exact hw hmem

end Stabilizer

section CentralScalars

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

theorem natCard_le_of_le_center_of_injective [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k G V) [ρ.IsIrreducible] (hinj : Function.Injective ρ) {Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) {q : ℕ} (hq : 0 < q) (hexp : ∀ z ∈ Z, z ^ q = 1) :
    Nat.card Z ≤ q := by
  classical
  have hscal : ∀ z : ↥Z, ∃ c : k, ρ (z : G) = c • (1 : Module.End k V) := by
    intro z
    refine Representation.IsIrreducible.exists_eq_smul_one_of_commute ρ _ fun g => ?_
    have hcz : g * (z : G) = (z : G) * g := Subgroup.mem_center_iff.1 (hZ z.2) g
    change ρ (z : G) * ρ g = ρ g * ρ (z : G)
    rw [← map_mul, ← map_mul, hcz]
  choose c hc using hscal
  have hcinj : Function.Injective c := fun a b hab =>
    Subtype.ext (hinj (by rw [hc a, hc b, hab]))
  have hroot : ∀ z : ↥Z, (c z) ^ q = 1 := by
    intro z
    have h1 : ρ ((z : G) ^ q) = 1 := by rw [hexp (z : G) z.2, map_one]
    rw [map_pow, hc z, smul_pow, one_pow] at h1
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    have h2 : ((c z) ^ q) • w = (1 : k) • w := by
      have := congrArg (fun T : Module.End k V => T w) h1
      simpa using this
    exact smul_left_injective k hw h2
  have hpoly : (Polynomial.X ^ q - Polynomial.C (1 : k)) ≠ 0 := fun h => by
    have hd := Polynomial.natDegree_X_pow_sub_C (R := k) (n := q) (r := 1)
    rw [h] at hd
    simp only [Polynomial.natDegree_zero] at hd
    omega
  have hle := ncard_le_natDegree_of_forall_eval_eq_zero hpoly
    (s := Set.range c) (by rintro a ⟨z, rfl⟩; simp [hroot z])
  rwa [Set.ncard_range_of_injective hcinj, Polynomial.natDegree_X_pow_sub_C] at hle

end CentralScalars

section SemidirectTransport

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable {K R : Subgroup G} [K.Normal]

noncomputable def semidirectRep (hRn : R ≤ normalizer (K : Set G)) (hKR : K.IsComplement' R)
    (ρ : Representation k G V) : Representation k (↥K ⋊[conjAction hRn] ↥R) V :=
  ρ.comp (SemidirectProduct.mulEquivSubgroup hKR).toMonoidHom

variable (hRn : R ≤ normalizer (K : Set G)) (hKR : K.IsComplement' R) (ρ : Representation k G V)

theorem semidirectRep_apply (z : ↥K ⋊[conjAction hRn] ↥R) :
    semidirectRep hRn hKR ρ z = ρ ((z.left : G) * (z.right : G)) :=
  congrArg ρ (SemidirectProduct.mulEquivSubgroup_apply hKR z)

@[simp]
theorem resInr_semidirectRep (b : ↥R) : resInr (semidirectRep hRn hKR ρ) b = ρ (b : G) := by
  rw [resInr_apply, semidirectRep_apply]; simp

@[simp]
theorem resInl_semidirectRep (y : ↥K) : resInl (semidirectRep hRn hKR ρ) y = ρ (y : G) := by
  rw [resInl_apply, semidirectRep_apply]; simp

theorem semidirectRep_eq_one_iff (hinj : Function.Injective ρ)
    {z : ↥K ⋊[conjAction hRn] ↥R} : semidirectRep hRn hKR ρ z = 1 ↔ z = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_one]⟩
  have h2 : (SemidirectProduct.mulEquivSubgroup hKR) z
      = (SemidirectProduct.mulEquivSubgroup hKR) 1 := by
    rw [map_one]; exact hinj (h.trans (map_one ρ).symm)
  exact (SemidirectProduct.mulEquivSubgroup hKR).injective h2

theorem invariants_resInr_semidirectRep :
    Representation.invariants (resInr (semidirectRep hRn hKR ρ))
      = Representation.invariants (ρ.comp R.subtype) := by
  ext w
  simp only [Representation.mem_invariants, MonoidHom.comp_apply, Subgroup.coe_subtype]
  exact forall_congr' fun b => by rw [resInr_semidirectRep]

end SemidirectTransport

section Summand

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

private def repFixedBy (ρ : Representation k G V) (x : G) : Submodule k V :=
  LinearMap.eqLocus (ρ x) 1

private theorem mem_repFixedBy {ρ : Representation k G V} {x : G} {v : V} :
    v ∈ repFixedBy ρ x ↔ ρ x v = v := by
  simp [repFixedBy, LinearMap.mem_eqLocus]

theorem exists_minimal_invariant_apply_ne [Finite G] [FiniteDimensional k V]
    (hk : (Nat.card G : k) ≠ 0) (ρ : Representation k G V) {x : G} (hx : ρ x ≠ 1) :
    ∃ S : Submodule k V, S ≠ ⊥ ∧ (∀ g : G, ∀ v ∈ S, ρ g v ∈ S) ∧
      (∀ T : Submodule k V, T ≤ S → (∀ g : G, ∀ v ∈ T, ρ g v ∈ T) → T = ⊥ ∨ T = S) ∧
      ∃ v ∈ S, ρ x v ≠ v := by
  classical
  set 𝒮 : Set (Submodule k V) :=
    {S | (∀ g : G, ∀ v ∈ S, ρ g v ∈ S) ∧ ∀ v ∈ S, ρ x v = v} with h𝒮
  set W : Submodule k V := sSup 𝒮 with hW
  have hWinv : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W := by
    intro g v hv
    have hle : W ≤ W.comap (ρ g) :=
      sSup_le fun S hS w hw => Submodule.mem_comap.2 (le_sSup hS (hS.1 g w hw))
    exact hle hv
  have hWfix : ∀ v ∈ W, ρ x v = v := by
    intro v hv
    have hle : W ≤ repFixedBy ρ x := sSup_le fun S hS w hw => mem_repFixedBy.2 (hS.2 w hw)
    exact mem_repFixedBy.1 (hle hv)
  have hWtop : W ≠ ⊤ := by
    intro h
    refine hx (LinearMap.ext fun v => ?_)
    simpa using hWfix v (h ▸ Submodule.mem_top)
  obtain ⟨U, hUinv, hcompl⟩ := exists_invariant_isCompl_of_natCard_ne_zero hk ρ W hWinv
  have hU0 : U ≠ ⊥ := fun h => hWtop (by simpa [h] using hcompl.sup_eq_top)
  obtain ⟨S, hS0, hSU, hSinv, hSmin⟩ := exists_minimal_invariant_le ρ hUinv hU0
  refine ⟨S, hS0, hSinv, hSmin, ?_⟩
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  have hSW : S ≤ W := le_sSup ⟨hSinv, fun v hv => hc v hv⟩
  have hbot : W ⊓ U = ⊥ := disjoint_iff.1 hcompl.disjoint
  exact hS0 (le_bot_iff.1 (hbot ▸ le_inf hSW hSU))

end Summand

section Frobenius

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable {K R : Subgroup G}

theorem eq_one_of_mem_of_inf_centralizer_eq_bot [Finite G]
    (hK : K.Normal) (hKR : K.IsComplement' R) (hr : (Nat.card R).Prime)
    (hCK : K ⊓ centralizer (R : Set G) = ⊥)
    (hk : (Nat.card G : k) ≠ 0) (ρ : Representation k G V)
    (hCV : Representation.invariants (ρ.comp R.subtype) = ⊥) {x : G} (hx : x ∈ K) :
    ρ x = 1 := by
  have hkU : (Nat.card K : k) ≠ 0 := by
    refine fun hc => hk ?_
    rw [← hKR.card_mul_card, Nat.cast_mul, hc, zero_mul]
  refine eq_one_of_invariants_comp_subtype_eq_bot hK hKR (fun w hw hw1 => ?_) hkU ρ hCV hx
  exact inf_centralizer_singleton_eq_bot_of_natCard_eq_prime hr rfl hCK hw hw1

end Frobenius

section Induction

open scoped commutatorElement

universe u v w

private theorem eq_one_of_mem_commutator_of_invariants_eq_bot_aux {k : Type u}
    [Field k] [IsAlgClosed k] (n : ℕ) :
    ∀ {G : Type v} [Group G] [Finite G] [Group.IsSolvable G] {V : Type w} [AddCommGroup V]
      [Module k V] [FiniteDimensional k V] {K R : Subgroup G}, K.Normal →
      Nat.card G ≤ n → Odd (Nat.card G) → K.IsComplement' R →
      (Nat.card K).Coprime (Nat.card R) → (Nat.card R).Prime → ((Nat.card G : k) ≠ 0) →
      ∀ ρ : Representation k G V, Representation.invariants (ρ.comp R.subtype) = ⊥ →
      ∀ x ∈ (⁅K, R⁆ : Subgroup G), ρ x = 1 := by
  induction n with
  | zero =>
    intro G _ _ _ V _ _ _ K R _ hn
    have : 0 < Nat.card G := Nat.card_pos
    omega
  | succ n ih =>
  intro G _ _ _ V _ _ _ K R hKn hn hodd hKR hcop hr hk ρ hCV x hx
  have := hKn
  by_contra hne
  obtain ⟨S, hS0, hSinv, hSmin, v, hvS, hv⟩ := exists_minimal_invariant_apply_ne hk ρ hne
  have hSle : ∀ g : G, S ≤ S.comap (ρ g) := fun g w hw => hSinv g w hw
  set σ : Representation k G ↥S := ρ.subrepresentation S hSle with hσdef
  have hσirr : σ.IsIrreducible := isIrreducible_subrepresentation_of_minimal ρ hS0 hSinv hSmin
  have hSnt : Nontrivial ↥S := Submodule.nontrivial_iff_ne_bot.2 hS0
  have hσne : σ x ≠ 1 := fun hc =>
    hv (mem_repStabilizer.1 ((mem_repStabilizer_iff_subrepresentation_eq_one ρ hSle x).2 hc) v hvS)
  have hCS : Representation.invariants (σ.comp R.subtype) = ⊥ :=
    invariants_subrepresentation_comp_subtype_eq_bot ρ hSle hCV
  have hRn : R ≤ normalizer (K : Set G) := by rw [K.normalizer_eq_top]; exact le_top
  have hKodd : Odd (Nat.card ↥K) := Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card K)
  have hKdvd : Nat.card ↥K ∣ Nat.card G := Subgroup.card_subgroup_dvd_card K
  have hcast : ∀ m : ℕ, m ∣ Nat.card G → (m : k) ≠ 0 := by
    intro m ⟨c, hc⟩ h
    rw [hc, Nat.cast_mul, h, zero_mul] at hk
    exact hk rfl
  have hRne : R ≠ ⊥ := by
    intro hR1
    rw [hR1] at hr
    simp only [Nat.card_eq_fintype_card] at hr
    exact Nat.not_prime_one (by simpa using hr)
  have hrK : ¬ (Nat.card ↥R) ∣ Nat.card ↥K := fun hd =>
    absurd (Nat.Coprime.eq_one_of_dvd hcop.symm hd) hr.one_lt.ne'
  have hNR : MonoidHom.ker σ ⊓ R = ⊥ := inf_ker_eq_bot_of_invariants_eq_bot hr σ hCS
  have hNK : MonoidHom.ker σ ≤ K :=
    le_of_not_dvd_natCard hr hKR rfl (not_dvd_natCard_of_inf_eq_bot hr hKR rfl hrK hNR hRne)
  have hσinj : Function.Injective σ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    by_contra hNne
    have hQcard : Nat.card (G ⧸ MonoidHom.ker σ) ≤ n := natCard_quotient_le hNne hn
    have hQdvd : Nat.card (G ⧸ MonoidHom.ker σ) ∣ Nat.card G := by
      rw [← Subgroup.index_eq_card]; exact (MonoidHom.ker σ).index_dvd_card
    have hRcard := natCard_map_mk_of_inf_eq_bot hNR (N := MonoidHom.ker σ)
    have h := ih (QuotientGroup.map_normal (MonoidHom.ker σ) K) hQcard
      (Odd.of_dvd_nat hodd hQdvd) (isComplement'_map_mk hKR hNK)
      (by rw [hRcard]; exact Nat.Coprime.coprime_dvd_left (Subgroup.card_map_dvd K _) hcop)
      (by rw [hRcard]; exact hr) (hcast _ hQdvd) (quotKerRep σ)
      (by rw [invariants_quotKerRep_comp_subtype]; exact hCS)
      (QuotientGroup.mk' (MonoidHom.ker σ) x)
      (by rw [← Subgroup.map_commutator]; exact ⟨x, hx, rfl⟩)
    rw [QuotientGroup.mk'_apply, quotKerRep_mk] at h
    exact hσne h
  have hcent : ∀ L : Subgroup G, L ≤ K → L ≠ K → R ≤ normalizer (L : Set G) →
      L ≤ centralizer (R : Set G) := by
    intro L hLK hLne hLnorm
    have hLR : L ⊓ R = ⊥ := by
      rw [eq_bot_iff, ← disjoint_iff.1 hKR.disjoint]
      exact le_inf (inf_le_left.trans hLK) inf_le_right
    have hLU : L ≤ L ⊔ R := le_sup_left
    have hRU : R ≤ L ⊔ R := le_sup_right
    have hLnU : (L.subgroupOf (L ⊔ R)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (sup_le le_normalizer (by simpa using hLnorm))
    have hLcard : Nat.card (L.subgroupOf (L ⊔ R)) = Nat.card L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLU).toEquiv
    have hRcard : Nat.card (R.subgroupOf (L ⊔ R)) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv
    have hUdvd : Nat.card (L ⊔ R : Subgroup G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    have hUlt : Nat.card (L ⊔ R : Subgroup G) ≤ n := by
      have hUcard : Nat.card (L ⊔ R : Subgroup G) = Nat.card L * Nat.card R :=
        natCard_sup_eq_mul_of_le_normalizer hLnorm hLR
      have hlt : Nat.card (L ⊔ R : Subgroup G) < Nat.card G := by
        rw [hUcard, ← hKR.card_mul_card]
        exact Nat.mul_lt_mul_of_lt_of_le (natCard_lt_of_le_of_ne hLK hLne) le_rfl Nat.card_pos
      omega
    have hcomm := ih hLnU hUlt (Odd.of_dvd_nat hodd hUdvd)
      (isComplement'_subgroupOf_sup_of_le_normalizer hLR hLnorm)
      (by rw [hLcard, hRcard]
          exact Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hLK) hcop)
      (by rw [hRcard]; exact hr) (hcast _ hUdvd) (σ.comp (L ⊔ R : Subgroup G).subtype)
      (by rw [invariants_comp_subtype_subgroupOf σ hRU]; exact hCS)
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hcm : (⁅(⟨a, hLU ha⟩ : ↥(L ⊔ R : Subgroup G)), (⟨b, hRU hb⟩ : ↥(L ⊔ R : Subgroup G))⁆) ∈
        (⁅L.subgroupOf (L ⊔ R), R.subgroupOf (L ⊔ R)⁆ : Subgroup ↥(L ⊔ R : Subgroup G)) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.2 ha)
        (Subgroup.mem_subgroupOf.2 hb)
    have h3 : a * b * a⁻¹ * b⁻¹ = 1 := by
      simpa [commutatorElement_def] using hσinj ((hcomm _ hcm).trans (map_one σ).symm)
    have h4 : a * b * a⁻¹ = b := by simpa using mul_eq_one_iff_eq_inv.1 h3
    calc b * a = (a * b * a⁻¹) * a := by rw [h4]
      _ = a * b := by group
  have hcommne : (⁅K, R⁆ : Subgroup G) ≠ ⊥ := by
    intro hc
    rw [hc, Subgroup.mem_bot] at hx
    rw [hx, map_one] at hσne
    exact hσne rfl
  have hK2 : ¬ 1 < (Nat.card ↥K).primeFactors.card := fun h2 =>
    hcommne (commutator_eq_bot_of_one_lt_card_primeFactors hKR.sup_eq_top hcop h2 hcent)
  have hKcard1 : Nat.card ↥K ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one.1 h1] at hcommne
    simp at hcommne
  obtain ⟨q, hq, j, hj1, hKq⟩ :=
    exists_prime_pow_of_primeFactors_card_le_one Nat.card_pos.ne' hKcard1 hK2
  have := Fact.mk hq
  have hKpg : IsPGroup q ↥K := IsPGroup.of_card hKq
  have hKnt : Nontrivial ↥K := by
    rw [← Finite.one_lt_card_iff_nontrivial, hKq]
    calc 1 < q := hq.one_lt
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ j := Nat.pow_le_pow_right hq.pos hj1
  have hqK : q ∣ Nat.card ↥K := hKq ▸ dvd_pow_self q (by omega)
  have hqodd : Odd q := Odd.of_dvd_nat hKodd hqK
  have hqk : (q : k) ≠ 0 := hcast q (hqK.trans hKdvd)
  have hmin : IsMinimalInvariantAction q (conjAction hRn) (⊤ : Subgroup ↥R) :=
    ⟨hq, hqodd, hKnt, hKpg, Nat.Coprime.coprime_dvd_right hqK hcop.symm, inferInstance,
      fun hc => hcommne ((actionCommutator_conjAction_top_eq_bot_iff hRn).1 hc),
      forall_conjAction_apply_eq_of_ne_top hRn hcent⟩
  rcases hmin.isMulCommutative_or_center_eq_commutator with hab | ⟨hZC, hCΦ⟩
  ·
    have hΦ : frattini ↥K = ⊥ := by
      rw [hmin.frattini_eq_commutator, commutator_eq_bot_iff]; exact hab
    have hCK : K ⊓ centralizer (R : Set G) = ⊥ :=
      inf_centralizer_eq_bot_of_actionCentralizer_eq_bot hRn (by
        rw [eq_bot_iff, ← hΦ]
        exact actionCentralizer_le_frattini hRn
          hmin.actionCentralizer_frattiniQuotientAction_eq_bot)
    exact hσne (eq_one_of_mem_of_inf_centralizer_eq_bot ‹K.Normal› hKR hr hCK (hcast _ dvd_rfl)
      σ hCS (Subgroup.commutator_le_left K R hx))
  ·
    have hZne : Subgroup.center ↥K ≠ ⊤ := by
      intro hc
      have hcb : _root_.commutator ↥K = ⊥ :=
        (commutator_eq_bot_iff ↥K).2 (Subgroup.center_eq_top_iff.1 hc)
      rw [hZC, hcb] at hc
      obtain ⟨a, b, hab2⟩ := hKnt
      refine hab2 ?_
      have h1 : a ∈ (⊥ : Subgroup ↥K) := hc ▸ Subgroup.mem_top a
      have h2 : b ∈ (⊥ : Subgroup ↥K) := hc ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot] at h1 h2
      rw [h1, h2]
    have hZcent : ∀ d : ↥R, ∀ y ∈ Subgroup.center ↥K, conjAction hRn d y = y :=
      fun d y hy => hmin.centralizes _
        (isInvariantSubgroup_of_characteristic (conjAction hRn) (Subgroup.center ↥K)) hZne d
        (Subgroup.mem_top d) y hy
    have hZG : (Subgroup.center ↥K).map K.subtype ≤ Subgroup.center G :=
      map_center_le_center hRn hKR hZcent
    have hexp : ∀ z ∈ (Subgroup.center ↥K).map K.subtype, z ^ q = 1 := by
      rintro z ⟨w, hw, rfl⟩
      simpa using congrArg (Subtype.val) (hmin.pow_eq_one w)
    have hZcard : Nat.card (Subgroup.center ↥K) ≤ q := by
      rw [Nat.card_congr ((Subgroup.center ↥K).equivMapOfInjective K.subtype
        (Subgroup.subtype_injective K)).toEquiv]
      exact natCard_le_of_le_center_of_injective σ hσinj hZG hq.pos hexp
    have hZ1 : 1 < Nat.card (Subgroup.center ↥K) :=
      Finite.one_lt_card_iff_nontrivial.2 hKpg.center_nontrivial
    obtain ⟨i, hi⟩ := (hKpg.to_subgroup (Subgroup.center ↥K)).exists_card_eq
    have hZeq : Nat.card (Subgroup.center ↥K) = q := by
      rw [hi] at hZ1 hZcard ⊢
      rcases Nat.lt_or_ge i 2 with hi2 | hi2
      · interval_cases i
        · simp at hZ1
        · simp
      · exact absurd (le_trans (Nat.pow_le_pow_right hq.pos hi2) hZcard)
          (by nlinarith [hq.two_le])
    have hP : IsExtraspecial q ↥K := ⟨hq, inferInstance, hKpg, hZC, hCΦ, hZeq⟩
    have hfix : ∀ y : ↥K ⧸ Subgroup.center ↥K,
        (∀ a : ↥R, centerQuotAut (conjAction hRn) a y = y) → y = 1 :=
      eq_one_of_forall_centerQuotAut_eq hRn (hZC.trans hCΦ)
        hmin.actionCentralizer_frattiniQuotientAction_eq_bot
    obtain ⟨h, hho, hgen⟩ :=
      exists_orderOf_eq_zpowers_eq_top (A := ↥R) (r := Nat.card ↥R) rfl hr
    have hRdvd : Nat.card ↥R ∣ Nat.card G := Subgroup.card_subgroup_dvd_card R
    obtain ⟨w, hw0, hw⟩ := exists_ne_zero_mem_invariants_resInr_of_faithful
      (ρ := semidirectRep hRn hKR σ) (h := h) hP hqk hqodd hZcent hr
      (Odd.of_dvd_nat hodd hRdvd) (hcast _ hRdvd) hho hgen hfix
      (fun g hg => (semidirectRep_eq_one_iff hRn hKR σ hσinj).1 hg)
    rw [invariants_resInr_semidirectRep, hCS, Submodule.mem_bot] at hw
    exact hw0 hw

end Induction

section Main

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable {K R : Subgroup G}

theorem eq_one_of_mem_commutator_of_invariants_eq_bot
    [IsAlgClosed k] [FiniteDimensional k V] [Finite G] [Group.IsSolvable G] [K.Normal]
    (hodd : Odd (Nat.card G)) (hKR : K.IsComplement' R)
    (hcop : (Nat.card K).Coprime (Nat.card R)) (hr : (Nat.card R).Prime)
    (hk : (Nat.card G : k) ≠ 0) (ρ : Representation k G V)
    (hCV : Representation.invariants (ρ.comp R.subtype) = ⊥)
    {x : G} (hx : x ∈ (⁅K, R⁆ : Subgroup G)) : ρ x = 1 :=
  eq_one_of_mem_commutator_of_invariants_eq_bot_aux (Nat.card G) ‹K.Normal› le_rfl hodd hKR hcop
    hr hk ρ hCV x hx

theorem eq_one_of_generalLinearGroup_of_mem_commutator_of_invariants_eq_bot
    [IsAlgClosed k] [FiniteDimensional k V] [Finite G] [Group.IsSolvable G] [K.Normal]
    (hodd : Odd (Nat.card G)) (hKR : K.IsComplement' R)
    (hcop : (Nat.card K).Coprime (Nat.card R)) (hr : (Nat.card R).Prime)
    (hk : (Nat.card G : k) ≠ 0) (ρ : G →* LinearMap.GeneralLinearGroup k V)
    (hCV : Representation.invariants
      (((Units.coeHom (V →ₗ[k] V)).comp ρ).comp R.subtype) = ⊥)
    {x : G} (hx : x ∈ (⁅K, R⁆ : Subgroup G)) : ρ x = 1 := by
  refine Units.ext ?_
  simpa using eq_one_of_mem_commutator_of_invariants_eq_bot hodd hKR hcop hr hk
    ((Units.coeHom (V →ₗ[k] V)).comp ρ) hCV hx

theorem forall_apply_eq_self_of_mem_commutator_of_invariants_eq_bot
    [IsAlgClosed k] [FiniteDimensional k V] [Finite G] [Group.IsSolvable G] [K.Normal]
    (hodd : Odd (Nat.card G)) (hKR : K.IsComplement' R)
    (hcop : (Nat.card K).Coprime (Nat.card R)) (hr : (Nat.card R).Prime)
    (hk : (Nat.card G : k) ≠ 0) (ρ : Representation k G V)
    (hCV : Representation.invariants (ρ.comp R.subtype) = ⊥) :
    ∀ x ∈ (⁅K, R⁆ : Subgroup G), ∀ v : V, ρ x v = v := by
  intro x hx v
  rw [eq_one_of_mem_commutator_of_invariants_eq_bot hodd hKR hcop hr hk ρ hCV hx]
  simp

end Main

end CFSG.FeitThompson
