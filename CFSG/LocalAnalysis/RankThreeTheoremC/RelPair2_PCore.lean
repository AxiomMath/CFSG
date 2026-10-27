module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Signalizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Sylow
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantQuotientFixedPoints

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem exists_orderOf_eq_centralizing_of_normal {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {Q D : Subgroup X} [Q.Normal] (hQp : IsPGroup p Q) (hQ1 : Q ≠ ⊥)
    (hDp : IsPGroup p D) : ∃ u ∈ Q, orderOf u = p ∧ ∀ d ∈ D, d * u = u * d := by
  have hPp : IsPGroup p (D ⊔ Q : Subgroup X) := hDp.to_sup_of_normal_right hQp
  have : Group.IsNilpotent (D ⊔ Q : Subgroup X) := hPp.isNilpotent
  have hQP : Q ≤ D ⊔ Q := le_sup_right
  have hH : Q.subgroupOf (D ⊔ Q) ≠ ⊥ := by
    intro h
    exact hQ1 ((by simpa using h : Disjoint Q (D ⊔ Q)).eq_bot_of_le hQP)
  have hK := Group.IsNilpotent.inf_center_ne_bot_of_normal hH
  have hKp : IsPGroup p ↥(Q.subgroupOf (D ⊔ Q) ⊓ center (D ⊔ Q : Subgroup X)) :=
    hPp.to_subgroup _
  have : Nontrivial ↥(Q.subgroupOf (D ⊔ Q) ⊓ center (D ⊔ Q : Subgroup X)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hK
  obtain ⟨n, hn, hcard⟩ := hKp.nontrivial_iff_card.mp inferInstance
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p (hcard ▸ dvd_pow_self p hn.ne')
  refine ⟨(((a : (D ⊔ Q : Subgroup X)) : X)), a.2.1, ?_, fun d hd => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ha]
  · exact congrArg Subtype.val
      (mem_center_iff.mp a.2.2 ⟨d, (le_sup_left : D ≤ D ⊔ Q) hd⟩)

theorem exists_centralizer_mul_mem_of_commute_map {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (K : Subgroup Y) [K.Normal] {R : Subgroup Y}
    (hR2 : IsPGroup 2 R) {z : Y} (hzR : z ∈ normalizer (R : Set Y)) (hzp : z ^ p = 1) {r : Y}
    (hr : r ∈ R) (hcomm : QuotientGroup.mk' K r * QuotientGroup.mk' K z =
      QuotientGroup.mk' K z * QuotientGroup.mk' K r) :
    ∃ r₀ ∈ R, r₀ * z = z * r₀ ∧ r₀⁻¹ * r ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : zpowers z ≤ normalizer (R : Set Y) := zpowers_le.mpr hzR
  have hact : IsPGroup p (zpowers z) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp g.2
    simp only [pow_one, coe_pow, OneMemClass.coe_one]
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzp, one_zpow]
  have hinv : ∀ a : zpowers z, ∀ x ∈ K.subgroupOf R,
      ambientSubgroupActionHom (zpowers z) R hzz a x ∈ K.subgroupOf R := by
    intro a x hx
    change ((ambientSubgroupActionHom (zpowers z) R hzz a x : R) : Y) ∈ K
    rw [ambientSubgroupActionHom_apply_coe]
    exact Normal.conj_mem (inferInstance : K.Normal) _ hx _
  have hcop : p.Coprime (Nat.card (K.subgroupOf R)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hR2.to_subgroup (K.subgroupOf R))
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp2)
  have hfix : ∀ a : zpowers z,
      invariantQuotientActionHom (ambientSubgroupActionHom (zpowers z) R hzz) (K.subgroupOf R)
        hinv a (QuotientGroup.mk' (K.subgroupOf R) ⟨r, hr⟩) =
      QuotientGroup.mk' (K.subgroupOf R) ⟨r, hr⟩ := by
    intro a
    rw [invariantQuotientActionHom_mk]
    refine QuotientGroup.eq.mpr ?_
    change (((ambientSubgroupActionHom (zpowers z) R hzz a ⟨r, hr⟩)⁻¹ * ⟨r, hr⟩ : R) : Y) ∈ K
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp a.2
    have hc : Commute (QuotientGroup.mk' K r) (QuotientGroup.mk' K (a : Y)) := by
      rw [← hi, map_zpow]
      exact Commute.zpow_right hcomm i
    rw [← QuotientGroup.ker_mk' K, MonoidHom.mem_ker]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ambientSubgroupActionHom_apply_coe, map_mul,
      map_inv]
    rw [hc.symm.mul_inv_cancel, inv_mul_cancel]
  obtain ⟨r₀, hr₀, hfix₀⟩ := coprime_normal_quotient_fixed_lift p Fact.out hact
    (ambientSubgroupActionHom (zpowers z) R hzz) (K.subgroupOf R) hinv hcop _ hfix
  have hz₀ := congrArg Subtype.val (hfix₀ ⟨z, mem_zpowers z⟩)
  rw [ambientSubgroupActionHom_apply_coe, mul_inv_eq_iff_eq_mul] at hz₀
  have hmem : r₀⁻¹ * ⟨r, hr⟩ ∈ K.subgroupOf R := (QuotientGroup.eq (s := K.subgroupOf R)).mp hr₀
  exact ⟨(r₀ : Y), r₀.2, hz₀.symm, hmem⟩

theorem eq_one_of_mem_isPGroup_of_pow_two_pow_eq_one {X : Type*} [Group X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup X} (hQ : IsPGroup p Q) {x : X} (hxQ : x ∈ Q)
    {k : ℕ} (hk : x ^ (2 ^ k) = 1) : x = 1 := by
  obtain ⟨m, hm⟩ := hQ ⟨x, hxQ⟩
  have hm' : x ^ (p ^ m) = 1 := congrArg Subtype.val hm
  have hcop : Nat.Coprime (2 ^ k) (p ^ m) :=
    Nat.Coprime.pow k m ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ p ^ m := orderOf_dvd_of_pow_eq_one hm'
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

variable {G : Type} [Group G] [Finite G]

theorem IsRelPairCandidate.pCore_quotient_eq_bot (hS : Setting G) (hD1 : TheoremD1 G)
    (hK : KFactLemma212) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M D R T H : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) (hH : IsRelPairCandidate p D R T H) :
    CFSG.Open.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥ := by
  classical
  by_contra hQ
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, -⟩ :=
    hext.transitivity_data hS hD1 hp hPD hR h13
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hDp : IsPGroup p D := P.isPGroup'.to_le hDP
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hH.base_le
  set K' : Subgroup H := primeComplementCore (G := H) p with hK'
  set π : H →* H ⧸ K' := QuotientGroup.mk' K' with hπ
  have hDHp : IsPGroup p (D.subgroupOf H) :=
    hDp.of_equiv (Subgroup.subgroupOfEquivOfLe hDH).symm
  have hDbarp : IsPGroup p ((D.subgroupOf H).map π) := hDHp.map π
  have hQnormal : (CFSG.Open.pCore p (H ⧸ K')).Normal :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal p
  obtain ⟨u, huQ, huo, hucomm⟩ := exists_orderOf_eq_centralizing_of_normal
    (Q := CFSG.Open.pCore p (H ⧸ K')) (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup p) hQ
    hDbarp
  have hcontainsH : ∀ e : H, e ∈ centralizer ((D.subgroupOf H : Subgroup H) : Set H) →
      orderOf e = p → e ∈ D.subgroupOf H := by
    intro e hec heo
    have hxC : (e : G) ∈ centralizer (D : Set G) := by
      apply mem_centralizer_iff.mpr
      intro d hd
      exact congrArg Subtype.val (mem_centralizer_iff.mp hec ⟨d, hDH hd⟩ hd)
    have hxp : (e : G) ^ p = 1 := by
      have : orderOf (e : G) = p := (Subgroup.orderOf_coe e).trans heo
      rw [← this]
      exact pow_orderOf_eq_one _
    exact hext.mem_of_mem_centralizer_of_isMulCommutative hS hD1 hp hDab hCD hxC hxp
  have hker : p.Coprime (Nat.card π.ker) := by
    rw [hπ, QuotientGroup.ker_mk']
    exact primeComplementCore_coprime p
  have hSC := coprime_quotient_preserves_order_prime_centralizer_condition p hprime
    (D.subgroupOf H) hDHp π (QuotientGroup.mk'_surjective K') hker hcontainsH
  have huC : u ∈ centralizer (((D.subgroupOf H).map π : Subgroup (H ⧸ K')) : Set (H ⧸ K')) :=
    mem_centralizer_iff.mpr fun d hd => hucomm d hd
  obtain ⟨δ, hδ, hδu⟩ := hSC u huC huo
  have hdD : (δ : G) ∈ D := hδ
  have hdH : (δ : G) ∈ H := δ.2
  have hd1 : (δ : G) ≠ 1 := by
    intro h
    have hδ1 : δ = 1 := Subtype.ext h
    rw [hδ1, map_one] at hδu
    rw [← hδu, orderOf_one] at huo
    exact hprime.one_lt.ne huo
  have hdp : (δ : G) ^ p = 1 := (hext.pow_eq_one_and_commutator_mem hprime hodd).1 _ hdD
  have huδ : π δ ∈ CFSG.Open.pCore p (H ⧸ K') := by rw [hδu]; exact huQ
  obtain ⟨Kd, -, -, hKdc, hKdall⟩ := hext.exists_normal_coprime_signalizer hS hD1 hK hp hPD hR
    h13 hdD hd1
  set Kg : Subgroup G := K'.map H.subtype with hKg
  have hKgH : Kg ≤ H := Subgroup.map_subtype_le _
  have hKgN : H ≤ normalizer (Kg : Set G) := CFSG.ABGTheoremB.le_normalizer_map_subtype H _
  have hKgc : p.Coprime (Nat.card Kg) := by
    rw [hKg, card_map_of_injective H.subtype_injective]
    exact primeComplementCore_coprime p
  have hDzp : D ≤ normalizer ((zpowers (δ : G) : Subgroup G) : Set G) := fun x hx =>
    centralizer_singleton_le_normalizer_zpowers (δ : G) (mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hDab.is_comm.comm ⟨x, hx⟩ ⟨(δ : G), hdD⟩)))
  have hDC : D ≤ normalizer ((centralizer ({(δ : G)} : Set G) : Subgroup G) : Set G) := by
    have h := hDzp.trans (normalizer_le_normalizer_centralizer (zpowers (δ : G)))
    rwa [zpowers_eq_closure, Subgroup.centralizer_closure] at h
  have hall : ∀ A : Subgroup G, A ≤ H → IsPGroup 2 A → D ≤ normalizer (A : Set G) →
      A ≤ Kg ⊔ (Kd ⊓ H) := by
    intro A hAH hA2 hDA r hr
    have hdN : (δ : G) ∈ normalizer (A : Set G) := hDA hdD
    have hc : r * (δ : G) * r⁻¹ * (δ : G)⁻¹ ∈ A := by
      have h1 : (δ : G) * r⁻¹ * (δ : G)⁻¹ ∈ A := (mem_normalizer_iff.mp hdN r⁻¹).mp (A.inv_mem hr)
      have : r * (δ : G) * r⁻¹ * (δ : G)⁻¹ = r * ((δ : G) * r⁻¹ * (δ : G)⁻¹) := by group
      rw [this]
      exact A.mul_mem hr h1
    have hcomm : π ⟨r, hAH hr⟩ * π δ = π δ * π ⟨r, hAH hr⟩ := by
      set c : H := ⟨r, hAH hr⟩ * δ * ⟨r, hAH hr⟩⁻¹ * δ⁻¹ with hcdef
      have hcA : (c : G) ∈ A := by
        have : (c : G) = r * (δ : G) * r⁻¹ * (δ : G)⁻¹ := rfl
        rw [this]
        exact hc
      have hcQ : π c ∈ CFSG.Open.pCore p (H ⧸ K') := by
        have : π c = (π ⟨r, hAH hr⟩ * π δ * (π ⟨r, hAH hr⟩)⁻¹) * (π δ)⁻¹ := by
          simp only [hcdef, map_mul, map_inv]
        rw [this]
        exact Subgroup.mul_mem _ (hQnormal.conj_mem _ huδ _) (Subgroup.inv_mem _ huδ)
      obtain ⟨k, hk⟩ := hA2 ⟨(c : G), hcA⟩
      have hkG : (c : G) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      have hk' : c ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hkG)
      have hπc : π c = 1 := eq_one_of_mem_isPGroup_of_pow_two_pow_eq_one hprime hodd
        (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup p) hcQ (k := k)
        (by rw [← map_pow, hk', map_one])
      have : π ⟨r, hAH hr⟩ * π δ * (π ⟨r, hAH hr⟩)⁻¹ * (π δ)⁻¹ = 1 := by
        rw [← hπc]
        simp only [hcdef, map_mul, map_inv]
      exact (mul_inv_eq_one.mp (by rw [← this]; group))
    have hzR : δ ∈ normalizer ((A.subgroupOf H : Subgroup H) : Set H) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hAH]
      exact hdN
    obtain ⟨r₀, hr₀A, hr₀z, hr₀K⟩ := exists_centralizer_mul_mem_of_commute_map hodd K'
      (hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAH).symm) hzR
      (by exact Subtype.ext hdp) (r := ⟨r, hAH hr⟩) hr hcomm
    have hr₀C : (r₀ : G) ∈ centralizer ({(δ : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hr₀z)
    have hY2 : IsPGroup 2 ((A ⊓ centralizer ({(δ : G)} : Set G) : Subgroup G)) :=
      hA2.to_inf_left
    have hYc : p.Coprime (Nat.card (A ⊓ centralizer ({(δ : G)} : Set G) : Subgroup G)) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hY2
      rw [hn]
      exact ((Nat.coprime_primes hprime Nat.prime_two).mpr hodd).pow_right n
    have hr₀Kd : (r₀ : G) ∈ Kd :=
      hKdall _ (inf_le_right.trans (centralizer_singleton_le_normalizer_zpowers (δ : G))) hYc
        (common_normalizer_le_normalizer_inf D A _ hDA hDC) ⟨hr₀A, hr₀C⟩
    have hmemKg : (r₀ : G)⁻¹ * r ∈ Kg := by
      have h : H.subtype (r₀⁻¹ * ⟨r, hAH hr⟩) ∈ K'.map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype hr₀K
      exact h
    have hprod : r = (r₀ : G) * ((r₀ : G)⁻¹ * r) := by group
    rw [sup_comm, hprod]
    exact Subgroup.mul_mem_sup ⟨hr₀Kd, r₀.2⟩ hmemKg
  have hjoin : invariantTwoJoinIn D H ≤ Kg ⊔ (Kd ⊓ H) := invariantTwoJoinIn_le_of_forall hall
  have hWc : p.Coprime (Nat.card (Kd ⊓ H : Subgroup G)) :=
    hKdc.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  have hcop : p.Coprime (Nat.card (Kg ⊔ (Kd ⊓ H) : Subgroup G)) :=
    coprime_card_sup_of_normalized_coprime hKgH inf_le_right hKgN hKgc hWc
  exact (hprime.coprime_iff_not_dvd.mp hcop)
    (hH.not_coprime.trans (Subgroup.card_dvd_of_le hjoin))

end CFSG.LocalAnalysis.RankThreeTheoremC
