module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightFamily
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.QuotientFamily
public import CFSG.ClassicalInvolution.Asc77.AscE184Cent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace OddQuot

section Basic

variable {G : Type} [Group G]

theorem exists_conj_of_involutions {N : Subgroup G} (hN : Odd (Nat.card N)) {z s : G}
    (hz : z * z = 1) (hs : s * s = 1) (h : s⁻¹ * z ∈ N) : ∃ n ∈ N, n * z * n⁻¹ = s := by
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [hs'] at h
  set c : G := s * z with hc
  have hcN : c ∈ N := h
  have hodd : Odd (orderOf c) := by
    have : orderOf c ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨c, hcN⟩ : N)
      rwa [← Subgroup.orderOf_coe] at this
    exact hN.of_dvd_nat this
  obtain ⟨k, hk⟩ := hodd
  have hcm : c ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one c
  refine ⟨c ^ (k + 1), N.pow_mem hcN _, ?_⟩
  have hzc : z * c⁻¹ * z⁻¹ = c := by
    rw [hc, hz']
    have : (s * z)⁻¹ = z * s := by
      rw [mul_inv_rev, hz', hs']
    rw [this]
    calc z * (z * s) * z = (z * z) * s * z := by group
      _ = s * z := by rw [hz]; group
  have e1 : c ^ (k + 1) * z * (c ^ (k + 1))⁻¹ = c ^ (k + 1) * (z * (c⁻¹) ^ (k + 1) * z⁻¹) * z := by
    rw [inv_pow]
    group
  have e2 : z * (c⁻¹) ^ (k + 1) * z⁻¹ = c ^ (k + 1) := by
    rw [← conj_pow, hzc]
  rw [e1, e2]
  have e3 : c ^ (k + 1) * c ^ (k + 1) = c := by
    rw [← pow_add]
    have : k + 1 + (k + 1) = (2 * k + 1) + 1 := by ring
    rw [this, pow_succ, hcm, one_mul]
  calc c ^ (k + 1) * c ^ (k + 1) * z = c * z := by rw [e3]
    _ = s := by rw [hc]; calc s * z * z = s * (z * z) := by group
                                _ = s := by rw [hz]; group

end Basic

section Members

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G}

theorem two_elt {K : Subgroup G} (hK : IsPGroup 2 K) {k : G} (hk : k ∈ K) : ∃ a : ℕ, k ^ 2 ^ a = 1 := by
  obtain ⟨a, ha⟩ := hK ⟨k, hk⟩
  exact ⟨a, by simpa using congrArg Subtype.val ha⟩

theorem oddCoreOf_eq_bot_of_isPGroup {K : Subgroup G} (hK : IsPGroup 2 K) : oddCoreOf K = ⊥ := by
  have h1 : oddCoreOf K ≤ K := Subgroup.map_subtype_le _
  have h2 := S1916.inf_oddCoreOf_eq_bot hK K
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ K ⊓ oddCoreOf K := ⟨h1 hx, hx⟩
  rw [h2] at this
  exact this

theorem commutes_of_twin_pgroup (hΩ : HypOmegaGen Ω) (h2 : ∀ K ∈ Ω, IsPGroup 2 K)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : K ≠ J) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) :
    ∀ k ∈ K, ∀ j ∈ J, k * j = j * k := by
  have h := Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ hne hzK hzJ
  rw [oddCoreOf_eq_bot_of_isPGroup (h2 K hK)] at h
  intro k hk j hj
  have h3 := h (Subgroup.commutator_mem_commutator hk hj)
  have h1 : ⁅k, j⁆ = 1 := by simpa using h3.1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem eq_of_commute_of_mem (hN : Odd (Nat.card N)) {k j : G} (hk : ∃ a : ℕ, k ^ 2 ^ a = 1)
    (hj : ∃ b : ℕ, j ^ 2 ^ b = 1) (hc : k * j = j * k) (h : k⁻¹ * j ∈ N) : k = j := by
  obtain ⟨a, ha⟩ := hk
  obtain ⟨b, hb⟩ := hj
  have hcm : Commute k⁻¹ j := (Commute.inv_left (show Commute k j from hc))
  have hx : (k⁻¹ * j) ^ 2 ^ (a + b) = 1 := by
    rw [hcm.mul_pow, inv_pow]
    have h1 : k ^ 2 ^ (a + b) = 1 := by
      rw [pow_add, pow_mul, ha, one_pow]
    have h2 : j ^ 2 ^ (a + b) = 1 := by
      rw [add_comm, pow_add, pow_mul, hb, one_pow]
    rw [h1, h2]; simp
  have hdvd1 : orderOf (k⁻¹ * j) ∣ 2 ^ (a + b) := orderOf_dvd_of_pow_eq_one hx
  have hdvd2 : orderOf (k⁻¹ * j) ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨k⁻¹ * j, h⟩ : N)
    rwa [← Subgroup.orderOf_coe] at this
  have hcop : Nat.Coprime (2 ^ (a + b)) (Nat.card N) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hN)
  have h1 : orderOf (k⁻¹ * j) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have := orderOf_eq_one_iff.mp h1
  calc k = k * (k⁻¹ * j) := by rw [this]; group
    _ = j := by group

end Members

section Quot

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem map_conjSub_of_mem {n : G} (hn : n ∈ N) (J : Subgroup G) :
    (conjSub n J).map (QuotientGroup.mk' N) = J.map (QuotientGroup.mk' N) := by
  rw [AscQuot.map_conjSub]
  have : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  rw [this, conjSub_one]

theorem inv_mul_mem_of_mk_eq {a b : G} (h : QuotientGroup.mk' N a = QuotientGroup.mk' N b) :
    a⁻¹ * b ∈ N := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
  exact h

theorem exists_conj_member (hΩ : ConjInvariant Ω) (hN : Odd (Nat.card N)) {J : Subgroup G}
    (hJ : J ∈ Ω) {t z : G} (ht : IsUniqueInvolution J t) (hz : z * z = 1)
    (hπ : QuotientGroup.mk' N z = QuotientGroup.mk' N t) :
    ∃ n ∈ N, conjSub n J ∈ Ω ∧ IsUniqueInvolution (conjSub n J) z ∧
      (conjSub n J).map (QuotientGroup.mk' N) = J.map (QuotientGroup.mk' N) := by
  obtain ⟨n, hn, hnz⟩ := exists_conj_of_involutions hN (z := t) (s := z) ht.sq hz
    (inv_mul_mem_of_mk_eq hπ)
  refine ⟨n, hn, hΩ n J hJ, ?_, map_conjSub_of_mem hn J⟩
  have := ht.conj n
  rwa [hnz] at this

theorem isPGroup_zpowers_of_pow {x : G} {a : ℕ} (h : x ^ 2 ^ a = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have hd : orderOf x ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

theorem exists_conj_commuting (hN : Odd (Nat.card N)) {z v : G} (hz : z * z = 1)
    (hv : ∃ a : ℕ, v ^ 2 ^ a = 1)
    (hc : QuotientGroup.mk' N v * QuotientGroup.mk' N z =
      QuotientGroup.mk' N z * QuotientGroup.mk' N v) :
    ∃ n ∈ N, (n * z * n⁻¹) * v = v * (n * z * n⁻¹) := by
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨a, ha⟩ := hv
  have hzπ : (π z) ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, ← map_mul, hz, map_one]
  have hvπ : (π v) ^ 2 ^ a = 1 := by rw [← map_pow, ha, map_one]
  have h2z : IsPGroup 2 (Subgroup.zpowers (π z)) := isPGroup_zpowers_of_pow hzπ
  have h2v : IsPGroup 2 (Subgroup.zpowers (π v)) := isPGroup_zpowers_of_pow hvπ
  have hnorm : Subgroup.zpowers (π z) ≤ Subgroup.normalizer
      ((Subgroup.zpowers (π v) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    refine Subgroup.zpowers_le.mpr ?_
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute (π v) (π z) from hc) k).eq
  set Tb : Subgroup (G ⧸ N) := Subgroup.zpowers (π z) ⊔ Subgroup.zpowers (π v) with hTb
  have hTb2 : IsPGroup 2 Tb := IsPGroup.to_sup_of_normal_right' h2z h2v hnorm
  set T : Subgroup G := Tb.comap π with hT
  have hvT : v ∈ T := by
    show π v ∈ Tb
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hzT : π z ∈ Tb := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := isPGroup_zpowers_of_pow ha
  obtain ⟨P, hP, hvP⟩ := IsSylow2In.exists_ge hv2 (Subgroup.zpowers_le.mpr hvT)
  have hmap := Hall196.isSylow2In_map_hom π hP
  have hTmap : T.map π = Tb := Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective N) Tb
  rw [hTmap] at hmap
  have hPmap : Tb = P.map π := hmap.2.2 Tb le_rfl hTb2 (by
    rw [← hTmap]; exact Subgroup.map_mono hP.1)
  obtain ⟨s, hsP, hsz⟩ := (show π z ∈ P.map π from hPmap ▸ hzT)
  have hPN : P ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hP.2.1 le_rfl (odd_natCard_inf hN P)
  have hss : s * s = 1 := by
    have h0 : π (s * s) = 1 := by rw [map_mul, hsz, ← map_mul, hz, map_one]
    have h1 : s * s ∈ P ⊓ N :=
      ⟨P.mul_mem hsP hsP, (QuotientGroup.eq_one_iff (s * s)).mp h0⟩
    rw [hPN, Subgroup.mem_bot] at h1
    exact h1
  obtain ⟨n, hn, hnz⟩ := exists_conj_of_involutions hN hz hss (inv_mul_mem_of_mk_eq hsz)
  refine ⟨n, hn, ?_⟩
  rw [hnz]
  have hvP' : v ∈ P := hvP (Subgroup.mem_zpowers v)
  have h0 : π ⁅s, v⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hsz]
    exact hc.symm
  have h1 : ⁅s, v⁆ ∈ P ⊓ N := by
    refine ⟨?_, (QuotientGroup.eq_one_iff _).mp h0⟩
    simp only [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hsP hvP') (P.inv_mem hsP)) (P.inv_mem hvP')
  rw [hPN, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end Quot

section Family

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem inf_eq_bot_of_mem (h2 : ∀ K ∈ Ω, IsPGroup 2 K) (hN : Odd (Nat.card N)) {K : Subgroup G}
    (hK : K ∈ Ω) : K ⊓ N = ⊥ :=
  AscQuot.inf_eq_bot_of_isPGroup_of_odd N (h2 K hK) le_rfl (odd_natCard_inf hN K)

theorem omega4_quot (hΩ : HypOmegaGen Ω) (h2 : ∀ K ∈ Ω, IsPGroup 2 K) (hN : Odd (Nat.card N))
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hne : K.map (QuotientGroup.mk' N) ≠ J.map (QuotientGroup.mk' N)) :
    padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓ J.map (QuotientGroup.mk' N))) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓
          J.map (QuotientGroup.mk' N))) = 1 →
        ⁅K.map (QuotientGroup.mk' N), J.map (QuotientGroup.mk' N)⁆ ≤
          oddCoreOf (K.map (QuotientGroup.mk' N)) ⊓ oddCoreOf (J.map (QuotientGroup.mk' N))) := by
  have hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(N ⊓ K)) := fun K _ => odd_natCard_inf hN K
  by_cases heven : 2 ∣ Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓ J.map (QuotientGroup.mk' N))
  swap
  · rw [padicValNat.eq_zero_of_not_dvd heven]
    exact ⟨zero_le_one, fun h => absurd h (by norm_num)⟩
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hz' := isUniqueInvolution_map_mk_of_odd (hXK K hK) hz
  have ht' := isUniqueInvolution_map_mk_of_odd (hXK J hJ) ht
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(K.map (QuotientGroup.mk' N) ⊓ J.map (QuotientGroup.mk' N))) 2 heven
  have haG : orderOf (a : G ⧸ N) = 2 := by rw [Subgroup.orderOf_coe]; exact ha
  have hasq : (a : G ⧸ N) * (a : G ⧸ N) = 1 := by
    have := pow_orderOf_eq_one (a : G ⧸ N)
    rwa [haG, pow_two] at this
  have hane : (a : G ⧸ N) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at haG
    omega
  have haz : (a : G ⧸ N) = QuotientGroup.mk' N z :=
    (hz'.unique _ a.2.1 hasq).resolve_left hane
  have hat : (a : G ⧸ N) = QuotientGroup.mk' N t :=
    (ht'.unique _ a.2.2 hasq).resolve_left hane
  obtain ⟨n, hn, hJ'Ω, hzJ', himg⟩ := exists_conj_member hΩ.conjInvariant hN hJ ht hz.sq
    (haz.symm.trans hat)
  have hKJ' : K ≠ conjSub n J := fun h => hne (by rw [h, himg])
  have hcomm := commutes_of_twin_pgroup hΩ h2 hK hJ'Ω hKJ' hz hzJ'
  have hsub : ∀ b ∈ K.map (QuotientGroup.mk' N) ⊓ J.map (QuotientGroup.mk' N),
      IsPGroup 2 (Subgroup.zpowers b) → b = 1 ∨ b = QuotientGroup.mk' N z := by
    intro b hb _
    obtain ⟨⟨k, hk, rfl⟩, hbJ⟩ := Subgroup.mem_inf.mp hb
    rw [← himg] at hbJ
    obtain ⟨j, hj, hjk⟩ := hbJ
    have hkj : k = j := eq_of_commute_of_mem hN (two_elt (h2 K hK) hk)
      (two_elt (h2 _ hJ'Ω) hj) (hcomm k hk j hj) (inv_mul_mem_of_mk_eq hjk.symm)
    have hkJ' : k ∈ conjSub n J := hkj ▸ hj
    have hcent : ∀ y ∈ K, ⁅k, y⁆ ∈ oddCoreOf K := by
      intro y hy
      have : ⁅k, y⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (hcomm y hy k hkJ').symm
      rw [this]
      exact (oddCoreOf K).one_mem
    rcases Sec6Gen.center_two hΩ hK hz k hk
      ((h2 K hK).to_le (Subgroup.zpowers_le.mpr hk)) hcent with h | h
    · left; rw [h, map_one]
    · right; rw [h]
  refine ⟨padicValNat_natCard_le_one_of_forall_isPGroup hsub, fun _ => ?_⟩
  have hbot : ⁅K.map (QuotientGroup.mk' N), J.map (QuotientGroup.mk' N)⁆ = ⊥ := by
    rw [← himg, ← Subgroup.map_commutator]
    have : ⁅K, conjSub n J⁆ = ⊥ := by
      rw [eq_bot_iff]
      refine Subgroup.commutator_le.mpr fun k hk j hj => ?_
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm k hk j hj)
    rw [this, Subgroup.map_bot]
  rw [hbot]
  exact bot_le

theorem omega5_quot (hΩ : HypOmegaGen Ω) (h2 : ∀ K ∈ Ω, IsPGroup 2 K) (hN : Odd (Nat.card N)) :
    ∀ L ∈ quotFamily Ω N, ∀ L' ∈ quotFamily Ω N, L ≠ L' →
      ∀ z : G ⧸ N, IsUniqueInvolution L z → ∀ v ∈ L',
        (¬ ∀ w ∈ L', v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
          v ∈ Subgroup.normalizer (L : Set (G ⧸ N)) := by
  have hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(N ⊓ K)) := fun K _ => odd_natCard_inf hN K
  rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne zb hzb _ ⟨v₀, hv₀J, rfl⟩ hvnc _ hcomm
  beta_reduce at hne hzb hvnc ⊢
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  have hzb' : zb = QuotientGroup.mk' N z :=
    hzb.eq (isUniqueInvolution_map_mk_of_odd (hXK K hK) hz)
  have hvnc' : ¬ ∀ w ∈ J, v₀ * w = w * v₀ := fun h => hvnc (by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, h w hw])
  obtain ⟨n, hn, hncomm⟩ := exists_conj_commuting hN hz.sq (two_elt (h2 J hJ) hv₀J)
    (by rw [← hzb']; exact hcomm)
  have himg := map_conjSub_of_mem hn K
  have hne' : conjSub n K ≠ J := fun h => hne (by rw [← himg, h])
  have hnorm := hΩ.omega5 (conjSub n K) (hΩ.conjInvariant n K hK) J hJ hne' _ (hz.conj n) v₀ hv₀J
    hvnc' ((h2 J hJ).to_le (Subgroup.zpowers_le.mpr hv₀J)) hncomm.symm
  have := mk_mem_normalizer_map (N := N) hnorm
  rwa [himg] at this

theorem hypOmegaGen_quotFamily (hΩ : HypOmegaGen Ω) (h2 : ∀ K ∈ Ω, IsPGroup 2 K)
    (hN : Odd (Nat.card N)) : HypOmegaGen (quotFamily Ω N) := by
  have hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(N ⊓ K)) := fun K _ => odd_natCard_inf hN K
  refine
    { conjInvariant := AscQuot.conjInvariant_quot hΩ.conjInvariant N
      omega1 := ?_
      omega2 := ?_
      omega3 := ?_
      omega4 := ?_
      omega5 := omega5_quot hΩ h2 hN }
  · rintro _ ⟨K, hK, rfl⟩
    exact CentQ.omega1_quot_gen hΩ N hXK hK
  · rintro _ ⟨K, hK, rfl⟩
    exact CentQ.omega2_quot_gen hΩ N hXK hK
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ P Q hP hQ
    exact CentQ.omega3_quot_gen hΩ N hXK hK hJ hP hQ
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne
    exact omega4_quot hΩ h2 hN hK hJ hne

end Family

section Fibres

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem le_of_map_le_of_commute (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : IsPGroup 2 K)
    (hJ : IsPGroup 2 J) (hc : ∀ k ∈ K, ∀ j ∈ J, k * j = j * k)
    (hle : K.map (QuotientGroup.mk' N) ≤ J.map (QuotientGroup.mk' N)) : K ≤ J := by
  intro k hk
  obtain ⟨j, hj, hjk⟩ := hle (Subgroup.mem_map_of_mem _ hk)
  have hkj : k = j := eq_of_commute_of_mem hN (two_elt hK hk) (two_elt hJ hj) (hc k hk j hj)
    (inv_mul_mem_of_mk_eq hjk.symm)
  exact hkj ▸ hj

theorem eq_of_map_eq_of_commute (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : IsPGroup 2 K)
    (hJ : IsPGroup 2 J) (hc : ∀ k ∈ K, ∀ j ∈ J, k * j = j * k)
    (h : K.map (QuotientGroup.mk' N) = J.map (QuotientGroup.mk' N)) : K = J :=
  le_antisymm (le_of_map_le_of_commute hN hK hJ hc h.le)
    (le_of_map_le_of_commute hN hJ hK (fun j hj k hk => (hc k hk j hj).symm) h.ge)

theorem eq_of_map_eq_of_twin (hΩ : HypOmegaGen Ω) (h2 : ∀ K ∈ Ω, IsPGroup 2 K)
    (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z)
    (h : K.map (QuotientGroup.mk' N) = J.map (QuotientGroup.mk' N)) : K = J := by
  by_contra hne
  exact hne (eq_of_map_eq_of_commute hN (h2 K hK) (h2 J hJ)
    (commutes_of_twin_pgroup hΩ h2 hK hJ hne hzK hzJ) h)

theorem exists_conj_of_map_eq (hΩ : HypOmegaGen Ω) (h2 : ∀ K ∈ Ω, IsPGroup 2 K)
    (hN : Odd (Nat.card N)) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : K.map (QuotientGroup.mk' N) = J.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, conjSub n J = K := by
  have hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(N ⊓ K)) := fun K _ => odd_natCard_inf hN K
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hz' := isUniqueInvolution_map_mk_of_odd (hXK K hK) hz
  have ht' := isUniqueInvolution_map_mk_of_odd (hXK J hJ) ht
  rw [h] at hz'
  obtain ⟨n, hn, hJ'Ω, hzJ', himg⟩ := exists_conj_member hΩ.conjInvariant hN hJ ht hz.sq
    (ht'.eq hz').symm
  exact ⟨n, hn, (eq_of_map_eq_of_twin hΩ h2 hN hK hJ'Ω hz hzJ' (h.trans himg.symm)).symm⟩

theorem twin_map (hΩ : HypOmegaGen Ω) (h2 : ∀ K ∈ Ω, IsPGroup 2 K) (hN : Odd (Nat.card N))
    {J K : Subgroup G} (hJ : J ∈ Ω) (hK : K ∈ twinSet Ω J) (hne : K ≠ J) :
    K.map (QuotientGroup.mk' N) ∈
        twinSet (quotFamily Ω N) (J.map (QuotientGroup.mk' N)) ∧
      K.map (QuotientGroup.mk' N) ≠ J.map (QuotientGroup.mk' N) := by
  have hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(N ⊓ K)) := fun K _ => odd_natCard_inf hN K
  obtain ⟨hKΩ, z, hzJ, hzK⟩ := hK
  refine ⟨⟨map_mem_quotFamily hKΩ, QuotientGroup.mk' N z,
    isUniqueInvolution_map_mk_of_odd (hXK J hJ) hzJ,
    isUniqueInvolution_map_mk_of_odd (hXK K hKΩ) hzK⟩, fun h => hne ?_⟩
  exact eq_of_map_eq_of_twin hΩ h2 hN hKΩ hJ hzK hzJ h

theorem exists_twin_of_map (hΩ : HypOmegaGen Ω) (hN : Odd (Nat.card N)) {J : Subgroup G} (hJ : J ∈ Ω) {M : Subgroup (G ⧸ N)}
    (hM : M ∈ twinSet (quotFamily Ω N) (J.map (QuotientGroup.mk' N)))
    (hne : M ≠ J.map (QuotientGroup.mk' N)) :
    ∃ K ∈ twinSet Ω J, K ≠ J ∧ K.map (QuotientGroup.mk' N) = M := by
  have hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(N ⊓ K)) := fun K _ => odd_natCard_inf hN K
  obtain ⟨⟨K₀, hK₀, rfl⟩, zb, hzbJ, hzbK⟩ := hM
  beta_reduce at hne hzbK ⊢
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK₀
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hz' := isUniqueInvolution_map_mk_of_odd (hXK K₀ hK₀) hz
  have ht' := isUniqueInvolution_map_mk_of_odd (hXK J hJ) ht
  have e1 : zb = QuotientGroup.mk' N t := hzbJ.eq ht'
  have e2 : zb = QuotientGroup.mk' N z := hzbK.eq hz'
  obtain ⟨n, hn, hKΩ, hzK, himg⟩ := exists_conj_member hΩ.conjInvariant hN hK₀ hz ht.sq
    (e1.symm.trans e2)
  refine ⟨conjSub n K₀, ⟨hKΩ, t, ht, hzK⟩, fun h => hne ?_, himg⟩
  rw [← himg, h]

end Fibres

section AEmptySec

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem exists_lift_USet (hΩ : HypOmegaGen Ω) (h2 : ∀ K ∈ Ω, IsPGroup 2 K)
    (hN : Odd (Nat.card N)) {J : Subgroup G} (hJ : J ∈ Ω) {Ub : Subgroup (G ⧸ N)}
    (hUb : Ub ∈ USet (quotFamily Ω N)) (hUbJ : Ub ≤ J.map (QuotientGroup.mk' N)) :
    ∃ U ∈ USet Ω, U ≤ J ∧ U.map (QuotientGroup.mk' N) = Ub := by
  set mk := QuotientGroup.mk' N with hmk
  have hq := hypOmegaGen_quotFamily hΩ h2 hN
  have hJN : J ⊓ N = ⊥ := inf_eq_bot_of_mem h2 hN hJ
  obtain ⟨Rb, hRb, Jb₁, hJb₁, hRbsyl, hUbRb, hcyc, hcard, h4⟩ :=
    Sec6Gen.exists_data_of_mem_USet hq hUb
  have hUb2 : IsPGroup 2 Ub := hRbsyl.2.1.to_le hUbRb
  have hJb : Jb₁ = J.map mk :=
    Sec6Gen.eq_of_le_of_le hq hJb₁ (map_mem_quotFamily hJ) hUb2 h4 (hUbRb.trans hRbsyl.1) hUbJ
  rw [hJb] at hRbsyl
  have hRbeq : J.map mk = Rb := hRbsyl.2.2 (J.map mk) le_rfl ((h2 J hJ).map mk) hRbsyl.1
  set U : Subgroup G := Ub.comap mk ⊓ J with hU
  have hUJ : U ≤ J := inf_le_right
  have hUN : U ⊓ N = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right N hUJ).trans hJN.le)
  have hUmap : U.map mk = Ub := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.1
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hUbJ hy
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
  have hUcard : Nat.card U = Nat.card Ub := by
    rw [← hUmap]
    exact Nat.card_congr (AscQuot.quotRestrictEquiv hUN).toEquiv
  have hUc : IsCyclic U := by
    have h1 : IsCyclic ↥(U.map mk) := hUmap ▸ hcyc
    exact (MulEquiv.isCyclic (AscQuot.quotRestrictEquiv hUN)).mpr h1
  have hJcard : Nat.card J = Nat.card Rb := by
    rw [← hRbeq]
    exact Nat.card_congr (AscQuot.quotRestrictEquiv hJN).toEquiv
  have hRcard : Nat.card J = 2 * Nat.card U := by rw [hJcard, hcard, hUcard]
  have hJJ : IsSylow2In J J := ⟨le_rfl, h2 J hJ, fun V' hV' _ hle => le_antisymm hV' hle⟩
  exact ⟨U, mem_USet_of_natCard hJ hJJ hUJ hUc hRcard, hUJ, hUmap⟩

theorem exists_conj_normalized (hN : Odd (Nat.card N)) {U K : Subgroup G} (hU : IsPGroup 2 U)
    (hK : IsPGroup 2 K)
    (hUn : ∀ u ∈ U, QuotientGroup.mk' N u ∈
      Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) :
    ∃ n ∈ N, U ≤ Subgroup.normalizer ((conjSub n K : Subgroup G) : Set G) := by
  set π := QuotientGroup.mk' N with hπ
  set D : Subgroup G := (K.map π).comap π with hD
  have hKD : K ≤ D := fun k hk => Subgroup.mem_map_of_mem _ hk
  have hmemD : ∀ x, x ∈ D ↔ π x ∈ K.map π := fun x => Iff.rfl
  have hUD : U ≤ Subgroup.normalizer (D : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemD, hmemD, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp (hUn u hu) (π x)
  have hBn : D ⊔ U ≤ Subgroup.normalizer (D : Set G) := sup_le Subgroup.le_normalizer hUD
  obtain ⟨P, hP, hUP⟩ := IsSylow2In.exists_ge hU (le_sup_right : U ≤ D ⊔ U)
  have hPD : IsSylow2In (P ⊓ D) D := isSylow2In_inf_of_le_normalizer hP le_sup_left hBn
  obtain ⟨V', hV', hKV'⟩ := IsSylow2In.exists_ge (hK) hKD
  have hcardV : Nat.card ↥(P ⊓ D) = Nat.card V' := hPD.natCard_eq hV'
  have hV2 : IsPGroup 2 ↥(P ⊓ D) := hPD.2.1
  have hVN : (P ⊓ D) ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hV2 le_rfl (odd_natCard_inf hN _)
  have hKN : K ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hK le_rfl (odd_natCard_inf hN _)
  have hle1 : Nat.card ↥(P ⊓ D) ≤ Nat.card K := by
    have h1 : Nat.card ↥((P ⊓ D).map π) = Nat.card ↥(P ⊓ D) :=
      (Nat.card_congr (AscQuot.quotRestrictEquiv hVN).toEquiv).symm
    have h2 : (P ⊓ D).map π ≤ K.map π := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    have h3 : Nat.card ↥(K.map π) = Nat.card K :=
      (Nat.card_congr (AscQuot.quotRestrictEquiv hKN).toEquiv).symm
    rw [← h1, ← h3]
    exact Subgroup.card_le_of_le h2
  have hle2 : Nat.card K ≤ Nat.card ↥(P ⊓ D) := hcardV ▸ Subgroup.card_le_of_le hKV'
  have hKnorm : K ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hVle : P ⊓ D ≤ N ⊔ K := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := hx.2
    have hnx : k⁻¹ * x ∈ N := inv_mul_mem_of_mk_eq hkx
    have : x = k * (k⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) (Subgroup.mem_sup_left hnx)
  obtain ⟨n, hn, hnK⟩ := Q3T7M.CentQ.exists_conjSub_of_le_sup_odd hKnorm hN hKN hK hV2
    (le_antisymm hle1 hle2) hVle
  refine ⟨n, hn, fun u hu => ?_⟩
  rw [hnK, Subgroup.mem_normalizer_iff]
  intro x
  have hxP : x ∈ P ↔ u * x * u⁻¹ ∈ P := by
    have hu' : u ∈ P := hUP hu
    constructor
    · intro hx; exact P.mul_mem (P.mul_mem hu' hx) (P.inv_mem hu')
    · intro hx
      have := P.mul_mem (P.mul_mem (P.inv_mem hu') hx) hu'
      simpa [mul_assoc] using this
  have hxD := Subgroup.mem_normalizer_iff.mp (hUD hu) x
  simp only [Subgroup.mem_inf] at hxD ⊢
  rw [hxP, hxD]

theorem aEmpty_quotFamily (hΩ : HypOmegaGen Ω) (h2 : ∀ K ∈ Ω, IsPGroup 2 K)
    (hN : Odd (Nat.card N)) (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    ∀ M ∈ quotFamily Ω N, AEmpty (quotFamily Ω N) M := by
  have hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(N ⊓ K)) := fun K _ => odd_natCard_inf hN K
  rintro _ ⟨K, hK, rfl⟩
  beta_reduce
  intro Jb hJbstar hJbnbr zKb zJb hzKb hzJb
  obtain ⟨J, hJ, rfl⟩ := hJbstar.1
  beta_reduce at hJbstar hJbnbr hzKb hzJb ⊢
  obtain ⟨-, hne, Ub, hUb, hUbJ, hUbN⟩ := hJbstar
  obtain ⟨U, hU, hUJ, hUmap⟩ := exists_lift_USet hΩ h2 hN hJ hUb hUbJ
  have hU2 : IsPGroup 2 U := (h2 J hJ).to_le hUJ
  obtain ⟨n, hn, hUnorm⟩ := exists_conj_normalized hN hU2 (h2 K hK)
    (fun u hu => hUbN (hUmap ▸ Subgroup.mem_map_of_mem _ hu))
  have himg := map_conjSub_of_mem hn K
  have hK'Ω : conjSub n K ∈ Ω := hΩ.conjInvariant n K hK
  have hJK' : J ≠ conjSub n K := fun h => hne (by rw [h, himg])
  have hstar : J ∈ omegaStarNbr Ω (conjSub n K) := ⟨hJ, hJK', U, hU, hUJ, hUnorm⟩
  have hnbr : J ∉ omegaNbr Ω (conjSub n K) := by
    intro h
    apply hJbnbr
    obtain ⟨-, -, T, hT, hTJ, hTN⟩ := h
    have hTsyl : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJ hT hTJ
    refine ⟨map_mem_quotFamily hJ, hne, T.map (QuotientGroup.mk' N),
      mem_RSet_of_isSylow2In (map_mem_quotFamily hJ)
        (Hall196.isSylow2In_map_hom (QuotientGroup.mk' N) hTsyl),
      Subgroup.map_mono hTJ, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have := mk_mem_normalizer_map (N := N) (hTN ht)
    rwa [himg] at this
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨zJ, hzJ⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have e1 : QuotientGroup.mk' N (n * z * n⁻¹) = zKb := by
    have hπn : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, map_mul, map_inv, hπn, one_mul, inv_one, mul_one]
    exact (hzKb.eq (isUniqueInvolution_map_mk_of_odd (hXK K hK) hz)).symm
  have e2 : QuotientGroup.mk' N zJ = zJb :=
    (hzJb.eq (isUniqueInvolution_map_mk_of_odd (hXK J hJ) hzJ)).symm
  obtain ⟨g, hg, hgK⟩ := hA _ hK'Ω J hstar hnbr (n * z * n⁻¹) zJ (hz.conj n) hzJ
  refine ⟨QuotientGroup.mk' N g, ?_, ?_⟩
  · have h3 := map_pairNormalizers_le (N := N) (conjSub n K) J (n * z * n⁻¹) zJ
      (Subgroup.mem_map_of_mem _ hg)
    rwa [himg, e1, e2] at h3
  · have h3 := congrArg (Subgroup.map (QuotientGroup.mk' N)) hgK
    rw [AscQuot.map_conjSub, himg] at h3
    exact h3

end AEmptySec
end OddQuot

section Datum

variable {Y : Type} [Group Y]

theorem tightCore_eq_self_of_isPGroup {R : Subgroup Y} (hR : IsPGroup 2 R) : tightCore R = R := by
  refine le_antisymm (tightCore_le R) fun x hx => ?_
  exact Subgroup.subset_closure ⟨hx, hR.to_le (Subgroup.zpowers_le.mpr hx)⟩

theorem sylow_eq_top {R : Subgroup Y} (hR : IsPGroup 2 R) (S : Sylow 2 R) :
    (S : Subgroup R) = ⊤ := by
  have h : IsPGroup 2 (⊤ : Subgroup R) := hR.of_equiv Subgroup.topEquiv.symm
  exact (S.is_maximal' h le_top).symm

theorem q8TwinDatum_of_isPGroup [Finite Y] {R : Subgroup Y} (hR : IsPGroup 2 R) (S : Sylow 2 R)
    {t : Y} (ht : IsUniqueInvolution R t) (hq8 : Nonempty (↥R ≃* QuaternionGroup 2)) :
    Q8TwinDatum R S t ∧ Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) := by
  have hS := sylow_eq_top hR S
  let e : ↥(S : Subgroup R) ≃* ↥R :=
    (MulEquiv.subgroupCongr hS).trans Subgroup.topEquiv
  have hq : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) := ⟨e.trans hq8.some⟩
  refine ⟨⟨⟨3, le_rfl, hq⟩, ?_, ?_, ?_, ?_⟩, hq⟩
  · have : (⟨t, ht.mem⟩ : R) ∈ (S : Subgroup R) := by rw [hS]; exact Subgroup.mem_top _
    exact ⟨⟨t, ht.mem⟩, this, rfl⟩
  · exact orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
  · intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (ht.commute_of_mem hw).symm
  · exact hR.to_quotient _

end Datum

section Outcome

variable {Y : Type} [Group Y]

@[expose] def HasTwin (R : Subgroup Y) : Prop :=
  ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R

end Outcome

section Restrict

variable {G : Type} [Group G] [Finite G]

theorem USet_mono {P Ω : Set (Subgroup G)} (h : P ⊆ Ω) : USet P ⊆ USet Ω := by
  rintro U ⟨R, ⟨J, hJ, S, rfl⟩, hUR, hcyc, hidx⟩
  exact ⟨_, ⟨J, h hJ, S, rfl⟩, hUR, hcyc, hidx⟩

theorem hypOmegaGen_sub {Λ Λ' : Set (Subgroup G)} (hΛ : HypOmegaGen Λ) (hsub : Λ' ⊆ Λ)
    (hinv : ConjInvariant Λ') : HypOmegaGen Λ' where
  conjInvariant := hinv
  omega1 K hK := hΛ.omega1 K (hsub hK)
  omega2 K hK := hΛ.omega2 K (hsub hK)
  omega3 K hK J hJ := hΛ.omega3 K (hsub hK) J (hsub hJ)
  omega4 K hK J hJ := hΛ.omega4 K (hsub hK) J (hsub hJ)
  omega5 K hK J hJ := hΛ.omega5 K (hsub hK) J (hsub hJ)

theorem aEmpty_restrictFamily {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) {X K : Subgroup G}
    (hKX : K ≤ X) (hA : AEmpty Ω K) : AEmpty (restrictFamily P X) (K.subgroupOf X) := by
  intro J' hJ'star hJ'nbr zK' zJ' hzK' hzJ'
  set J : Subgroup G := J'.map X.subtype with hJdef
  have hJ'eq : J.subgroupOf X = J' := subgroupOf_map_subtype' J'
  have hJX : J ≤ X := Subgroup.map_subtype_le J'
  have hJP : J ∈ P := mem_restrictFamily_iff.mp hJ'star.1
  have hstarP : J ∈ omegaStarNbr P K := omegaStarNbr_of_restrict hKX hJX (by rwa [hJ'eq])
  have hstar : J ∈ omegaStarNbr Ω K := by
    obtain ⟨-, hne, U, hU, hUJ, hUN⟩ := hstarP
    exact ⟨hPΩ hJP, hne, U, USet_mono hPΩ hU, hUJ, hUN⟩
  have hnbr : J ∉ omegaNbr Ω K := by
    intro h
    apply hJ'nbr
    rw [← hJ'eq]
    obtain ⟨-, hne, T, hT, hTJ, hTN⟩ := h
    have hTs : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ (hPΩ hJP) hT hTJ
    have hTJ' : T = J := (hTs.2.2 J le_rfl (h2 J (hPΩ hJP)) hTJ).symm
    have hJN : J ≤ Subgroup.normalizer (K : Set G) := hTJ' ▸ hTN
    have hJ'2 : IsPGroup 2 ↥(J.subgroupOf X) := (h2 J (hPΩ hJP)).comap_subtype
    have hJJ : IsSylow2In (J.subgroupOf X) (J.subgroupOf X) :=
      ⟨le_rfl, hJ'2, fun V' hV' _ hle => le_antisymm hV' hle⟩
    refine ⟨subgroupOf_mem_restrictFamily hJP hJX, subgroupOf_ne_of_ne hKX hJX hne,
      J.subgroupOf X, mem_RSet_of_isSylow2In (subgroupOf_mem_restrictFamily hJP hJX) hJJ, le_rfl,
      fun x hx => ?_⟩
    exact (mem_normalizer_subgroupOf_iff hKX).mp (hJN (Subgroup.mem_subgroupOf.mp hx))
  have hzK : IsUniqueInvolution K (zK' : G) := isUniqueInvolution_of_subgroupOf hzK' hKX
  have hzJ : IsUniqueInvolution J (zJ' : G) :=
    isUniqueInvolution_of_subgroupOf (by rwa [hJ'eq]) hJX
  obtain ⟨g, hg, hgK⟩ := hA J hstar hnbr _ _ hzK hzJ
  set Z' : Subgroup X := Subgroup.closure ({zK', zJ'} : Set X) with hZ'
  have hZ : Z'.map X.subtype = Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :=
    map_closure_pair_subtype zK' zJ'
  have hZX : Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) ≤ X := by
    rw [← hZ]; exact Subgroup.map_subtype_le _
  have hgX : g ∈ X := by
    have : pairNormalizers K J (zK' : G) (zJ' : G) ≤ X := by
      unfold pairNormalizers
      exact sup_le (inf_le_left.trans hKX) (inf_le_left.trans hJX)
    exact this hg
  have hN : ∀ {A : Subgroup G}, A ≤ X →
      (A ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
        Subgroup G) : Set G)).subgroupOf X ≤
        A.subgroupOf X ⊓ Subgroup.normalizer ((Z' : Subgroup X) : Set X) := by
    intro A hAX x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hx.1, ?_⟩
    have := (mem_normalizer_subgroupOf_iff hZX).mp hx.2
    rwa [← hZ, subgroupOf_map_subtype'] at this
  have hAX : K ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
      Subgroup G) : Set G) ≤ X := inf_le_left.trans hKX
  have hBX : J ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
      Subgroup G) : Set G) ≤ X := inf_le_left.trans hJX
  have hmem : (⟨g, hgX⟩ : X) ∈ (pairNormalizers K J (zK' : G) (zJ' : G)).subgroupOf X :=
    Subgroup.mem_subgroupOf.mpr hg
  have hmem' : (⟨g, hgX⟩ : X) ∈ pairNormalizers (K.subgroupOf X) J' zK' zJ' := by
    have h1 := hmem
    unfold pairNormalizers at h1
    rw [Subgroup.subgroupOf_sup hAX hBX] at h1
    have h2' := hN (A := K) hKX
    have h3 := hN (A := J) hJX
    rw [hJ'eq] at h3
    exact sup_le_sup h2' h3 h1
  refine ⟨⟨g, hgX⟩, hmem', ?_⟩
  rw [conjSub_subgroupOf X ⟨g, hgX⟩ K]
  show (conjSub g K).subgroupOf X = J'
  rw [hgK]
  exact hJ'eq

end Restrict

section SectionOutcomeDef

variable {G : Type} [Group G]

abbrev SecQuot (X : Subgroup G) : Type := ↥X ⧸ classicalInvolutionOddCore ↥X

@[expose] noncomputable def secImage (X J : Subgroup G) : Subgroup (SecQuot X) :=
  (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X))

@[expose] noncomputable def secInv (X : Subgroup G) (t : X) : SecQuot X :=
  QuotientGroup.mk' (classicalInvolutionOddCore ↥X) t

end SectionOutcomeDef

section Main

variable {G : Type} [Group G] [Finite G]

theorem restrictFamily_conjFamily {J X : Subgroup G} (hJX : J ≤ X) :
    restrictFamily {L | ∃ x : X, conjSub (x : G) J = L} X =
      CoreAssembly.conjClass (J.subgroupOf X) := by
  ext L'
  constructor
  · rintro ⟨L, ⟨x, rfl⟩, -, rfl⟩
    exact ⟨x, conjSub_subgroupOf X x J⟩
  · rintro ⟨g, rfl⟩
    refine ⟨conjSub (g : G) J, ⟨g, rfl⟩, ?_, conjSub_subgroupOf X g J⟩
    have := conjSub_mono (n := (g : G)) hJX
    rwa [conjSub_eq_self_of_mem g.2] at this

theorem conjFamily_subset {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {J : Subgroup G}
    (hJ : J ∈ Ω) (X : Subgroup G) : {L | ∃ x : X, conjSub (x : G) J = L} ⊆ Ω := by
  rintro _ ⟨x, rfl⟩
  exact hΩ (x : G) J hJ

theorem hypOmegaGen_conjClass_section {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {J : Subgroup G}
    (hJ : J ∈ Ω) {X : Subgroup G} (hJX : J ≤ X) :
    HypOmegaGen (CoreAssembly.conjClass (J.subgroupOf X)) := by
  have hfam := restrictFamily_conjFamily hJX
  refine hypOmegaGen_sub (hypOmegaGen_restrict hΩ X) ?_ (Q3B.conjInvariant_conjClass _)
  rw [← hfam]
  rintro _ ⟨L, hL, hLX, rfl⟩
  exact ⟨L, conjFamily_subset hΩ.conjInvariant hJ X hL, hLX, rfl⟩

theorem aEmpty_conjClass_section {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ K ∈ Ω, IsPGroup 2 K) {J : Subgroup G} (hJ : J ∈ Ω) (hA : AEmpty Ω J)
    {X : Subgroup G} (hJX : J ≤ X) :
    AEmpty (CoreAssembly.conjClass (J.subgroupOf X)) (J.subgroupOf X) := by
  rw [← restrictFamily_conjFamily hJX]
  exact aEmpty_restrictFamily hΩ h2 (conjFamily_subset hΩ.conjInvariant hJ X) hJX hA

theorem hasTwin_secImage_iff {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ K ∈ Ω, IsPGroup 2 K) {J : Subgroup G} (hJ : J ∈ Ω) {X : Subgroup G} (hJX : J ≤ X) :
    HasTwin (secImage X J) ↔
      ∃ K ∈ twinSet {L | ∃ x : X, conjSub (x : G) J = L} J, K ≠ J := by
  have hfam := restrictFamily_conjFamily hJX
  have hΔ := hypOmegaGen_conjClass_section hΩ hJ hJX
  have hNodd := CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hmem2 : ∀ K ∈ CoreAssembly.conjClass (J.subgroupOf X), IsPGroup 2 K := by
    rintro _ ⟨g, rfl⟩
    exact isPGroup_conjSub g (h2 J hJ).comap_subtype
  have hqf : quotFamily (CoreAssembly.conjClass (J.subgroupOf X))
      (classicalInvolutionOddCore ↥X) = CoreAssembly.conjClass (secImage X J) :=
    image_conjClass (N := classicalInvolutionOddCore ↥X) (J.subgroupOf X)
  have htc : tightCore (secImage X J) = secImage X J :=
    tightCore_eq_self_of_isPGroup ((h2 J hJ).comap_subtype.map _)
  have hmemJ := CoreAssembly.mem_conjClass_self (J.subgroupOf X)
  unfold HasTwin
  rw [htc]
  constructor
  · rintro ⟨M, hM, hne⟩
    rw [← hqf] at hM
    obtain ⟨K, ⟨hKc, z, hzJ, hzK⟩, hKne, -⟩ :=
      OddQuot.exists_twin_of_map hΔ hNodd hmemJ hM hne
    rw [← hfam] at hKc
    obtain ⟨L, hLP, hLX, rfl⟩ := hKc
    exact ⟨L, ⟨hLP, (z : G), isUniqueInvolution_of_subgroupOf hzJ hJX,
      isUniqueInvolution_of_subgroupOf hzK hLX⟩, fun h => hKne (by rw [h])⟩
  · rintro ⟨L, ⟨hLP, z, hzJ, hzL⟩, hne⟩
    have hLX : L ≤ X := by
      obtain ⟨x, rfl⟩ := hLP
      have := conjSub_mono (n := (x : G)) hJX
      rwa [conjSub_eq_self_of_mem x.2] at this
    have hK : L.subgroupOf X ∈ twinSet (CoreAssembly.conjClass (J.subgroupOf X))
        (J.subgroupOf X) := by
      refine ⟨?_, ⟨z, hJX hzJ.mem⟩, isUniqueInvolution_subgroupOf hzJ hJX,
        isUniqueInvolution_subgroupOf hzL hLX⟩
      rw [← hfam]
      exact ⟨L, hLP, hLX, rfl⟩
    obtain ⟨hm, hne'⟩ := OddQuot.twin_map hΔ hmem2 hNodd hmemJ hK
      (subgroupOf_ne_of_ne hJX hLX hne)
    exact ⟨_, by rw [← hqf]; exact hm, hne'⟩

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
