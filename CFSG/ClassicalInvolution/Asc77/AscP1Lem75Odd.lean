module

public import CFSG.ClassicalInvolution.Asc77.AscT7BFuse23

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace T75

variable {G : Type} [Group G]

omit [Group G] in
theorem two_pow_coprime_of_odd {a b : ℕ} (hb : Odd b) : Nat.Coprime (2 ^ a) b :=
  Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hb)

theorem isPGroup_zpowers_of_pow_two_pow {x : G} {a : ℕ} (h : x ^ (2 ^ a) = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have hd : orderOf x ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])

theorem mem_of_mem_normalizer [Finite G] {K R : Subgroup G} (hR : IsSylow2In R K) {t : G}
    (htK : t ∈ K) (htN : t ∈ Subgroup.normalizer (R : Set G))
    (ht : IsPGroup 2 (Subgroup.zpowers t)) : t ∈ R := by
  set N : Subgroup G := K ⊓ Subgroup.normalizer (R : Set G) with hN
  have hRN : IsSylow2In R N :=
    ⟨le_inf hR.1 Subgroup.le_normalizer, hR.2.1, fun T hTN hT2 hle =>
      hR.2.2 T (hTN.trans inf_le_left) hT2 hle⟩
  have htN' : Subgroup.zpowers t ≤ N := Subgroup.zpowers_le.mpr ⟨htK, htN⟩
  obtain ⟨V, hV, htV⟩ := IsSylow2In.exists_ge ht htN'
  obtain ⟨x, hx, hxV⟩ := Thompson.exists_conj_of_isSylow2In hRN hV
  have hxR : conjSub x R = R := mem_normalizer_iff_conjSub_eq.mp hx.2
  rw [hxR] at hxV
  rw [hxV]
  exact htV (Subgroup.mem_zpowers t)

theorem exists_odd_pow [Finite G] {K R : Subgroup G} (hR : IsSylow2In R K) {k : G}
    (hkK : k ∈ K) (hkN : k ∈ Subgroup.normalizer (R : Set G)) :
    ∃ m : ℕ, Odd (orderOf (k ^ m)) ∧ (k ^ m)⁻¹ * k ∈ R := by
  have hpos : 0 < orderOf k := orderOf_pos k
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  obtain ⟨m, hm0, hm1⟩ := Nat.chineseRemainder (two_pow_coprime_of_odd (a := a) hb) 0 1
  have h2m : 2 ^ a ∣ m := (Nat.modEq_zero_iff_dvd).mp hm0
  refine ⟨m, ?_, ?_⟩
  · have hdvd : orderOf k ∣ m * b := by
      rw [hab]
      exact Nat.mul_dvd_mul_right h2m b
    have h1 : (k ^ m) ^ b = 1 := by
      rw [← pow_mul]
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    exact hb.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  · obtain ⟨j, hj⟩ : (b : ℤ) ∣ (1 : ℤ) - m := (Nat.modEq_iff_dvd).mp hm1
    have hkb : k ^ b ∈ R := by
      refine mem_of_mem_normalizer hR (K.pow_mem hkK b)
        ((Subgroup.normalizer (R : Set G)).pow_mem hkN b) ?_
      refine isPGroup_zpowers_of_pow_two_pow (a := a) ?_
      rw [← pow_mul, mul_comm, ← hab]
      exact pow_orderOf_eq_one k
    have e : (k ^ m)⁻¹ * k = (k ^ b) ^ j := by
      calc (k ^ m)⁻¹ * k = k ^ ((1 : ℤ) - m) := by
            rw [sub_eq_neg_add, zpow_add, zpow_neg, zpow_natCast, zpow_one]
        _ = (k ^ b) ^ j := by rw [hj, zpow_mul, zpow_natCast]
    rw [e]
    exact R.zpow_mem hkb j

theorem conjSub_eq_of_natCard_eq_two_mul [Finite G] {R U : Subgroup G} (hUR : U ≤ R)
    (hcard : Nat.card R = 2 * Nat.card U) {r : G} (hr : r ∈ R) : conjSub r U = U := by
  have hrel : U.relIndex R = 2 := by
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR, hcard] at h1
    have hU0 : 0 < Nat.card U := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hU0 h1
  have hidx : (U.subgroupOf R).index = 2 := hrel
  have hN : (U.subgroupOf R).Normal := Subgroup.normal_of_index_eq_two hidx
  have key : ∀ s ∈ R, ∀ x ∈ U, s * x * s⁻¹ ∈ U := by
    intro s hs x hx
    have h1 : (⟨x, hUR hx⟩ : ↥R) ∈ U.subgroupOf R := hx
    exact hN.conj_mem _ h1 ⟨s, hs⟩
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have := key r hr _ hx
    simpa [mul_assoc] using this
  · intro hx
    have := key r⁻¹ (R.inv_mem hr) x hx
    simpa [mul_assoc] using this

theorem exists_gen_sq_eq [Finite G] {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    {V : Subgroup G} (hVK : V ≤ K) (hc : IsCyclic ↥V) (h4 : Nat.card V = 4) :
    ∃ a ∈ V, a * a = z ∧ ∀ v ∈ V, ∃ j : ℤ, v = a ^ j := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥V)
  have hord : orderOf g = Nat.card V := orderOf_eq_card_of_forall_mem_zpowers hg
  have hord' : orderOf (g : G) = 4 := by rw [Subgroup.orderOf_coe, hord, h4]
  refine ⟨(g : G), g.2, T7B.mul_self_eq_of_orderOf_four hz (hVK g.2) hord', fun v hv => ?_⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨v, hv⟩)
  exact ⟨j, by simpa using (congrArg Subtype.val hj).symm⟩

theorem exists_odd_normalizer_conj {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)} [Finite G]
    (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {R V U : Subgroup G} (hR : IsSylow2In R K) (hVR : V ≤ R)
    (hUR : U ≤ R) (hcV : IsCyclic ↥V) (hcU : IsCyclic ↥U) (hV4 : Nat.card V = 4)
    (hU4 : Nat.card U = 4) (hR8 : Nat.card R = 8) :
    ∃ y ∈ K, y ∈ Subgroup.normalizer (R : Set G) ∧ Odd (orderOf y) ∧ conjSub y V = U := by
  have hVK : V ≤ K := hVR.trans hR.1
  have hUK : U ≤ K := hUR.trans hR.1
  obtain ⟨a, haV, ha2, hagen⟩ := exists_gen_sq_eq hz hVK hcV hV4
  obtain ⟨x, hxU, hx2, hxgen⟩ := exists_gen_sq_eq hz hUK hcU hU4
  obtain ⟨k, hkK, hk⟩ := T7B.exists_conj_of_sq_eq hp hΩ hK hz (hVK haV) (hUK hxU) ha2 hx2
  have hVk : conjSub k V = U := by
    have hle : conjSub k V ≤ U := by
      intro w hw
      rw [mem_conjSub_iff] at hw
      obtain ⟨j, hj⟩ := hagen _ hw
      have hw' : w = k * (k⁻¹ * w * k) * k⁻¹ := by group
      rw [hw', hj]
      have : k * a ^ j * k⁻¹ = x ^ j := by
        rw [← hk]
        simp [conj_zpow]
      rw [this]
      exact U.zpow_mem hxU j
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [AscL62.natCard_conjSub, hU4, hV4])
  have hRV : ∀ r ∈ R, conjSub r V = V := fun r hr =>
    conjSub_eq_of_natCard_eq_two_mul hVR (by omega) hr
  have hRU : ∀ r ∈ R, conjSub r U = U := fun r hr =>
    conjSub_eq_of_natCard_eq_two_mul hUR (by omega) hr
  set H : Subgroup G := K ⊓ Subgroup.normalizer (U : Set G) with hH
  have hRH : R ≤ H := le_inf hR.1 fun r hr => mem_normalizer_iff_conjSub_eq.mpr (hRU r hr)
  have hkR : IsSylow2In (conjSub k R) K := by
    have := IsSylow2In.conj hR k
    rwa [conjSub_eq_self_of_mem hkK] at this
  have hkRH : conjSub k R ≤ H := by
    refine le_inf hkR.1 fun w hw => mem_normalizer_iff_conjSub_eq.mpr ?_
    have hr : k⁻¹ * w * k ∈ R := (mem_conjSub_iff).mp hw
    have hw' : w = k * (k⁻¹ * w * k) * k⁻¹ := by group
    calc conjSub w U = conjSub (k * (k⁻¹ * w * k) * k⁻¹) U := by rw [← hw']
      _ = conjSub k (conjSub (k⁻¹ * w * k) (conjSub k⁻¹ U)) := by rw [conjSub_mul, conjSub_mul]
      _ = conjSub k (conjSub (k⁻¹ * w * k) V) := by rw [← hVk, conjSub_inv_conjSub]
      _ = conjSub k V := by rw [hRV _ hr]
      _ = U := hVk
  have hRsyl : IsSylow2In R H :=
    ⟨hRH, hR.2.1, fun T hTH hT2 hle => hR.2.2 T (hTH.trans inf_le_left) hT2 hle⟩
  have hkRsyl : IsSylow2In (conjSub k R) H :=
    ⟨hkRH, hkR.2.1, fun T hTH hT2 hle => hkR.2.2 T (hTH.trans inf_le_left) hT2 hle⟩
  obtain ⟨n, hnH, hn⟩ := Thompson.exists_conj_of_isSylow2In hRsyl hkRsyl
  have hnU : conjSub n⁻¹ U = U := by
    have h1 : conjSub n U = U := mem_normalizer_iff_conjSub_eq.mp hnH.2
    have h2 := congrArg (conjSub n⁻¹) h1
    rw [conjSub_inv_conjSub] at h2
    exact h2.symm
  set k' : G := n⁻¹ * k with hk'
  have hk'K : k' ∈ K := K.mul_mem (K.inv_mem hnH.1) hkK
  have hk'R : conjSub k' R = R := by
    rw [hk', conjSub_mul, ← hn, conjSub_inv_conjSub]
  have hk'V : conjSub k' V = U := by
    rw [hk', conjSub_mul, hVk, hnU]
  obtain ⟨m, hmodd, hmR⟩ := exists_odd_pow hR hk'K (mem_normalizer_iff_conjSub_eq.mpr hk'R)
  refine ⟨k' ^ m, K.pow_mem hk'K m,
    (Subgroup.normalizer (R : Set G)).pow_mem (mem_normalizer_iff_conjSub_eq.mpr hk'R) m,
    hmodd, ?_⟩
  have hy : k' ^ m = k' * ((k' ^ m)⁻¹ * k')⁻¹ := by group
  rw [hy, conjSub_mul, hRV _ (R.inv_mem hmR), hk'V]

theorem odd_orderOf_conj {n : G} (v : G) (h : Odd (orderOf n)) : Odd (orderOf (v * n * v⁻¹)) := by
  have := orderOf_injective (MulAut.conj v).toMonoidHom (MulAut.conj v).injective n
  simpa using this ▸ h

theorem eq_one_or_eq_of_centralizes [Finite G] {K R : Subgroup G} {z : G} (hR : IsSylow2In R K)
    (hZ : ∀ x ∈ R, (∀ r ∈ R, r * x = x * r) → x = 1 ∨ x = z) {c : G} (hcK : c ∈ K)
    (hcC : ∀ r ∈ R, r * c = c * r) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) : c = 1 ∨ c = z := by
  have hcN : c ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.centralizer_le_normalizer (R : Set G) (Subgroup.mem_centralizer_iff.mpr hcC)
  exact hZ c (mem_of_mem_normalizer hR hcK hcN hc2) hcC

theorem natCard_centralizer_eq [Finite G] {K R : Subgroup G} {z : G} (hR : IsSylow2In R K)
    (hzR : z ∈ R) (hzsq : z * z = 1) (hz1 : z ≠ 1) (hzK : ∀ w ∈ K, w * z = z * w)
    (hZ : ∀ x ∈ R, (∀ r ∈ R, r * x = x * r) → x = 1 ∨ x = z) :
    ∃ m : ℕ, Odd m ∧ Nat.card ↥(Subgroup.centralizer (R : Set G) ⊓ K) = 2 * m := by
  set C : Subgroup G := Subgroup.centralizer (R : Set G) ⊓ K with hC
  have hzC : z ∈ C := by
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun r hr => ?_, hR.1 hzR⟩
    exact hzK r (hR.1 hr)
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzsq) hz1
  have hzC2 : IsSylow2In (Subgroup.zpowers z) C := by
    refine ⟨Subgroup.zpowers_le.mpr hzC, isPGroup_zpowers_of_mul_self_eq_one hzsq hz1,
      fun V' hV'C hV'2 hle => ?_⟩
    refine le_antisymm (fun v hv => ?_) hle
    have hv2 : IsPGroup 2 (Subgroup.zpowers v) := hV'2.to_le (Subgroup.zpowers_le.mpr hv)
    have hvC := hV'C hv
    rcases eq_one_or_eq_of_centralizes hR hZ hvC.2 (fun r hr => Subgroup.mem_centralizer_iff.mp
      hvC.1 r hr) hv2 with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  have hQ : Nat.card ↥(Q : Subgroup ↥C) = 2 ^ (Nat.card ↥C).factorization 2 :=
    Sylow.card_eq_multiplicity Q
  have hc : Nat.card ↥((Q : Subgroup ↥C).map C.subtype) = Nat.card ↥(Q : Subgroup ↥C) :=
    (Nat.card_congr ((Q : Subgroup ↥C).equivMapOfInjective C.subtype
      C.subtype_injective).toEquiv).symm
  have hzQ : Nat.card (Subgroup.zpowers z) = Nat.card ↥((Q : Subgroup ↥C).map C.subtype) :=
    hzC2.natCard_eq (isSylow2In_map_sylow C Q)
  have hfac : (Nat.card C).factorization 2 = 1 := by
    rw [Nat.card_zpowers, hzord, hc, hQ] at hzQ
    exact (Nat.pow_right_injective (le_refl 2) (by simpa using hzQ.symm))
  have hne : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hdvd : 2 ∣ Nat.card C := by
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne (k := 1)).mpr hfac.ge
    simpa using this
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨m, ?_, hm⟩
  by_contra hodd
  have hev : 2 ∣ m := by
    rcases Nat.even_or_odd m with h | h
    · exact even_iff_two_dvd.mp h
    · exact absurd h hodd
  have h4 : 2 ^ 2 ∣ Nat.card C := by
    obtain ⟨m', hm'⟩ := hev
    exact ⟨m', by rw [hm, hm']; ring⟩
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp h4
  omega

theorem exists_fixed_odd_conj [Finite G] {K R : Subgroup G} {z : G} (hR : IsSylow2In R K)
    (hzR : z ∈ R) (hzsq : z * z = 1) (hz1 : z ≠ 1) (hzK : ∀ w ∈ K, w * z = z * w)
    (hZ : ∀ x ∈ R, (∀ r ∈ R, r * x = x * r) → x = 1 ∨ x = z) {y : G} (hyK : y ∈ K)
    (hyN : y ∈ Subgroup.normalizer (R : Set G)) (hyodd : Odd (orderOf y)) {P : Subgroup G}
    (hP : IsPGroup 2 ↥P) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hPR : P ≤ Subgroup.centralizer (R : Set G)) :
    ∃ y' ∈ K, y' ∈ Subgroup.normalizer (R : Set G) ∧ Odd (orderOf y') ∧
      (∀ r ∈ R, y' * r * y'⁻¹ = y * r * y⁻¹) ∧ ∀ x ∈ P, x * y' = y' * x := by
  set C : Subgroup G := Subgroup.centralizer (R : Set G) ⊓ K with hC
  obtain ⟨m, hmodd, hCcard⟩ := natCard_centralizer_eq hR hzR hzsq hz1 hzK hZ
  have hyR : ∀ r ∈ R, y * r * y⁻¹ ∈ R := fun r hr => (Subgroup.mem_normalizer_iff.mp hyN r).mp hr
  have hzC : z ∈ C := by
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun r hr => ?_, hR.1 hzR⟩
    exact hzK r (hR.1 hr)
  have hzcomm : ∀ n ∈ K, n * z = z * n := hzK
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hzsq
  have hCsq : ∀ c ∈ C, c * c = 1 → c = 1 ∨ c = z := by
    intro c hc hc2
    by_cases hc1 : c = 1
    · exact Or.inl hc1
    · exact eq_one_or_eq_of_centralizes hR hZ hc.2
        (fun r hr => Subgroup.mem_centralizer_iff.mp hc.1 r hr)
        (isPGroup_zpowers_of_mul_self_eq_one hc2 hc1)
  set Sa : Set G := (fun c => y * c) '' (C : Set G) with hSa
  set So : Set G := {n | n ∈ Sa ∧ Odd (orderOf n)} with hSo
  have hSaK : ∀ n ∈ Sa, n ∈ K := by
    rintro _ ⟨c, hc, rfl⟩
    exact K.mul_mem hyK hc.2
  have hSaact : ∀ n ∈ Sa, ∀ r ∈ R, n * r * n⁻¹ = y * r * y⁻¹ := by
    rintro _ ⟨c, hc, rfl⟩ r hr
    have h1 : c * r = r * c := (Subgroup.mem_centralizer_iff.mp hc.1 r hr).symm
    calc y * c * r * (y * c)⁻¹ = y * (c * r * c⁻¹) * y⁻¹ := by group
      _ = y * r * y⁻¹ := by rw [h1]; group
  have hSaN : ∀ n ∈ Sa, n ∈ Subgroup.normalizer (R : Set G) := by
    intro n hn
    have hle : conjSub n R ≤ R := by
      intro w hw
      have hr : n⁻¹ * w * n ∈ R := (mem_conjSub_iff).mp hw
      have e : w = n * (n⁻¹ * w * n) * n⁻¹ := by group
      rw [e, hSaact n hn _ hr]
      exact hyR _ hr
    exact mem_normalizer_iff_conjSub_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hle (by rw [AscL62.natCard_conjSub]))
  have hSaz : ∀ n ∈ Sa, n * z ∈ Sa := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c * z, C.mul_mem hc hzC, by group⟩
  have hpowact : ∀ n ∈ Sa, ∀ j : ℕ, ∀ r ∈ R, n ^ j * r * (n ^ j)⁻¹ = y ^ j * r * (y ^ j)⁻¹ := by
    intro n hn j
    induction j with
    | zero => intro r hr; simp
    | succ j ih =>
      intro r hr
      have hyj : y ^ j * r * (y ^ j)⁻¹ ∈ R := by
        have := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (R : Set G)).pow_mem hyN j) r).mp hr
        exact this
      calc n ^ (j + 1) * r * (n ^ (j + 1))⁻¹
          = n * (n ^ j * r * (n ^ j)⁻¹) * n⁻¹ := by group
        _ = n * (y ^ j * r * (y ^ j)⁻¹) * n⁻¹ := by rw [ih r hr]
        _ = y * (y ^ j * r * (y ^ j)⁻¹) * y⁻¹ := hSaact n hn _ hyj
        _ = y ^ (j + 1) * r * (y ^ (j + 1))⁻¹ := by group
  have hclaim : ∀ n ∈ Sa, Odd (orderOf n) ∨ Odd (orderOf (n * z)) := by
    intro n hn
    have hnC : n ^ orderOf y ∈ C := by
      refine ⟨Subgroup.mem_centralizer_iff.mpr fun r hr => ?_, K.pow_mem (hSaK n hn) _⟩
      have := hpowact n hn (orderOf y) r hr
      rw [pow_orderOf_eq_one y] at this
      simp only [one_mul, inv_one, mul_one] at this
      calc r * n ^ orderOf y = n ^ orderOf y * r * (n ^ orderOf y)⁻¹ * n ^ orderOf y := by
            rw [this]
        _ = n ^ orderOf y * r := inv_mul_cancel_right _ _
    set e := orderOf y with he
    have hw : (n ^ e) ^ m ∈ C := C.pow_mem hnC m
    have hw2 : (n ^ e) ^ m * (n ^ e) ^ m = 1 := by
      have h1 : orderOf (n ^ e) ∣ 2 * m := hCcard ▸ Subgroup.orderOf_dvd_natCard C hnC
      have h2 : (n ^ e) ^ (2 * m) = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
      rw [← pow_add, ← two_mul, mul_comm 2 m, pow_mul]
      calc ((n ^ e) ^ m) ^ 2 = (n ^ e) ^ (m * 2) := by rw [pow_mul]
        _ = 1 := by rw [mul_comm]; exact h2
    have hem : Odd (e * m) := hyodd.mul hmodd
    have hcomm : Commute n z := hzcomm n (hSaK n hn)
    rcases hCsq _ hw hw2 with h | h
    · left
      have h1 : n ^ (e * m) = 1 := by rw [pow_mul]; exact h
      exact hem.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
    · right
      have h1 : (n * z) ^ (e * m) = 1 := by
        rw [hcomm.mul_pow, pow_mul, h]
        obtain ⟨k, hk⟩ := hem
        rw [hk, pow_succ, pow_mul, hz2, one_pow, one_mul, hzsq]
      exact hem.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  have hnotboth : ∀ n ∈ Sa, ¬ (Odd (orderOf n) ∧ Odd (orderOf (n * z))) := by
    rintro n hn ⟨⟨o, ho⟩, ⟨o', ho'⟩⟩
    have hcomm : Commute n z := hzcomm n (hSaK n hn)
    have hn1 : n ^ (2 * o + 1) = 1 := by rw [← ho]; exact pow_orderOf_eq_one n
    have hn2 : (n * z) ^ (2 * o' + 1) = 1 := by rw [← ho']; exact pow_orderOf_eq_one _
    have hzpow : ∀ k : ℕ, z ^ (2 * k + 1) = z := by
      intro k
      rw [pow_succ, pow_mul, hz2, one_pow, one_mul]
    have h1 : (n * z) ^ (2 * o + 1) = z := by rw [hcomm.mul_pow, hn1, one_mul, hzpow]
    have h2 : z ^ (2 * o' + 1) = 1 := by
      calc z ^ (2 * o' + 1) = ((n * z) ^ (2 * o + 1)) ^ (2 * o' + 1) := by rw [h1]
        _ = ((n * z) ^ (2 * o' + 1)) ^ (2 * o + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ = 1 := by rw [hn2, one_pow]
    rw [hzpow] at h2
    exact hz1 h2
  have hSaCard : Nat.card ↥Sa = 2 * m := by
    rw [Nat.card_coe_set_eq, hSa, Set.ncard_image_of_injective _ (mul_right_injective y),
      ← Nat.card_coe_set_eq]
    exact hCcard
  set Sz : Set G := (fun n => n * z) '' So with hSz
  have hSz_card : Sz.ncard = So.ncard := Set.ncard_image_of_injective _ (mul_left_injective z)
  have hdisj : Disjoint So Sz := by
    rw [Set.disjoint_left]
    rintro n ⟨hnSa, hnodd⟩ ⟨n', ⟨hn'Sa, hn'odd⟩, rfl⟩
    exact hnotboth n' hn'Sa ⟨hn'odd, hnodd⟩
  have hunion : Sa = So ∪ Sz := by
    ext n
    constructor
    · intro hn
      rcases hclaim n hn with h | h
      · exact Or.inl ⟨hn, h⟩
      · refine Or.inr ⟨n * z, ⟨hSaz n hn, h⟩, ?_⟩
        show n * z * z = n
        rw [mul_assoc, hzsq, mul_one]
    · rintro (⟨hn, -⟩ | ⟨n', ⟨hn', -⟩, rfl⟩)
      · exact hn
      · exact hSaz n' hn'
  have hSoodd : Odd (Nat.card ↥So) := by
    have h1 : Sa.ncard = So.ncard + Sz.ncard := by
      rw [hunion]
      exact Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    rw [Nat.card_coe_set_eq] at hSaCard ⊢
    rw [hSz_card] at h1
    obtain ⟨k, hk⟩ := hmodd
    exact ⟨k, by omega⟩
  have hinv : ∀ v ∈ P, ∀ n ∈ So, v * n * v⁻¹ ∈ So := by
    rintro v hv n ⟨hnSa, hnodd⟩
    obtain ⟨c, hc, rfl⟩ := hnSa
    have hnK : y * c ∈ K := K.mul_mem hyK hc.2
    have hvK : v * (y * c) * v⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hPK hv) _).mp hnK
    have hvR : ∀ r ∈ R, v * r * v⁻¹ = r := by
      intro r hr
      have := Subgroup.mem_centralizer_iff.mp (hPR hv) r hr
      calc v * r * v⁻¹ = (v * r) * v⁻¹ := rfl
        _ = (r * v) * v⁻¹ := by rw [this]
        _ = r := by group
    have hvR' : ∀ r ∈ R, v⁻¹ * r * v = r := by
      intro r hr
      have := Subgroup.mem_centralizer_iff.mp (hPR (P.inv_mem hv)) r hr
      calc v⁻¹ * r * v = (v⁻¹ * r) * v⁻¹⁻¹ := by group
        _ = (r * v⁻¹) * v⁻¹⁻¹ := by rw [this]
        _ = r := by group
    refine ⟨⟨y⁻¹ * (v * (y * c) * v⁻¹), ⟨Subgroup.mem_centralizer_iff.mpr fun r hr => ?_,
      K.mul_mem (K.inv_mem hyK) hvK⟩, by group⟩, odd_orderOf_conj v hnodd⟩
    set c' := y⁻¹ * (v * (y * c) * v⁻¹) with hc'
    have h1 : v⁻¹ * r * v = r := hvR' r hr
    have h2 : (y * c) * r * (y * c)⁻¹ = y * r * y⁻¹ := hSaact _ ⟨c, hc, rfl⟩ r hr
    have h3 : v * (y * r * y⁻¹) * v⁻¹ = y * r * y⁻¹ := hvR _ (hyR r hr)
    have : c' * r * c'⁻¹ = r := by
      calc c' * r * c'⁻¹ = y⁻¹ * (v * ((y * c) * (v⁻¹ * r * v) * (y * c)⁻¹) * v⁻¹) * y := by
            rw [hc']; group
        _ = y⁻¹ * (v * (y * r * y⁻¹) * v⁻¹) * y := by rw [h1, h2]
        _ = r := by rw [h3]; group
    calc r * c' = (c' * r * c'⁻¹) * c' := by rw [this]
      _ = c' * r := by group
  obtain ⟨n, ⟨hnSa, hnodd⟩, hfix⟩ := Thompson.exists_fixed_mem_of_odd hP hinv hSoodd
  refine ⟨n, hSaK n hnSa, hSaN n hnSa, hnodd, hSaact n hnSa, fun x hx => ?_⟩
  exact mul_inv_eq_iff_eq_mul.mp (hfix x hx)

end T75

end CFSG.ClassicalInvolution.Asc77
