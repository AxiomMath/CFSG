module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.PermThree
public import CFSG.GH74.GLS.Stage1.Thm6.M12Facts.Triples
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Group
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.GH74.GLS.Stage1.Thm6.M12Facts.Classes
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14

open Subgroup CFSG.GH74.GLS.Stage1.Thm6.Sec13 CFSG.GH74.GLS.Stage1.Thm6.M12Facts

variable {G : Type} [Group G] [Finite G]

structure Hyp14 (G : Type) [Group G] [Finite G] (S : Subgroup G) (a b y x : G) : Prop where
  data : M12Data S a b y x
  sylow : Sylow2In S (centralizer ({a ^ 2 * b ^ 2} : Set G))
  odd : CFSG.oddCore ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) = ⊥
  F1 : ∀ c ∈ S, c * c = a ^ 2 * b ^ 2 →
    ∃ g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G), g * c * g⁻¹ ∈ closure ({a, b} : Set G) ∧
      (g * c * g⁻¹) * (g * c * g⁻¹) = a ^ 2 * b ^ 2
  F2 : ∀ g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G),
    g * x * g⁻¹ ∉ closure ({a * a, b * b} : Set G)
  normal : ((Rsub S a b).subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G))).Normal

variable {S : Subgroup G} {a b y x : G}

omit [Finite G] in
theorem mem_C_iff {g : G} : g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G) ↔
    (a ^ 2 * b ^ 2) * g = g * (a ^ 2 * b ^ 2) := by
  rw [mem_centralizer_iff]; simp

theorem S_le_C (H : Hyp14 G S a b y x) : S ≤ centralizer ({a ^ 2 * b ^ 2} : Set G) := H.sylow.1

omit [Finite G] in
theorem z_comm_C {g : G} (hg : g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G)) :
    g * (a ^ 2 * b ^ 2) = (a ^ 2 * b ^ 2) * g := (mem_C_iff.1 hg).symm

theorem R_eq' (H : Hyp14 G S a b y x) : Rsub S a b = nfSub H.data pR closed_pR := R_eq H.data

theorem R_le_C (H : Hyp14 G S a b y x) : Rsub S a b ≤ centralizer ({a ^ 2 * b ^ 2} : Set G) := by
  rw [R_eq' H]; exact (nfSub_le_S H.data closed_pR).trans (S_le_C H)

theorem conj_R (H : Hyp14 G S a b y x) {g : G}
    (hg : g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G)) {r : G} (hr : r ∈ Rsub S a b) :
    g * r * g⁻¹ ∈ Rsub S a b := by
  have := H.normal.conj_mem (⟨r, R_le_C H hr⟩ : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) hr ⟨g, hg⟩
  exact this

theorem z_mem_R (H : Hyp14 G S a b y x) : a ^ 2 * b ^ 2 ∈ Rsub S a b := by
  rw [R_eq' H, zG_eq (y := y) (x := x)]
  exact ⟨zNF, pR_zNF, rfl⟩

theorem mem_of_odd_orderOf {X : Type*} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (hq : IsPGroup 2 (X ⧸ K)) {g : X} (hg : Odd (orderOf g)) : g ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hq (g : X ⧸ K)
  have h1 : orderOf (g : X ⧸ K) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : orderOf (g : X ⧸ K) ∣ orderOf g := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]; rfl
  have h3 : orderOf (g : X ⧸ K) ∣ Nat.gcd (orderOf g) (2 ^ n) := Nat.dvd_gcd h2 h1
  have hc2 : Nat.Coprime (orderOf g) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by have := Nat.odd_iff.1 hg; omega)).symm
  have hcop : Nat.gcd (orderOf g) (2 ^ n) = 1 := Nat.Coprime.pow_right n hc2
  rw [hcop] at h3
  have : (g : X ⧸ K) = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  exact (QuotientGroup.eq_one_iff g).1 this

theorem centralizer_R_eq (H : Hyp14 G S a b y x) :
    centralizer ((Rsub S a b : Subgroup G) : Set G) = zpowers (a ^ 2 * b ^ 2) := by
  have h := H.data
  set Zc : Subgroup G := centralizer ((Rsub S a b : Subgroup G) : Set G) with hZc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzR : a ^ 2 * b ^ 2 ∈ Rsub S a b := z_mem_R H
  have hzcomm : ∀ r ∈ Rsub S a b, r * (a ^ 2 * b ^ 2) = (a ^ 2 * b ^ 2) * r :=
    fun r hr => z_comm_C (R_le_C H hr)
  have hZC : Zc ≤
      centralizer ({a ^ 2 * b ^ 2} : Set G) := by
    intro g hg
    rw [mem_C_iff]
    exact mem_centralizer_iff.1 hg _ hzR
  have hZn : ∀ c ∈ centralizer ({a ^ 2 * b ^ 2} : Set G),
      ∀ g ∈ Zc,
      c * g * c⁻¹ ∈ Zc := by
    intro c hc g hg
    rw [mem_centralizer_iff]
    intro r hr
    have hr' : c⁻¹ * r * c ∈ Rsub S a b := by
      have := conj_R H (Subgroup.inv_mem _ hc) hr
      simpa using this
    have e := mem_centralizer_iff.1 hg _ hr'
    calc r * (c * g * c⁻¹) = c * ((c⁻¹ * r * c) * g) * c⁻¹ := by group
      _ = c * (g * (c⁻¹ * r * c)) * c⁻¹ := by rw [e]
      _ = (c * g * c⁻¹) * r := by group
  have h2 : ∀ g ∈ Zc, (∃ n : ℕ, g ^ 2 ^ n = 1) →
      g ∈ zpowers (a ^ 2 * b ^ 2) := by
    rintro g hg ⟨n, hn⟩
    have hgC : g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G) := hZC hg
    have hpg : IsPGroup 2 ↥(zpowers g) := by
      rintro ⟨k, hk⟩
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      refine ⟨n, ?_⟩
      apply Subtype.ext
      show (g ^ m) ^ 2 ^ n = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]
    obtain ⟨P, hP, hgP⟩ := Sec12.exists_sylow2_ge hpg (Subgroup.zpowers_le.2 hgC)
    obtain ⟨c, hcC, hPc⟩ := Sec12.sylow2_exists_conj H.sylow hP
    have hgS : c * g * c⁻¹ ∈ S := by
      have hgP' : g ∈ P := hgP (Subgroup.mem_zpowers g)
      rw [hPc] at hgP'
      exact hgP'
    have hcg := hZn c hcC g hg
    obtain ⟨p, hp⟩ := exists_nf h hgS
    have hcomm : ∀ q, pR q → nfMul p q = nfMul q p := by
      intro q hq
      have hqR : nu a b y x q ∈ Rsub S a b := by rw [R_eq' H]; exact ⟨q, hq, rfl⟩
      have e := mem_centralizer_iff.1 hcg _ hqR
      rw [hp, nu_mul h, nu_mul h] at e
      exact (nu_injective h e).symm
    have hzc := z_comm_C hcC
    rcases centralizer_R p hcomm with rfl | rfl
    · have e : c * g * c⁻¹ = 1 := by rw [hp, nu_zero]
      have : g = 1 := by
        calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
          _ = 1 := by rw [e]; group
      rw [this]; exact one_mem _
    · have e : c * g * c⁻¹ = a ^ 2 * b ^ 2 := by rw [hp, ← zG_eq (y := y) (x := x)]
      have hg' : g = a ^ 2 * b ^ 2 := by
        calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
          _ = c⁻¹ * (a ^ 2 * b ^ 2) * c := by rw [e]
          _ = a ^ 2 * b ^ 2 := by rw [mul_assoc, ← hzc]; group
      rw [hg']; exact mem_zpowers _
  have hzZ : a ^ 2 * b ^ 2 ∈ Zc := by
    rw [mem_centralizer_iff]; intro r hr; exact hzcomm r hr
  have hordz : orderOf (a ^ 2 * b ^ 2) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact z_sq h) (z_ne_one h)
  have hzle : zpowers (a ^ 2 * b ^ 2) ≤ Zc :=
    Subgroup.zpowers_le.2 hzZ
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(Zc)) :=
    inferInstance
  have hQcard : Nat.card ((zpowers (a ^ 2 * b ^ 2)).subgroupOf
      (Zc)) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv, Nat.card_zpowers, hordz]
  have hPQ : (P : Subgroup ↥(Zc)) ≤
      (zpowers (a ^ 2 * b ^ 2)).subgroupOf (Zc) := by
    intro p hp
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨p, hp⟩
    have hpn : ((p : ↥(Zc)) : G) ^ 2 ^ n = 1 := by
      have := congrArg (fun t : ↥(P : Subgroup ↥(Zc)) =>
        (((t : ↥(Zc)) : G))) hn
      simpa using this
    exact h2 _ p.2 ⟨n, hpn⟩
  have hdvdZ : 2 ∣ Nat.card ↥(Zc) := by
    have := orderOf_dvd_natCard (⟨a ^ 2 * b ^ 2, hzZ⟩ :
      ↥(Zc))
    rwa [Subgroup.orderOf_mk, hordz] at this
  have hPcard : Nat.card P = 2 := by
    have hP1 := P.card_eq_multiplicity
    have hfac : 0 < (Nat.card ↥(Zc)).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two (Nat.card_pos.ne') hdvdZ
    have hle : Nat.card P ≤ 2 := by
      have := Subgroup.card_le_of_le hPQ
      rw [hQcard] at this
      exact this
    have : 2 ≤ Nat.card P := by
      rw [hP1]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hfac
    omega
  have hPeq : (P : Subgroup ↥(Zc)) =
      (zpowers (a ^ 2 * b ^ 2)).subgroupOf (Zc) :=
    Subgroup.eq_of_le_of_card_ge hPQ (by rw [hPcard, hQcard])
  have hPcent : ∀ n : ↥Zc, ∀ p ∈ (P : Subgroup ↥Zc), p * n = n * p := by
    intro n p hp
    rw [hPeq] at hp
    have hpz : (p : G) ∈ zpowers (a ^ 2 * b ^ 2) := hp
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hpz
    apply Subtype.ext
    show (p : G) * (n : G) = (n : G) * (p : G)
    rw [← hk]
    have hc : Commute (n : G) (a ^ 2 * b ^ 2) := z_comm_C (hZC n.2)
    exact (hc.zpow_right k).symm.eq
  have hPn : Subgroup.normalizer ((P : Subgroup ↥Zc) : Set ↥Zc) ≤
      Subgroup.centralizer ((P : Subgroup ↥Zc) : Set ↥Zc) :=
    fun n _ => mem_centralizer_iff.2 (fun p hp => hPcent n p hp)
  obtain ⟨K, hKn, hKodd, hKidx, -, -, -, -, -, ⟨e, -⟩, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hPn
  have := hKn
  have hq : IsPGroup 2 (↥Zc ⧸ K) := P.isPGroup'.of_surjective e.toMonoidHom e.surjective
  set K' : Subgroup G := K.map Zc.subtype with hK'
  have hK'Zc : K' ≤ Zc := by
    rintro _ ⟨k₀, _, rfl⟩
    exact k₀.2
  have hK'C : K' ≤ centralizer ({a ^ 2 * b ^ 2} : Set G) := hK'Zc.trans hZC
  have hKodd' : Odd (Nat.card K) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hKodd)
  have hK'card : Nat.card K' = Nat.card K := Subgroup.card_map_of_injective Zc.subtype_injective
  have hnormK' : ∀ n ∈ K', ∀ g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G), g * n * g⁻¹ ∈ K' := by
    rintro _ ⟨k, hk, rfl⟩ g hg
    have hmem : g * (k : G) * g⁻¹ ∈ Zc := hZn g hg k k.2
    have hord : Odd (orderOf (⟨g * (k : G) * g⁻¹, hmem⟩ : ↥Zc)) := by
      have h1 : orderOf (g * (k : G) * g⁻¹) = orderOf (k : G) := by
        have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (k : G)
        simpa [MulAut.conj_apply] using this
      rw [Subgroup.orderOf_mk, h1, Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat hKodd' (Subgroup.orderOf_dvd_natCard K hk)
    exact ⟨_, mem_of_odd_orderOf K hq hord, rfl⟩
  set N' : Subgroup ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) :=
    K'.subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G)) with hN'
  have hN'norm : N'.Normal := ⟨fun n hn g => hnormK' n hn g g.2⟩
  have hN'card : Odd (Nat.card N') := by
    rw [hN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'C).toEquiv, hK'card]
    exact hKodd'
  have hN'le : N' ≤ CFSG.oddCore ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) :=
    le_sSup ⟨hN'norm, hN'card⟩
  rw [H.odd] at hN'le
  have hK'bot : K' = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    have h1 : (⟨k, hK'C hk⟩ : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) ∈ N' := hk
    have h2 := hN'le h1
    rw [Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h2
  have hKbot : K = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    have h1 : (k : G) ∈ K' := ⟨k, hk, rfl⟩
    rw [hK'bot, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext h1
  have hZcard : Nat.card Zc = 2 := by
    have := hKidx
    rw [hKbot, Subgroup.index_bot, hPcard] at this
    exact this
  have hzeq : zpowers (a ^ 2 * b ^ 2) = Zc :=
    Subgroup.eq_of_le_of_card_ge hzle (by rw [hZcard, Nat.card_zpowers, hordz])
  exact hzeq.symm

section Q8

variable (h : M12Data S a b y x)

omit [Finite G] in
theorem R2_q8 : Nonempty (↥(nfSub h pR2 closed_pR2) ≃* QuaternionGroup 2) := by
  let f : QuaternionGroup 2 →* ↥(nfSub h pR2 closed_pR2) :=
    MonoidHom.mk' (fun u => ⟨nu a b y x (q8NF2 u), ⟨q8NF2 u, q8NF2_pR2 u, rfl⟩⟩) (by
      intro u v
      apply Subtype.ext
      show nu a b y x (q8NF2 (u * v)) = nu a b y x (q8NF2 u) * nu a b y x (q8NF2 v)
      rw [q8NF2_mul, nu_mul h])
  have hbij : Function.Bijective f := by
    constructor
    · intro u v huv
      exact q8NF2_inj (nu_injective h (congrArg Subtype.val huv))
    · rintro ⟨g, p, hp, rfl⟩
      obtain ⟨u, hu⟩ := q8NF2_surj p hp
      exact ⟨u, Subtype.ext (by simp [f, hu])⟩
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

theorem q8_sub_eq {K : Subgroup G} (hKR : K ≤ nfSub h pR closed_pR)
    (e : ↥K ≃* QuaternionGroup 2) :
    K = nfSub h pR1 closed_pR1 ∨ K = nfSub h pR2 closed_pR2 := by
  obtain ⟨hr1, hr2, hr3⟩ := Q8_rels
  have hKS : ∀ k ∈ K, ∃ p, pR p ∧ k = nu a b y x p := fun k hk => by
    obtain ⟨p, hp, hpk⟩ := hKR hk
    exact ⟨p, hp, hpk⟩
  obtain ⟨p, hp, hpe⟩ := hKS ((e.symm (QuaternionGroup.a 1) : ↥K) : G) (e.symm _).2
  obtain ⟨q, hq, hqe⟩ := hKS ((e.symm (QuaternionGroup.xa 0) : ↥K) : G) (e.symm _).2
  have hsq : e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.a 1) =
      e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.xa 0) := by
    rw [← map_mul, ← map_mul, hr1]
  have hsq1 : e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.a 1) ≠ 1 := by
    rw [← map_mul]
    intro h1
    apply hr2
    simpa using congrArg e.symm.symm h1
  have hnc : e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) ≠
      e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) := by
    rw [← map_mul, ← map_mul]
    intro h1
    apply hr3
    exact e.symm.injective h1
  have hpsq : nfMul p p = zNF := by
    apply pR_sq_ne_one_of_mem p hp
    intro h0
    apply hsq1
    apply Subtype.ext
    show ((e.symm (QuaternionGroup.a 1) : ↥K) : G) * ((e.symm (QuaternionGroup.a 1) : ↥K) : G) = 1
    rw [hpe, nu_mul h, h0, nu_zero]
  have hqsq : nfMul q q = zNF := by
    apply pR_sq_ne_one_of_mem q hq
    intro h0
    apply hsq1
    rw [hsq]
    apply Subtype.ext
    show ((e.symm (QuaternionGroup.xa 0) : ↥K) : G) * ((e.symm (QuaternionGroup.xa 0) : ↥K) : G) = 1
    rw [hqe, nu_mul h, h0, nu_zero]
  have hpq : nfMul p q ≠ nfMul q p := by
    intro h0
    apply hnc
    apply Subtype.ext
    show ((e.symm (QuaternionGroup.a 1) : ↥K) : G) * ((e.symm (QuaternionGroup.xa 0) : ↥K) : G) =
      ((e.symm (QuaternionGroup.xa 0) : ↥K) : G) * ((e.symm (QuaternionGroup.a 1) : ↥K) : G)
    rw [hpe, hqe, nu_mul h, nu_mul h, h0]
  have hsame := q8_pair p ((sq_eq_z_iff p).1 hpsq) q ((sq_eq_z_iff q).1 hqsq) hpq
  have hcardK : Nat.card K = 8 := by rw [Nat.card_congr e.toEquiv, card_Q8]
  have gen : ∀ k : ↥K, ∃ m < 4, ∃ n < 2, k = (e.symm (QuaternionGroup.a 1)) ^ m *
      (e.symm (QuaternionGroup.xa 0)) ^ n := by
    intro k
    obtain ⟨m, hm, n, hn, hu⟩ := Q8_gen (e k)
    refine ⟨m, hm, n, hn, ?_⟩
    apply e.injective
    rw [hu]
    simp
  rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have hle : K ≤ nfSub h pR1 closed_pR1 := by
      intro k hk
      obtain ⟨m, _, n, _, hk'⟩ := gen ⟨k, hk⟩
      have hkk : k = (nu a b y x p) ^ m * (nu a b y x q) ^ n := by
        have := congrArg Subtype.val hk'
        simpa [hpe, hqe] using this
      rw [hkk]
      exact mul_mem (pow_mem ((nu_mem_nfSub h closed_pR1 p).2 h1) _)
        (pow_mem ((nu_mem_nfSub h closed_pR1 q).2 h2) _)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_nfSub h, card_pR1, hcardK])
  · right
    have hle : K ≤ nfSub h pR2 closed_pR2 := by
      intro k hk
      obtain ⟨m, _, n, _, hk'⟩ := gen ⟨k, hk⟩
      have hkk : k = (nu a b y x p) ^ m * (nu a b y x q) ^ n := by
        have := congrArg Subtype.val hk'
        simpa [hpe, hqe] using this
      rw [hkk]
      exact mul_mem (pow_mem ((nu_mem_nfSub h closed_pR2 p).2 h1) _)
        (pow_mem ((nu_mem_nfSub h closed_pR2 q).2 h2) _)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_nfSub h, card_pR2, hcardK])

end Q8

@[expose] def cj (g : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj g).toMonoidHom

omit [Finite G] in
theorem mem_cj {g k : G} {K : Subgroup G} : k ∈ cj g K ↔ g⁻¹ * k * g ∈ K := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro hk
    exact ⟨g⁻¹ * k * g, hk, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [Finite G] in
theorem cj_mul (g g' : G) (K : Subgroup G) : cj (g * g') K = cj g (cj g' K) := by
  ext k
  simp only [mem_cj]
  rw [show (g * g')⁻¹ * k * (g * g') = g'⁻¹ * (g⁻¹ * k * g) * g' by group]

omit [Finite G] in
theorem cj_one (K : Subgroup G) : cj 1 K = K := by ext k; simp [mem_cj]

omit [Finite G] in
theorem cj_injective {g : G} {K K' : Subgroup G} (e : cj g K = cj g K') : K = K' := by
  ext k
  have h1 := Iff.of_eq (congrArg (fun L : Subgroup G => g * k * g⁻¹ ∈ L) e)
  simp only [mem_cj] at h1
  rw [show g⁻¹ * (g * k * g⁻¹) * g = k by group] at h1
  exact h1

theorem cj_le_R (H : Hyp14 G S a b y x) {g : G}
    (hg : g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G)) {K : Subgroup G} (hK : K ≤ Rsub S a b) :
    cj g K ≤ Rsub S a b := by
  intro k hk
  rw [mem_cj] at hk
  have := conj_R H hg (hK hk)
  simpa [mul_assoc] using this

theorem cj_dichotomy (H : Hyp14 G S a b y x) {g : G}
    (hg : g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G)) :
    (cj g (nfSub H.data pR1 closed_pR1) = nfSub H.data pR1 closed_pR1 ∨
      cj g (nfSub H.data pR1 closed_pR1) = nfSub H.data pR2 closed_pR2) ∧
    (cj g (nfSub H.data pR2 closed_pR2) = nfSub H.data pR1 closed_pR1 ∨
      cj g (nfSub H.data pR2 closed_pR2) = nfSub H.data pR2 closed_pR2) := by
  have h := H.data
  have hR1R : nfSub h pR1 closed_pR1 ≤ Rsub S a b := by
    rw [R_eq' H]; exact R1_le_R h
  have hR2R : nfSub h pR2 closed_pR2 ≤ Rsub S a b := by
    rw [R_eq' H]; exact nfSub_le_nfSub h closed_pR2 closed_pR pR_of_pR2
  constructor
  · obtain ⟨e⟩ := R1_q8 h
    exact q8_sub_eq h (by rw [← R_eq' H]; exact cj_le_R H hg hR1R)
      ((Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm.trans e)
  · obtain ⟨e⟩ := R2_q8 h
    exact q8_sub_eq h (by rw [← R_eq' H]; exact cj_le_R H hg hR2R)
      ((Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm.trans e)

theorem normalizes_R1R2 (H : Hyp14 G S a b y x) :
    ∀ g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G),
      cj g (nfSub H.data pR1 closed_pR1) = nfSub H.data pR1 closed_pR1 ∧
      cj g (nfSub H.data pR2 closed_pR2) = nfSub H.data pR2 closed_pR2 := by
  classical
  have h := H.data
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R1 := nfSub h pR1 closed_pR1 with hR1
  set R2 := nfSub h pR2 closed_pR2 with hR2
  have hne : R1 ≠ R2 := by
    intro e
    obtain ⟨p, hp1, hp2⟩ := R1_not_le_R2
    apply hp2
    have : nu a b y x p ∈ R2 := e ▸ (nu_mem_nfSub h closed_pR1 p).2 hp1
    exact (nu_mem_nfSub h closed_pR2 p).1 this
  let Ω := {K : Subgroup G // K = R1 ∨ K = R2}
  let _ : MulAction ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) Ω :=
    { smul := fun g K => ⟨cj g K.1, by
        rcases K.2 with e | e
        · rw [e]; exact (cj_dichotomy H g.2).1
        · rw [e]; exact (cj_dichotomy H g.2).2⟩
      one_smul := fun K => Subtype.ext (cj_one K.1)
      mul_smul := fun g g' K => Subtype.ext (cj_mul (g : G) (g' : G) K.1) }
  let ω₁ : Ω := ⟨R1, Or.inl rfl⟩
  have hstab : S.subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G)) ≤
      MulAction.stabilizer ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) ω₁ := by
    intro s hs
    show s • ω₁ = ω₁
    apply Subtype.ext
    show cj (s : G) R1 = R1
    have hsS : (s : G) ∈ S := hs
    ext k
    rw [mem_cj]
    constructor
    · intro hk
      have := conj_mem_nfSub h closed_pR1 conj_pR1 (s : G) hsS _ hk
      simpa [mul_assoc] using this
    · intro hk
      have := conj_mem_nfSub h closed_pR1 conj_pR1 ((s : G)⁻¹) (S.inv_mem hsS) _ hk
      simpa using this
  have hidx := Subgroup.index_dvd_of_le hstab
  have hodd : ¬ 2 ∣ (S.subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G))).index :=
    H.sylow.2.2
  have horb : (MulAction.stabilizer ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) ω₁).index =
      Nat.card (MulAction.orbit ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) ω₁) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ ω₁)).symm
  have hcard2 : Nat.card (MulAction.orbit ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) ω₁) ≤ 2 := by
    have hinj : Function.Injective (fun K : Ω => decide (K.1 = R1)) := by
      intro K K' hKK
      apply Subtype.ext
      simp only [decide_eq_decide] at hKK
      by_cases h1 : K.1 = R1
      · exact h1.trans (hKK.1 h1).symm
      · have h2 : K.1 = R2 := K.2.resolve_left h1
        have h1' : ¬ K'.1 = R1 := fun e => h1 (hKK.2 e)
        exact h2.trans (K'.2.resolve_left h1').symm
    calc Nat.card (MulAction.orbit ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) ω₁)
        ≤ Nat.card Ω := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
      _ = 2 := by simp
  have hdvd : Nat.card (MulAction.orbit ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) ω₁) ∣
      (S.subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G))).index := by
    rw [← horb]; exact hidx
  have hone : Nat.card (MulAction.orbit ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) ω₁) = 1 := by
    have hne' : Nonempty (MulAction.orbit ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) ω₁) :=
      ⟨⟨ω₁, MulAction.mem_orbit_self _⟩⟩
    have hpos : 0 < Nat.card (MulAction.orbit ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) ω₁) :=
      Nat.card_pos
    by_contra hne1
    have h2 : Nat.card (MulAction.orbit ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) ω₁) = 2 := by
      omega
    rw [h2] at hdvd
    exact hodd hdvd
  have hsub := (Nat.card_eq_one_iff_unique.1 hone).1
  have hfix : ∀ g : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)), g • ω₁ = ω₁ := fun g => by
    have := hsub.elim (⟨g • ω₁, MulAction.mem_orbit _ _⟩ :
      MulAction.orbit ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) ω₁)
      ⟨ω₁, MulAction.mem_orbit_self _⟩
    exact congrArg Subtype.val this
  intro g hg
  have h1 : cj g R1 = R1 := congrArg Subtype.val (hfix ⟨g, hg⟩)
  refine ⟨h1, ?_⟩
  rcases (cj_dichotomy H hg).2 with e | e
  · exfalso
    apply hne
    exact (cj_injective (g := g) (e.trans h1.symm)).symm
  · exact e

omit [Finite G] in
theorem exists_triple_hom (C : Subgroup G) (z : G) (r : Fin 3 → G)
    (hz : ∀ g ∈ C, g * z = z * g) (hz2 : z * z = 1)
    (hT : ∀ g ∈ C, ∀ i, ∃ j, g * r i * g⁻¹ = r j ∨ g * r i * g⁻¹ = r j * z)
    (hdist : ∀ i j, (r i = r j ∨ r i = r j * z) → i = j) :
    ∃ ρ : ↥C →* Equiv.Perm (Fin 3), ∀ (g : ↥C) (i j : Fin 3),
      ((g : G) * r i * (g : G)⁻¹ = r j ∨ (g : G) * r i * (g : G)⁻¹ = r j * z) ↔ ρ g i = j := by
  have hzz : ∀ t : G, t * z * z = t := fun t => by rw [mul_assoc, hz2, mul_one]
  have huniq : ∀ (c : G) (j j' : Fin 3), (c = r j ∨ c = r j * z) → (c = r j' ∨ c = r j' * z) →
      j = j' := by
    intro c j j' h1 h2
    apply hdist j j'
    rcases h1 with rfl | rfl
    · exact h2
    · rcases h2 with e | e
      · exact Or.inr (by rw [← e, hzz])
      · exact Or.inl (mul_right_cancel e)
  have hsel : ∀ (g : ↥C) (i : Fin 3), ∃ j, (g : G) * r i * (g : G)⁻¹ = r j ∨
      (g : G) * r i * (g : G)⁻¹ = r j * z := fun g i => hT g.1 g.2 i
  choose σ hσ using hsel
  have hσ' : ∀ (g : ↥C) (i j : Fin 3), ((g : G) * r i * (g : G)⁻¹ = r j ∨
      (g : G) * r i * (g : G)⁻¹ = r j * z) → σ g i = j :=
    fun g i j hj => huniq _ _ _ (hσ g i) hj
  have hmul : ∀ (g g' : ↥C) (i : Fin 3), σ (g * g') i = σ g (σ g' i) := by
    intro g g' i
    apply hσ'
    have hc : ((g * g' : ↥C) : G) * r i * ((g * g' : ↥C) : G)⁻¹ =
        (g : G) * ((g' : G) * r i * (g' : G)⁻¹) * (g : G)⁻¹ := by
      show ((g : G) * (g' : G)) * r i * ((g : G) * (g' : G))⁻¹ = _
      group
    rw [hc]
    have hgz : (g : G) * z * (g : G)⁻¹ = z := by rw [hz g g.2]; group
    rcases hσ g' i with e | e
    · rw [e]; exact hσ g (σ g' i)
    · rw [e]
      have : (g : G) * (r (σ g' i) * z) * (g : G)⁻¹ =
          ((g : G) * r (σ g' i) * (g : G)⁻¹) * z := by
        calc (g : G) * (r (σ g' i) * z) * (g : G)⁻¹
            = ((g : G) * r (σ g' i) * (g : G)⁻¹) * ((g : G) * z * (g : G)⁻¹) := by group
          _ = _ := by rw [hgz]
      rw [this]
      rcases hσ g (σ g' i) with e' | e'
      · exact Or.inr (by rw [e'])
      · exact Or.inl (by rw [e', hzz])
  have hone : ∀ i, σ 1 i = i := fun i => hσ' 1 i i (Or.inl (by simp))
  let ρ : ↥C →* Equiv.Perm (Fin 3) := MonoidHom.mk'
    (fun g => ⟨σ g, σ g⁻¹, fun i => by rw [← hmul, inv_mul_cancel, hone],
      fun i => by rw [← hmul, mul_inv_cancel, hone]⟩)
    (fun g g' => Equiv.ext fun i => hmul g g' i)
  refine ⟨ρ, fun g i j => ⟨fun hj => hσ' g i j hj, fun hj => ?_⟩⟩
  have : σ g i = j := hj
  rw [← this]
  exact hσ g i

theorem exists_hom_of_triple (H : Hyp14 G S a b y x) {pk : NF → Prop} (hk : NFClosed pk)
    (rep : Fin 3 → NF)
    (hnorm : ∀ g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G),
      cj g (nfSub H.data pk hk) = nfSub H.data pk hk)
    (hmem : ∀ i, pk (rep i)) (hsq : ∀ i, nfMul (rep i) (rep i) = zNF)
    (hpoints : ∀ p, pk p → nfMul p p = zNF → ∃ i, p = rep i ∨ p = nfMul (rep i) zNF)
    (hdist : ∀ i j, (rep i = rep j ∨ rep i = nfMul (rep j) zNF) → i = j) :
    ∃ ρ : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) →* Equiv.Perm (Fin 3),
      ∀ (g : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) (i j : Fin 3),
        ((g : G) * nu a b y x (rep i) * (g : G)⁻¹ = nu a b y x (rep j) ∨
          (g : G) * nu a b y x (rep i) * (g : G)⁻¹ = nu a b y x (rep j) * (a ^ 2 * b ^ 2)) ↔
        ρ g i = j := by
  have h := H.data
  have hZ : a ^ 2 * b ^ 2 = nu a b y x zNF := zG_eq
  apply exists_triple_hom (centralizer ({a ^ 2 * b ^ 2} : Set G)) (a ^ 2 * b ^ 2)
    (fun i => nu a b y x (rep i))
  · intro g hg; exact z_comm_C hg
  · exact z_sq h
  · intro g hg i
    have hmemk : nu a b y x (rep i) ∈ nfSub h pk hk := (nu_mem_nfSub h hk _).2 (hmem i)
    have hin : g * nu a b y x (rep i) * g⁻¹ ∈ nfSub h pk hk := by
      rw [← hnorm g hg, mem_cj]
      rw [show g⁻¹ * (g * nu a b y x (rep i) * g⁻¹) * g = nu a b y x (rep i) by group]
      exact hmemk
    obtain ⟨p, hp, hpe⟩ := hin
    have hsqp : nfMul p p = zNF := by
      have h1 : (g * nu a b y x (rep i) * g⁻¹) * (g * nu a b y x (rep i) * g⁻¹) = a ^ 2 * b ^ 2 := by
        calc (g * nu a b y x (rep i) * g⁻¹) * (g * nu a b y x (rep i) * g⁻¹)
            = g * (nu a b y x (rep i) * nu a b y x (rep i)) * g⁻¹ := by group
          _ = g * (a ^ 2 * b ^ 2) * g⁻¹ := by rw [nu_mul h, hsq i, hZ]
          _ = a ^ 2 * b ^ 2 := by rw [z_comm_C hg]; group
      rw [hpe, nu_mul h, hZ] at h1
      exact nu_injective h h1
    obtain ⟨j, hj⟩ := hpoints p hp hsqp
    refine ⟨j, ?_⟩
    rw [hpe]
    rcases hj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by rw [hZ, nu_mul h])
  · intro i j hij
    apply hdist
    rcases hij with e | e
    · exact Or.inl (nu_injective h e)
    · refine Or.inr (nu_injective h ?_)
      rw [e, hZ, nu_mul h]

section Kernel

variable (h : M12Data S a b y x)

omit [Finite G] in
theorem inner_R1 {T₀ T₁ : G}
    (h0 : T₀ = nu a b y x (r1rep 0) ∨ T₀ = nu a b y x (r1rep 0) * (a ^ 2 * b ^ 2))
    (h1 : T₁ = nu a b y x (r1rep 1) ∨ T₁ = nu a b y x (r1rep 1) * (a ^ 2 * b ^ 2)) :
    ∃ u ∈ nfSub h pR1 closed_pR1, u * nu a b y x (r1rep 0) * u⁻¹ = T₀ ∧
      u * nu a b y x (r1rep 1) * u⁻¹ = T₁ := by
  have hZ : a ^ 2 * b ^ 2 = nu a b y x zNF := zG_eq
  have key : ∀ e₀ e₁ : Fin 2, ∃ u ∈ nfSub h pR1 closed_pR1,
      u * nu a b y x (r1rep 0) * u⁻¹ =
        (if e₀ = 0 then nu a b y x (r1rep 0) else nu a b y x (r1rep 0) * (a ^ 2 * b ^ 2)) ∧
      u * nu a b y x (r1rep 1) * u⁻¹ =
        (if e₁ = 0 then nu a b y x (r1rep 1) else nu a b y x (r1rep 1) * (a ^ 2 * b ^ 2)) := by
    intro e₀ e₁
    obtain ⟨r, hr, h0', h1'⟩ := R1_inner e₀ e₁
    refine ⟨nu a b y x r, (nu_mem_nfSub h closed_pR1 r).2 hr, ?_, ?_⟩
    · have := congrArg (nu a b y x) h0'
      rw [← nu_mul h, ← nu_mul h, ← nu_inv h] at this
      rw [this]
      by_cases he : e₀ = 0
      · simp [he]
      · simp [he, nu_mul h, hZ]
    · have := congrArg (nu a b y x) h1'
      rw [← nu_mul h, ← nu_mul h, ← nu_inv h] at this
      rw [this]
      by_cases he : e₁ = 0
      · simp [he]
      · simp [he, nu_mul h, hZ]
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl
  · obtain ⟨u, hu, e0, e1⟩ := key 0 0; exact ⟨u, hu, by simpa using e0, by simpa using e1⟩
  · obtain ⟨u, hu, e0, e1⟩ := key 0 1; exact ⟨u, hu, by simpa using e0, by simpa using e1⟩
  · obtain ⟨u, hu, e0, e1⟩ := key 1 0; exact ⟨u, hu, by simpa using e0, by simpa using e1⟩
  · obtain ⟨u, hu, e0, e1⟩ := key 1 1; exact ⟨u, hu, by simpa using e0, by simpa using e1⟩

omit [Finite G] in
theorem inner_R2 {T₀ T₁ : G}
    (h0 : T₀ = nu a b y x (r2rep 0) ∨ T₀ = nu a b y x (r2rep 0) * (a ^ 2 * b ^ 2))
    (h1 : T₁ = nu a b y x (r2rep 1) ∨ T₁ = nu a b y x (r2rep 1) * (a ^ 2 * b ^ 2)) :
    ∃ u ∈ nfSub h pR2 closed_pR2, u * nu a b y x (r2rep 0) * u⁻¹ = T₀ ∧
      u * nu a b y x (r2rep 1) * u⁻¹ = T₁ := by
  have hZ : a ^ 2 * b ^ 2 = nu a b y x zNF := zG_eq
  have key : ∀ e₀ e₁ : Fin 2, ∃ u ∈ nfSub h pR2 closed_pR2,
      u * nu a b y x (r2rep 0) * u⁻¹ =
        (if e₀ = 0 then nu a b y x (r2rep 0) else nu a b y x (r2rep 0) * (a ^ 2 * b ^ 2)) ∧
      u * nu a b y x (r2rep 1) * u⁻¹ =
        (if e₁ = 0 then nu a b y x (r2rep 1) else nu a b y x (r2rep 1) * (a ^ 2 * b ^ 2)) := by
    intro e₀ e₁
    obtain ⟨r, hr, h0', h1'⟩ := R2_inner e₀ e₁
    refine ⟨nu a b y x r, (nu_mem_nfSub h closed_pR2 r).2 hr, ?_, ?_⟩
    · have := congrArg (nu a b y x) h0'
      rw [← nu_mul h, ← nu_mul h, ← nu_inv h] at this
      rw [this]
      by_cases he : e₀ = 0
      · simp [he]
      · simp [he, nu_mul h, hZ]
    · have := congrArg (nu a b y x) h1'
      rw [← nu_mul h, ← nu_mul h, ← nu_inv h] at this
      rw [this]
      by_cases he : e₁ = 0
      · simp [he]
      · simp [he, nu_mul h, hZ]
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl
  · obtain ⟨u, hu, e0, e1⟩ := key 0 0; exact ⟨u, hu, by simpa using e0, by simpa using e1⟩
  · obtain ⟨u, hu, e0, e1⟩ := key 0 1; exact ⟨u, hu, by simpa using e0, by simpa using e1⟩
  · obtain ⟨u, hu, e0, e1⟩ := key 1 0; exact ⟨u, hu, by simpa using e0, by simpa using e1⟩
  · obtain ⟨u, hu, e0, e1⟩ := key 1 1; exact ⟨u, hu, by simpa using e0, by simpa using e1⟩

omit [Finite G] in
theorem cent_triv {g u c : G} (e : g * c * g⁻¹ = u * c * u⁻¹) :
    (u⁻¹ * g) * c * (u⁻¹ * g)⁻¹ = c := by
  calc (u⁻¹ * g) * c * (u⁻¹ * g)⁻¹ = u⁻¹ * (g * c * g⁻¹) * u := by group
    _ = u⁻¹ * (u * c * u⁻¹) * u := by rw [e]
    _ = c := by group

omit [Finite G] in
theorem comm_of_conj {g c : G} (e : g * c * g⁻¹ = c) : g * c = c * g := by
  calc g * c = (g * c * g⁻¹) * g := by group
    _ = c * g := by rw [e]

omit [Finite G] in
include h in
theorem cent_R1_of_gens {g : G} (hg0 : g * nu a b y x (r1rep 0) * g⁻¹ = nu a b y x (r1rep 0))
    (hg1 : g * nu a b y x (r1rep 1) * g⁻¹ = nu a b y x (r1rep 1)) :
    ∀ q, pR1 q → g * nu a b y x q * g⁻¹ = nu a b y x q := by
  intro q hq
  obtain ⟨m, _, n, _, hmn⟩ := R1_gen q hq
  have h0 : Commute g (nu a b y x (r1rep 0)) := comm_of_conj hg0
  have h1 : Commute g (nu a b y x (r1rep 1)) := comm_of_conj hg1
  have hq' : nu a b y x q = (nu a b y x (r1rep 0)) ^ m * (nu a b y x (r1rep 1)) ^ n := by
    rw [← hmn, ← nu_mul h, ← nu_pow h, ← nu_pow h]
  rw [hq']
  have hc : Commute g ((nu a b y x (r1rep 0)) ^ m * (nu a b y x (r1rep 1)) ^ n) :=
    (h0.pow_right m).mul_right (h1.pow_right n)
  calc g * ((nu a b y x (r1rep 0)) ^ m * (nu a b y x (r1rep 1)) ^ n) * g⁻¹
      = ((nu a b y x (r1rep 0)) ^ m * (nu a b y x (r1rep 1)) ^ n) * g * g⁻¹ := by rw [hc.eq]
    _ = _ := by group

omit [Finite G] in
include h in
theorem cent_R2_of_gens {g : G} (hg0 : g * nu a b y x (r2rep 0) * g⁻¹ = nu a b y x (r2rep 0))
    (hg1 : g * nu a b y x (r2rep 1) * g⁻¹ = nu a b y x (r2rep 1)) :
    ∀ q, pR2 q → g * nu a b y x q * g⁻¹ = nu a b y x q := by
  intro q hq
  obtain ⟨m, _, n, _, hmn⟩ := R2_gen q hq
  have h0 : Commute g (nu a b y x (r2rep 0)) := comm_of_conj hg0
  have h1 : Commute g (nu a b y x (r2rep 1)) := comm_of_conj hg1
  have hq' : nu a b y x q = (nu a b y x (r2rep 0)) ^ m * (nu a b y x (r2rep 1)) ^ n := by
    rw [← hmn, ← nu_mul h, ← nu_pow h, ← nu_pow h]
  rw [hq']
  have hc : Commute g ((nu a b y x (r2rep 0)) ^ m * (nu a b y x (r2rep 1)) ^ n) :=
    (h0.pow_right m).mul_right (h1.pow_right n)
  calc g * ((nu a b y x (r2rep 0)) ^ m * (nu a b y x (r2rep 1)) ^ n) * g⁻¹
      = ((nu a b y x (r2rep 0)) ^ m * (nu a b y x (r2rep 1)) ^ n) * g * g⁻¹ := by rw [hc.eq]
    _ = _ := by group

omit [Finite G] in
include h in
theorem R1R2_comm_G {p q : NF} (hp : pR1 p) (hq : pR2 q) :
    nu a b y x p * nu a b y x q = nu a b y x q * nu a b y x p := by
  rw [nu_mul h, nu_mul h, R1R2_comm p q hp hq]

theorem mem_R_of_kernel (H : Hyp14 G S a b y x) {g : G}
    (hk1 : ∀ i, g * nu a b y x (r1rep i) * g⁻¹ = nu a b y x (r1rep i) ∨
      g * nu a b y x (r1rep i) * g⁻¹ = nu a b y x (r1rep i) * (a ^ 2 * b ^ 2))
    (hk2 : ∀ i, g * nu a b y x (r2rep i) * g⁻¹ = nu a b y x (r2rep i) ∨
      g * nu a b y x (r2rep i) * g⁻¹ = nu a b y x (r2rep i) * (a ^ 2 * b ^ 2)) :
    g ∈ Rsub S a b := by
  have h := H.data
  obtain ⟨u, hu, hu0, hu1⟩ := inner_R1 h (hk1 0) (hk1 1)
  have hg₁0 : (u⁻¹ * g) * nu a b y x (r1rep 0) * (u⁻¹ * g)⁻¹ = nu a b y x (r1rep 0) :=
    cent_triv (by rw [hu0])
  have hg₁1 : (u⁻¹ * g) * nu a b y x (r1rep 1) * (u⁻¹ * g)⁻¹ = nu a b y x (r1rep 1) :=
    cent_triv (by rw [hu1])
  have hg₁R1 := cent_R1_of_gens h hg₁0 hg₁1
  have huS : u ∈ S := nfSub_le_S h closed_pR1 hu
  have hzu : u * (a ^ 2 * b ^ 2) = (a ^ 2 * b ^ 2) * u := z_central h huS
  have hucomm : ∀ i, u * nu a b y x (r2rep i) = nu a b y x (r2rep i) * u := by
    intro i
    obtain ⟨p, hp, hpe⟩ := hu
    rw [hpe]
    exact R1R2_comm_G h hp (r2rep_mem i)
  have hconj₁ : ∀ i, (u⁻¹ * g) * nu a b y x (r2rep i) * (u⁻¹ * g)⁻¹ =
      g * nu a b y x (r2rep i) * g⁻¹ := by
    intro i
    calc (u⁻¹ * g) * nu a b y x (r2rep i) * (u⁻¹ * g)⁻¹
        = u⁻¹ * (g * nu a b y x (r2rep i) * g⁻¹) * u := by group
      _ = g * nu a b y x (r2rep i) * g⁻¹ := by
        have hcomm1 : u * nu a b y x (r2rep i) = nu a b y x (r2rep i) * u := hucomm i
        have hcomm2 : u * (nu a b y x (r2rep i) * (a ^ 2 * b ^ 2)) =
            (nu a b y x (r2rep i) * (a ^ 2 * b ^ 2)) * u := by
          calc u * (nu a b y x (r2rep i) * (a ^ 2 * b ^ 2))
              = (u * nu a b y x (r2rep i)) * (a ^ 2 * b ^ 2) := by group
            _ = (nu a b y x (r2rep i) * u) * (a ^ 2 * b ^ 2) := by rw [hcomm1]
            _ = nu a b y x (r2rep i) * (u * (a ^ 2 * b ^ 2)) := by group
            _ = nu a b y x (r2rep i) * ((a ^ 2 * b ^ 2) * u) := by rw [hzu]
            _ = (nu a b y x (r2rep i) * (a ^ 2 * b ^ 2)) * u := by group
        rcases hk2 i with e | e
        · rw [e]
          calc u⁻¹ * nu a b y x (r2rep i) * u = u⁻¹ * (nu a b y x (r2rep i) * u) := by group
            _ = u⁻¹ * (u * nu a b y x (r2rep i)) := by rw [hcomm1]
            _ = nu a b y x (r2rep i) := by group
        · rw [e]
          calc u⁻¹ * (nu a b y x (r2rep i) * (a ^ 2 * b ^ 2)) * u
              = u⁻¹ * ((nu a b y x (r2rep i) * (a ^ 2 * b ^ 2)) * u) := by group
            _ = u⁻¹ * (u * (nu a b y x (r2rep i) * (a ^ 2 * b ^ 2))) := by rw [hcomm2]
            _ = nu a b y x (r2rep i) * (a ^ 2 * b ^ 2) := by group
  obtain ⟨u', hu', hu'0, hu'1⟩ := inner_R2 h (hk2 0) (hk2 1)
  have hg₂0 : (u'⁻¹ * (u⁻¹ * g)) * nu a b y x (r2rep 0) * (u'⁻¹ * (u⁻¹ * g))⁻¹ =
      nu a b y x (r2rep 0) := cent_triv (by rw [hconj₁ 0, hu'0])
  have hg₂1 : (u'⁻¹ * (u⁻¹ * g)) * nu a b y x (r2rep 1) * (u'⁻¹ * (u⁻¹ * g))⁻¹ =
      nu a b y x (r2rep 1) := cent_triv (by rw [hconj₁ 1, hu'1])
  have hg₂R2 := cent_R2_of_gens h hg₂0 hg₂1
  have hu'comm : ∀ q, pR1 q → u' * nu a b y x q = nu a b y x q * u' := by
    intro q hq
    obtain ⟨p, hp, hpe⟩ := hu'
    rw [hpe]
    exact (R1R2_comm_G h hq hp).symm
  have hg₂R1 : ∀ q, pR1 q → (u'⁻¹ * (u⁻¹ * g)) * nu a b y x q * (u'⁻¹ * (u⁻¹ * g))⁻¹ =
      nu a b y x q := by
    intro q hq
    calc (u'⁻¹ * (u⁻¹ * g)) * nu a b y x q * (u'⁻¹ * (u⁻¹ * g))⁻¹
        = u'⁻¹ * ((u⁻¹ * g) * nu a b y x q * (u⁻¹ * g)⁻¹) * u' := by group
      _ = u'⁻¹ * nu a b y x q * u' := by rw [hg₁R1 q hq]
      _ = nu a b y x q := by
        calc u'⁻¹ * nu a b y x q * u' = u'⁻¹ * (u' * nu a b y x q) := by
              rw [hu'comm q hq]; group
          _ = _ := by group
  have hcentR : u'⁻¹ * (u⁻¹ * g) ∈ centralizer ((Rsub S a b : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    rw [R_eq' H] at hw
    obtain ⟨p', hp', rfl⟩ := hw
    obtain ⟨q, hq, q', hq', rfl⟩ := R_decomp p' hp'
    have e : (u'⁻¹ * (u⁻¹ * g)) * nu a b y x (nfMul q q') * (u'⁻¹ * (u⁻¹ * g))⁻¹ =
        nu a b y x (nfMul q q') := by
      rw [← nu_mul h]
      calc (u'⁻¹ * (u⁻¹ * g)) * (nu a b y x q * nu a b y x q') * (u'⁻¹ * (u⁻¹ * g))⁻¹
          = ((u'⁻¹ * (u⁻¹ * g)) * nu a b y x q * (u'⁻¹ * (u⁻¹ * g))⁻¹) *
            ((u'⁻¹ * (u⁻¹ * g)) * nu a b y x q' * (u'⁻¹ * (u⁻¹ * g))⁻¹) := by group
        _ = _ := by rw [hg₂R1 q hq, hg₂R2 q' hq']
    exact (comm_of_conj e).symm
  rw [centralizer_R_eq H] at hcentR
  have hzR : zpowers (a ^ 2 * b ^ 2) ≤ Rsub S a b := Subgroup.zpowers_le.2 (z_mem_R H)
  have hR1R : nfSub h pR1 closed_pR1 ≤ Rsub S a b := by rw [R_eq' H]; exact R1_le_R h
  have hR2R : nfSub h pR2 closed_pR2 ≤ Rsub S a b := by
    rw [R_eq' H]; exact nfSub_le_nfSub h closed_pR2 closed_pR pR_of_pR2
  have hg : g = u * (u' * (u'⁻¹ * (u⁻¹ * g))) := by group
  rw [hg]
  exact mul_mem (hR1R hu) (mul_mem (hR2R hu') (hzR hcentR))

end Kernel

theorem exists_hom_R1 (H : Hyp14 G S a b y x) :
    ∃ ρ : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) →* Equiv.Perm (Fin 3),
      ∀ (g : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) (i j : Fin 3),
        ((g : G) * nu a b y x (r1rep i) * (g : G)⁻¹ = nu a b y x (r1rep j) ∨
          (g : G) * nu a b y x (r1rep i) * (g : G)⁻¹ =
            nu a b y x (r1rep j) * (a ^ 2 * b ^ 2)) ↔ ρ g i = j :=
  exists_hom_of_triple H closed_pR1 r1rep (fun g hg => (normalizes_R1R2 H g hg).1) r1rep_mem
    r1rep_sq r1_points r1rep_dist

theorem exists_hom_R2 (H : Hyp14 G S a b y x) :
    ∃ ρ : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) →* Equiv.Perm (Fin 3),
      ∀ (g : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) (i j : Fin 3),
        ((g : G) * nu a b y x (r2rep i) * (g : G)⁻¹ = nu a b y x (r2rep j) ∨
          (g : G) * nu a b y x (r2rep i) * (g : G)⁻¹ =
            nu a b y x (r2rep j) * (a ^ 2 * b ^ 2)) ↔ ρ g i = j :=
  exists_hom_of_triple H closed_pR2 r2rep (fun g hg => (normalizes_R1R2 H g hg).2) r2rep_mem
    r2rep_sq r2_points r2rep_dist

omit [Finite G] in
theorem conj_nu {g : G} {p : NF} (h : M12Data S a b y x) (hg : g = nu a b y x p) (q : NF) :
    g * nu a b y x q * g⁻¹ = nu a b y x (nfMul (nfMul p q) (nfInv p)) := by
  rw [hg, nu_mul h p q, nu_inv h p, nu_mul h]

theorem ker_eq (H : Hyp14 G S a b y x)
    (ρ₁ ρ₂ : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) →* Equiv.Perm (Fin 3))
    (h1 : ∀ (g : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) (i j : Fin 3),
        ((g : G) * nu a b y x (r1rep i) * (g : G)⁻¹ = nu a b y x (r1rep j) ∨
          (g : G) * nu a b y x (r1rep i) * (g : G)⁻¹ =
            nu a b y x (r1rep j) * (a ^ 2 * b ^ 2)) ↔ ρ₁ g i = j)
    (h2 : ∀ (g : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) (i j : Fin 3),
        ((g : G) * nu a b y x (r2rep i) * (g : G)⁻¹ = nu a b y x (r2rep j) ∨
          (g : G) * nu a b y x (r2rep i) * (g : G)⁻¹ =
            nu a b y x (r2rep j) * (a ^ 2 * b ^ 2)) ↔ ρ₂ g i = j) :
    (ρ₁.prod ρ₂).ker = (Rsub S a b).subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G)) := by
  have h := H.data
  have hZ : a ^ 2 * b ^ 2 = nu a b y x zNF := zG_eq
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hker
    have hρ₁ : ρ₁ g = 1 := congrArg Prod.fst hker
    have hρ₂ : ρ₂ g = 1 := congrArg Prod.snd hker
    exact mem_R_of_kernel H (fun i => (h1 g i i).2 (by rw [hρ₁]; rfl))
      (fun i => (h2 g i i).2 (by rw [hρ₂]; rfl))
  · intro hg
    rw [R_eq' H] at hg
    obtain ⟨p, hp, hpe⟩ := hg
    have key : ∀ (rep : Fin 3 → NF) (hrep : ∀ i, pR (rep i)) (i : Fin 3),
        (g : G) * nu a b y x (rep i) * (g : G)⁻¹ = nu a b y x (rep i) ∨
          (g : G) * nu a b y x (rep i) * (g : G)⁻¹ = nu a b y x (rep i) * (a ^ 2 * b ^ 2) := by
      intro rep hrep i
      rw [conj_nu h hpe]
      rcases R_conj_R p (rep i) hp (hrep i) with e | e
      · exact Or.inl (by rw [e])
      · exact Or.inr (by rw [e, hZ, nu_mul h])
    refine Prod.ext (Equiv.ext fun i => ?_) (Equiv.ext fun i => ?_)
    · exact (h1 g i i).1 (key r1rep (fun i => pR_of_pR1 _ (r1rep_mem i)) i)
    · exact (h2 g i i).1 (key r2rep (fun i => pR_of_pR2 _ (r2rep_mem i)) i)

theorem trans1 (H : Hyp14 G S a b y x)
    (ρ₁ : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) →* Equiv.Perm (Fin 3))
    (h1 : ∀ (g : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) (i j : Fin 3),
        ((g : G) * nu a b y x (r1rep i) * (g : G)⁻¹ = nu a b y x (r1rep j) ∨
          (g : G) * nu a b y x (r1rep i) * (g : G)⁻¹ =
            nu a b y x (r1rep j) * (a ^ 2 * b ^ 2)) ↔ ρ₁ g i = j) (i : Fin 3) :
    ∃ g : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)), ρ₁ g 0 = i := by
  have h := H.data
  have hZ : a ^ 2 * b ^ 2 = nu a b y x zNF := zG_eq
  have hc : nu a b y x (r1rep i) ∈ S := nu_mem h _
  have hcz : nu a b y x (r1rep i) * nu a b y x (r1rep i) = a ^ 2 * b ^ 2 := by
    rw [nu_mul h, r1rep_sq i, hZ]
  obtain ⟨g, hgC, hgH, hgsq⟩ := H.F1 _ hc hcz
  have hnorm := (normalizes_R1R2 H g hgC).1
  have ht1 : g * nu a b y x (r1rep i) * g⁻¹ ∈ nfSub h pR1 closed_pR1 := by
    rw [← hnorm, mem_cj]
    rw [show g⁻¹ * (g * nu a b y x (r1rep i) * g⁻¹) * g = nu a b y x (r1rep i) by group]
    exact (nu_mem_nfSub h closed_pR1 _).2 (r1rep_mem i)
  obtain ⟨p, hp, hpe⟩ := ht1
  rw [H0_eq h] at hgH
  obtain ⟨p', hp', hpe'⟩ := hgH
  have hpp : p = p' := nu_injective h (hpe.symm.trans hpe')
  subst hpp
  have hsq : nfMul p p = zNF := by
    rw [hpe, nu_mul h, hZ] at hgsq
    exact nu_injective h hgsq
  refine ⟨⟨g, hgC⟩⁻¹, ?_⟩
  have hρ : ρ₁ ⟨g, hgC⟩ i = 0 := by
    apply (h1 ⟨g, hgC⟩ i 0).1
    rcases H0_land_R1 p hp hp' hsq with e | e
    · exact Or.inl (by rw [hpe, e])
    · exact Or.inr (by rw [hpe, e, hZ, nu_mul h])
  calc ρ₁ ⟨g, hgC⟩⁻¹ 0 = ρ₁ ⟨g, hgC⟩⁻¹ (ρ₁ ⟨g, hgC⟩ i) := by rw [hρ]
    _ = i := by rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem trans2 (H : Hyp14 G S a b y x)
    (ρ₂ : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) →* Equiv.Perm (Fin 3))
    (h2 : ∀ (g : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) (i j : Fin 3),
        ((g : G) * nu a b y x (r2rep i) * (g : G)⁻¹ = nu a b y x (r2rep j) ∨
          (g : G) * nu a b y x (r2rep i) * (g : G)⁻¹ =
            nu a b y x (r2rep j) * (a ^ 2 * b ^ 2)) ↔ ρ₂ g i = j) (i : Fin 3) :
    ∃ g : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)), ρ₂ g 0 = i := by
  have h := H.data
  have hZ : a ^ 2 * b ^ 2 = nu a b y x zNF := zG_eq
  have hc : nu a b y x (r2rep i) ∈ S := nu_mem h _
  have hcz : nu a b y x (r2rep i) * nu a b y x (r2rep i) = a ^ 2 * b ^ 2 := by
    rw [nu_mul h, r2rep_sq i, hZ]
  obtain ⟨g, hgC, hgH, hgsq⟩ := H.F1 _ hc hcz
  have hnorm := (normalizes_R1R2 H g hgC).2
  have ht1 : g * nu a b y x (r2rep i) * g⁻¹ ∈ nfSub h pR2 closed_pR2 := by
    rw [← hnorm, mem_cj]
    rw [show g⁻¹ * (g * nu a b y x (r2rep i) * g⁻¹) * g = nu a b y x (r2rep i) by group]
    exact (nu_mem_nfSub h closed_pR2 _).2 (r2rep_mem i)
  obtain ⟨p, hp, hpe⟩ := ht1
  rw [H0_eq h] at hgH
  obtain ⟨p', hp', hpe'⟩ := hgH
  have hpp : p = p' := nu_injective h (hpe.symm.trans hpe')
  subst hpp
  have hsq : nfMul p p = zNF := by
    rw [hpe, nu_mul h, hZ] at hgsq
    exact nu_injective h hgsq
  refine ⟨⟨g, hgC⟩⁻¹, ?_⟩
  have hρ : ρ₂ ⟨g, hgC⟩ i = 0 := by
    apply (h2 ⟨g, hgC⟩ i 0).1
    rcases H0_land_R2 p hp hp' hsq with e | e
    · exact Or.inl (by rw [hpe, e])
    · exact Or.inr (by rw [hpe, e, hZ, nu_mul h])
  calc ρ₂ ⟨g, hgC⟩⁻¹ 0 = ρ₂ ⟨g, hgC⟩⁻¹ (ρ₂ ⟨g, hgC⟩ i) := by rw [hρ]
    _ = i := by rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

omit [Finite G] in
theorem point_move {g z c d t : G} (hgz : g * z = z * g) (hz2 : z * z = 1)
    (e : g * c * g⁻¹ = d ∨ g * c * g⁻¹ = d * z) (ht : t = c ∨ t = c * z) :
    g * t * g⁻¹ = d ∨ g * t * g⁻¹ = d * z := by
  have hgzg : g * z * g⁻¹ = z := by rw [hgz]; group
  rcases ht with rfl | rfl
  · exact e
  · have : g * (c * z) * g⁻¹ = (g * c * g⁻¹) * z := by
      calc g * (c * z) * g⁻¹ = (g * c * g⁻¹) * (g * z * g⁻¹) := by group
        _ = _ := by rw [hgzg]
    rw [this]
    rcases e with e | e
    · exact Or.inr (by rw [e])
    · exact Or.inl (by rw [e, mul_assoc, hz2, mul_one])

theorem no_fuse (H : Hyp14 G S a b y x)
    (ρ₁ ρ₂ : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) →* Equiv.Perm (Fin 3))
    (h1 : ∀ (g : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) (i j : Fin 3),
        ((g : G) * nu a b y x (r1rep i) * (g : G)⁻¹ = nu a b y x (r1rep j) ∨
          (g : G) * nu a b y x (r1rep i) * (g : G)⁻¹ =
            nu a b y x (r1rep j) * (a ^ 2 * b ^ 2)) ↔ ρ₁ g i = j)
    (h2 : ∀ (g : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) (i j : Fin 3),
        ((g : G) * nu a b y x (r2rep i) * (g : G)⁻¹ = nu a b y x (r2rep j) ∨
          (g : G) * nu a b y x (r2rep i) * (g : G)⁻¹ =
            nu a b y x (r2rep j) * (a ^ 2 * b ^ 2)) ↔ ρ₂ g i = j)
    (g : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) (hg1 : ρ₁ g 2 = 0) (hg2 : ρ₂ g 1 = 0) :
    False := by
  have h := H.data
  have hZ : a ^ 2 * b ^ 2 = nu a b y x zNF := zG_eq
  obtain ⟨q, hq, q', hq', hqq'⟩ := x_decomp
  have e1 := (h1 g 2 0).2 hg1
  have e2 := (h2 g 1 0).2 hg2
  have hqG : nu a b y x q = nu a b y x (r1rep 2) ∨
      nu a b y x q = nu a b y x (r1rep 2) * (a ^ 2 * b ^ 2) := by
    rcases hq with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by rw [hZ, nu_mul h])
  have hq'G : nu a b y x q' = nu a b y x (r2rep 1) ∨
      nu a b y x q' = nu a b y x (r2rep 1) * (a ^ 2 * b ^ 2) := by
    rcases hq' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by rw [hZ, nu_mul h])
  have A := point_move (z_comm_C g.2) (z_sq h) e1 hqG
  have B := point_move (z_comm_C g.2) (z_sq h) e2 hq'G
  have hxdec : x = nu a b y x q * nu a b y x q' := by
    rw [nu_mul h, hqq']; simp [nu]
  have hgx : (g : G) * x * (g : G)⁻¹ =
      ((g : G) * nu a b y x q * (g : G)⁻¹) * ((g : G) * nu a b y x q' * (g : G)⁻¹) := by
    calc (g : G) * x * (g : G)⁻¹ = (g : G) * (nu a b y x q * nu a b y x q') * (g : G)⁻¹ := by
          rw [← hxdec]
      _ = _ := by group
  have hU : (g : G) * x * (g : G)⁻¹ ∈ closure ({a * a, b * b} : Set G) := by
    rw [U_eq h, hgx]
    obtain ⟨α, hα, hAe⟩ : ∃ α ∈ [r1rep 0, nfMul (r1rep 0) zNF],
        (g : G) * nu a b y x q * (g : G)⁻¹ = nu a b y x α := by
      rcases A with e | e
      · exact ⟨r1rep 0, by simp, e⟩
      · exact ⟨nfMul (r1rep 0) zNF, by simp, by rw [e, hZ, nu_mul h]⟩
    obtain ⟨β, hβ, hBe⟩ : ∃ β ∈ [r2rep 0, nfMul (r2rep 0) zNF],
        (g : G) * nu a b y x q' * (g : G)⁻¹ = nu a b y x β := by
      rcases B with e | e
      · exact ⟨r2rep 0, by simp, e⟩
      · exact ⟨nfMul (r2rep 0) zNF, by simp, by rw [e, hZ, nu_mul h]⟩
    rw [hAe, hBe, nu_mul h]
    have := point00_prod' α hα β hβ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with e | e
    · rw [e]; exact (nu_mem_nfSub h closed_pU _).2 pU_two_zero
    · rw [e]; exact (nu_mem_nfSub h closed_pU _).2 pU_zero_two
  exact H.F2 g g.2 hU

omit [Finite G] in
theorem point_back {g z t : G} (hgz : g * z = z * g)
    (e : g * (t * z) * g⁻¹ = t * z ∨ g * (t * z) * g⁻¹ = (t * z) * z) :
    g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * z := by
  have hgzg : g * z * g⁻¹ = z := by rw [hgz]; group
  have : g * (t * z) * g⁻¹ = (g * t * g⁻¹) * z := by
    calc g * (t * z) * g⁻¹ = (g * t * g⁻¹) * (g * z * g⁻¹) := by group
      _ = _ := by rw [hgzg]
  rw [this] at e
  rcases e with e | e
  · exact Or.inl (mul_right_cancel e)
  · exact Or.inr (mul_right_cancel e)

omit [Finite G] in
theorem fixed_point_gen (h : M12Data S a b y x) {pk : NF → Prop} {rep : Fin 3 → NF}
    (hk : ∀ q, pk q → q ≠ (0, 0, 0, 0) → q ≠ zNF → nfMul q q = zNF)
    (hpoints : ∀ q, pk q → nfMul q q = zNF → ∃ i, q = rep i ∨ q = nfMul (rep i) zNF)
    {W : G} (hWz : W * (a ^ 2 * b ^ 2) = (a ^ 2 * b ^ 2) * W)
    (hWfix : ∀ j, ¬ (W * nu a b y x (rep j) * W⁻¹ = nu a b y x (rep j) ∨
      W * nu a b y x (rep j) * W⁻¹ = nu a b y x (rep j) * (a ^ 2 * b ^ 2)))
    {q : NF} (hq : pk q)
    (e : W * nu a b y x q * W⁻¹ = nu a b y x q ∨
      W * nu a b y x q * W⁻¹ = nu a b y x q * (a ^ 2 * b ^ 2)) :
    q = (0, 0, 0, 0) ∨ q = zNF := by
  have hZ : a ^ 2 * b ^ 2 = nu a b y x zNF := zG_eq
  by_contra hne
  push Not at hne
  obtain ⟨j, hj⟩ := hpoints q hq (hk q hq hne.1 hne.2)
  apply hWfix j
  rcases hj with rfl | rfl
  · exact e
  · have hN : nu a b y x (nfMul (rep j) zNF) = nu a b y x (rep j) * (a ^ 2 * b ^ 2) := by
      rw [hZ, nu_mul h]
    rw [hN] at e
    exact point_back hWz e

theorem lemma14_3_conc (H : Hyp14 G S a b y x) :
    Lemma14_3Conc G (a ^ 2 * b ^ 2) (Rsub S a b) (R1sub a b y) := by
  classical
  have h := H.data
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : a ^ 2 * b ^ 2 = nu a b y x zNF := zG_eq
  obtain ⟨ρ₁, h1⟩ := exists_hom_R1 H
  obtain ⟨ρ₂, h2⟩ := exists_hom_R2 H
  have hker := ker_eq H ρ₁ ρ₂ h1 h2
  have hRn := H.normal
  let ρ := ρ₁.prod ρ₂
  let e₁ : (↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) ⧸
      (Rsub S a b).subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G))) ≃* ρ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ρ)
  have hS' : Nat.card (S.subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G))) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe H.sylow.1).toEquiv]; exact h.card
  have hidx := Subgroup.card_mul_index (S.subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G)))
  have hR32 : Nat.card ((Rsub S a b).subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G))) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (R_le_C H)).toEquiv, R_eq' H]
    exact card_R h
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Rsub S a b).subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G)))
  have hrange : Nat.card ρ.range = Nat.card (↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) ⧸
      (Rsub S a b).subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G))) :=
    (Nat.card_congr e₁.toEquiv).symm
  have hcard : ∃ m, Odd m ∧ Nat.card ρ.range = 2 * m := by
    refine ⟨(S.subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G))).index,
      Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 H.sylow.2.2), ?_⟩
    rw [hrange]
    rw [hS'] at hidx
    rw [hR32] at hq
    omega
  have ht1 : ∀ i, ∃ t ∈ ρ.range, t.1 0 = i := fun i => by
    obtain ⟨g, hg⟩ := trans1 H ρ₁ h1 i
    exact ⟨ρ g, ⟨g, rfl⟩, hg⟩
  have ht2 : ∀ i, ∃ t ∈ ρ.range, t.2 0 = i := fun i => by
    obtain ⟨g, hg⟩ := trans2 H ρ₂ h2 i
    exact ⟨ρ g, ⟨g, rfl⟩, hg⟩
  have hT2 : ∀ t ∈ ρ.range, ¬ (t.1 2 = 0 ∧ t.2 1 = 0) := by
    rintro _ ⟨g, rfl⟩ ⟨hg1, hg2⟩
    exact no_fuse H ρ₁ ρ₂ h1 h2 g hg1 hg2
  have hequiv := exists_equiv_perm_three ρ.range hcard ht1 ht2 hT2
  have hcard6 := card_eq_six ρ.range hcard ht1 hT2
  refine ⟨H.normal, ⟨e₁.trans hequiv.some⟩, ?_, ?_⟩
  ·
    intro X r hr hXr
    have hrR : (r : G) ∈ Rsub S a b := hr
    have h192 : Nat.card ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) = 192 := by
      rw [hR32, ← hrange, hcard6] at hq
      omega
    have hXne : (X : Subgroup ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) ≠ ⊥ :=
      X.ne_bot_of_dvd_card (by rw [h192]; norm_num)
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hXne
    have hwX : (w : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) ∈ X := w.2
    have hW3 : (w : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) ^ 3 = 1 := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp X.isPGroup'
      have hdvd192 : Nat.card X ∣ 192 :=
        h192 ▸ Subgroup.card_subgroup_dvd_card (X : Subgroup ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)))
      have hn1 : n ≤ 1 := by
        by_contra hn2
        have h9 : 3 ^ 2 ∣ 3 ^ n := Nat.pow_dvd_pow 3 (by omega)
        rw [← hn] at h9
        have := h9.trans hdvd192
        omega
      have hord : orderOf w ∣ Nat.card X := orderOf_dvd_natCard w
      have h3 : orderOf w ∣ 3 := by
        rw [hn] at hord
        refine hord.trans ?_
        interval_cases n <;> simp
      have hw3 : w ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 h3
      have := congrArg (fun t : X => ((t : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))))) hw3
      simpa using this
    set W : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) := (w : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)))
      with hW
    have hρW : ρ W ≠ 1 := by
      intro e
      have hmem : W ∈ ρ.ker := e
      rw [hker] at hmem
      have hWR : (W : G) ∈ Rsub S a b := hmem
      have hWS : (W : G) ∈ S := nfSub_le_S h closed_pR (by rw [← R_eq' H]; exact hWR)
      obtain ⟨m, hm⟩ := H.sylow.2.1 ⟨(W : G), hWS⟩
      have hm' : (W : G) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have h3' : (W : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hW3
      have hg := pow_gcd_eq_one.2 ⟨h3', hm'⟩
      have hg1 : Nat.gcd 3 (2 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num)
      rw [hg1, pow_one] at hg
      apply hw1
      apply Subtype.ext
      exact Subtype.ext hg
    have hu : ρ W ∈ ρ.range := ⟨W, rfl⟩
    have hu3 : (ρ W) ^ 3 = 1 := by rw [← map_pow, hW3, map_one]
    have hfix1 := fixed_point_free_of_order_three ρ.range hcard6 ht1 hu hρW hu3
    have hfix2 := fixed_point_free_of_order_three_snd ρ.range hcard6 ht2 hu hρW hu3
    have hWz : (W : G) * (a ^ 2 * b ^ 2) = (a ^ 2 * b ^ 2) * (W : G) := z_comm_C W.2
    have hWfix1 : ∀ j, ¬ ((W : G) * nu a b y x (r1rep j) * (W : G)⁻¹ = nu a b y x (r1rep j) ∨
        (W : G) * nu a b y x (r1rep j) * (W : G)⁻¹ = nu a b y x (r1rep j) * (a ^ 2 * b ^ 2)) :=
      fun j hj => hfix1 j ((h1 W j j).1 hj)
    have hWfix2 : ∀ j, ¬ ((W : G) * nu a b y x (r2rep j) * (W : G)⁻¹ = nu a b y x (r2rep j) ∨
        (W : G) * nu a b y x (r2rep j) * (W : G)⁻¹ = nu a b y x (r2rep j) * (a ^ 2 * b ^ 2)) :=
      fun j hj => hfix2 j ((h2 W j j).1 hj)
    obtain ⟨p, hp, hpe⟩ : ∃ p, pR p ∧ (r : G) = nu a b y x p := by
      rw [R_eq' H] at hrR
      obtain ⟨p, hp, e⟩ := hrR
      exact ⟨p, hp, e⟩
    obtain ⟨q, hq1, q', hq2, hqq⟩ := R_decomp p hp
    have hrdec : (r : G) = nu a b y x q * nu a b y x q' := by rw [hpe, ← hqq, nu_mul h]
    have hWr : (W : G) * (r : G) * (W : G)⁻¹ = (r : G) := by
      have e := congrArg Subtype.val (hXr W hwX)
      calc (W : G) * (r : G) * (W : G)⁻¹ = (r : G) * (W : G) * (W : G)⁻¹ := by
            rw [show ((W * r : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) : G) = (W : G) * (r : G)
              from rfl, show ((r * W : ↥(centralizer ({a ^ 2 * b ^ 2} : Set G))) : G) =
                (r : G) * (W : G) from rfl] at e
            rw [e]
        _ = (r : G) := by group
    have hnorm := normalizes_R1R2 H W W.2
    have hA : (W : G) * nu a b y x q * (W : G)⁻¹ ∈ nfSub h pR1 closed_pR1 := by
      rw [← hnorm.1, mem_cj]
      rw [show (W : G)⁻¹ * ((W : G) * nu a b y x q * (W : G)⁻¹) * (W : G) = nu a b y x q by group]
      exact (nu_mem_nfSub h closed_pR1 q).2 hq1
    have hB : (W : G) * nu a b y x q' * (W : G)⁻¹ ∈ nfSub h pR2 closed_pR2 := by
      rw [← hnorm.2, mem_cj]
      rw [show (W : G)⁻¹ * ((W : G) * nu a b y x q' * (W : G)⁻¹) * (W : G) = nu a b y x q' by group]
      exact (nu_mem_nfSub h closed_pR2 q').2 hq2
    have hAB : ((W : G) * nu a b y x q * (W : G)⁻¹) * ((W : G) * nu a b y x q' * (W : G)⁻¹) =
        nu a b y x q * nu a b y x q' := by
      rw [← hrdec, ← hWr]
      calc ((W : G) * nu a b y x q * (W : G)⁻¹) * ((W : G) * nu a b y x q' * (W : G)⁻¹)
          = (W : G) * (nu a b y x q * nu a b y x q') * (W : G)⁻¹ := by group
        _ = _ := by rw [← hrdec, hWr]
    have hz2 : (a ^ 2 * b ^ 2) * (a ^ 2 * b ^ 2) = 1 := z_sq h
    have he : (nu a b y x q)⁻¹ * ((W : G) * nu a b y x q * (W : G)⁻¹) =
        nu a b y x q' * ((W : G) * nu a b y x q' * (W : G)⁻¹)⁻¹ := by
      calc (nu a b y x q)⁻¹ * ((W : G) * nu a b y x q * (W : G)⁻¹)
          = (nu a b y x q)⁻¹ * (((W : G) * nu a b y x q * (W : G)⁻¹) *
              ((W : G) * nu a b y x q' * (W : G)⁻¹)) * ((W : G) * nu a b y x q' * (W : G)⁻¹)⁻¹ := by
            group
        _ = (nu a b y x q)⁻¹ * (nu a b y x q * nu a b y x q') *
              ((W : G) * nu a b y x q' * (W : G)⁻¹)⁻¹ := by rw [hAB]
        _ = _ := by group
    have heR1 : (nu a b y x q)⁻¹ * ((W : G) * nu a b y x q * (W : G)⁻¹) ∈ nfSub h pR1 closed_pR1 :=
      mul_mem (inv_mem ((nu_mem_nfSub h closed_pR1 q).2 hq1)) hA
    have heR2 : (nu a b y x q)⁻¹ * ((W : G) * nu a b y x q * (W : G)⁻¹) ∈ nfSub h pR2 closed_pR2 := by
      rw [he]
      exact mul_mem ((nu_mem_nfSub h closed_pR2 q').2 hq2) (inv_mem hB)
    obtain ⟨p₀, hp₀1, hp₀e⟩ := heR1
    have hp₀2 : pR2 p₀ := (nu_mem_nfSub h closed_pR2 p₀).1 (hp₀e ▸ heR2)
    have hε : (nu a b y x q)⁻¹ * ((W : G) * nu a b y x q * (W : G)⁻¹) = 1 ∨
        (nu a b y x q)⁻¹ * ((W : G) * nu a b y x q * (W : G)⁻¹) = a ^ 2 * b ^ 2 := by
      rcases R1R2_inter p₀ hp₀1 hp₀2 with e0 | e0
      · left; rw [hp₀e, e0, nu_zero]
      · right; rw [hp₀e, e0, hZ]
    have hAc : (W : G) * nu a b y x q * (W : G)⁻¹ = nu a b y x q ∨
        (W : G) * nu a b y x q * (W : G)⁻¹ = nu a b y x q * (a ^ 2 * b ^ 2) := by
      rcases hε with e | e
      · left
        calc (W : G) * nu a b y x q * (W : G)⁻¹
            = nu a b y x q * ((nu a b y x q)⁻¹ * ((W : G) * nu a b y x q * (W : G)⁻¹)) := by group
          _ = nu a b y x q := by rw [e, mul_one]
      · right
        calc (W : G) * nu a b y x q * (W : G)⁻¹
            = nu a b y x q * ((nu a b y x q)⁻¹ * ((W : G) * nu a b y x q * (W : G)⁻¹)) := by group
          _ = nu a b y x q * (a ^ 2 * b ^ 2) := by rw [e]
    have hBe : (W : G) * nu a b y x q' * (W : G)⁻¹ =
        ((nu a b y x q)⁻¹ * ((W : G) * nu a b y x q * (W : G)⁻¹))⁻¹ * nu a b y x q' := by
      rw [he]
      group
    have hBc : (W : G) * nu a b y x q' * (W : G)⁻¹ = nu a b y x q' ∨
        (W : G) * nu a b y x q' * (W : G)⁻¹ = nu a b y x q' * (a ^ 2 * b ^ 2) := by
      rcases hε with e | e
      · left; rw [hBe, e]; group
      · right
        rw [hBe, e, inv_eq_of_mul_eq_one_right hz2]
        exact (z_central h (nu_mem h q')).symm
    have hq0 := fixed_point_gen h R1_order4 r1_points hWz hWfix1 hq1 hAc
    have hq'0 := fixed_point_gen h R2_order4 r2_points hWz hWfix2 hq2 hBc
    rw [hrdec]
    rcases hq0 with rfl | rfl <;> rcases hq'0 with rfl | rfl
    · rw [nu_zero, mul_one]; exact one_mem _
    · rw [nu_zero, one_mul, ← hZ]; exact mem_zpowers _
    · rw [nu_zero, mul_one, ← hZ]; exact mem_zpowers _
    · rw [← hZ, hz2]; exact one_mem _
  ·
    have hR1 := R1_eq h
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ nfSub h pR1 closed_pR1 := by rw [← hR1]; exact hn
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ R1sub a b y
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ Subgroup.closure ({a⁻¹ * b, a * b * y} : Set G)
    rw [hR1, ← (normalizes_R1R2 H g g.2).1, mem_cj]
    rw [show (g : G)⁻¹ * ((g : G) * (n : G) * (g : G)⁻¹) * (g : G) = n by group]
    exact hn'

theorem iv3_14_3b :
    ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G) (a b y x : G), M12Data S a b y x →
      Sylow2In S (centralizer ({a ^ 2 * b ^ 2} : Set G)) →
        CFSG.oddCore ↥(centralizer ({a ^ 2 * b ^ 2} : Set G)) = ⊥ →
        (∀ c ∈ S, c * c = a ^ 2 * b ^ 2 →
          ∃ g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G), g * c * g⁻¹ ∈ closure ({a, b} : Set G) ∧
            (g * c * g⁻¹) * (g * c * g⁻¹) = a ^ 2 * b ^ 2) →
        (∀ g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G),
          g * x * g⁻¹ ∉ closure ({a * a, b * b} : Set G)) →
        ((Rsub S a b).subgroupOf (centralizer ({a ^ 2 * b ^ 2} : Set G))).Normal →
        Lemma14_3Conc G (a ^ 2 * b ^ 2) (Rsub S a b) (R1sub a b y) :=
  fun _ _ _ _ _ _ _ _ h hS hO h1 h2 hn => lemma14_3_conc ⟨h, hS, hO, h1, h2, hn⟩

end CFSG.GH74.GLS.Stage1.Thm6.Sec14
