module

public import CFSG.CGT.PushingUpLit.K1R.SporBase
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGJ2
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGJ3
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Card
public import CFSG.Sporadic.J1

public section

namespace CFSG.CGT.PushingUpLit.K1R

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

section General

variable {D : Type} [Group D]

theorem disjoint_centralizer_of_center_eq_bot {S Q : Subgroup D} (hZ : center S = ⊥)
    (hQ : Q ≤ centralizer (S : Set D)) : Disjoint S Q := by
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  obtain ⟨hxS, hxQ⟩ := mem_inf.1 hx
  have hxZ : (⟨x, hxS⟩ : S) ∈ center S := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.1 (hQ hxQ) y y.2)
  rw [hZ, mem_bot] at hxZ
  exact mem_bot.2 (congrArg Subtype.val hxZ)

theorem card_sup_of_le_centralizer {S H Q : Subgroup D} (hZ : center S = ⊥) (hHS : H ≤ S)
    (hQ : Q ≤ centralizer (S : Set D)) : Nat.card ↥(Q ⊔ H) = Nat.card Q * Nat.card H := by
  refine CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Q H ?_ ?_
  · intro h hh
    refine Subgroup.centralizer_le_normalizer (Q : Set D) ?_
    rw [mem_centralizer_iff]
    intro q hq
    exact (mem_centralizer_iff.1 (hQ hq) h (hHS hh)).symm
  · exact (disjoint_centralizer_of_center_eq_bot hZ hQ).symm.mono_right hHS

theorem NoFour.exists_mul_self_ne_one [Finite D] {Q : Subgroup D} (h : NoFour Q)
    (h2 : 2 < Nat.card Q) : ∃ g ∈ Q, g * g ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain hbot | ⟨x, hx, hx1⟩ := Q.bot_or_exists_ne_one
  · rw [hbot, card_bot] at h2
    omega
  have hle : Q ≤ zpowers x := by
    intro y hy
    have hxy : x * y = y * x := by
      have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hcon _ (mul_mem hx hy))
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hcon y hy),
        inv_eq_of_mul_eq_one_right (hcon x hx)] at h1
      exact h1.symm
    rcases h x hx y hy (hcon x hx) (hcon y hy) hxy with h' | h' | h'
    · exact absurd h' hx1
    · rw [h']
      exact one_mem _
    · rw [← h']
      exact mem_zpowers x
  have hox : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hcon x hx) hx1
  have := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hox] at this
  omega

theorem sq_conj_eq_of_card_eq_three [Finite D] {N : Subgroup D} (hN : Nat.card N = 3) {s : D}
    (hs : ∀ r ∈ N, s * r * s⁻¹ ∈ N) : ∀ r ∈ N, s * s * r * (s * s)⁻¹ = r := by
  classical
  intro r hr
  by_cases hr1 : r = 1
  · rw [hr1]
    group
  have hor : orderOf r = 3 := by
    have h1 := Subgroup.orderOf_dvd_natCard N hr
    rw [hN] at h1
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hr1
    · exact h
  have hNz : N = zpowers r := by
    refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hr) (le_of_eq ?_)).symm
    rw [hN, Nat.card_zpowers, hor]
  have h1 : s * r * s⁻¹ ∈ zpowers r := by
    rw [← hNz]
    exact hs r hr
  rw [mem_zpowers_iff_mem_range_orderOf, hor] at h1
  simp only [Finset.mem_image, Finset.mem_range] at h1
  obtain ⟨k, hk, hkr⟩ := h1
  have hr3 : r ^ 3 = 1 := by
    rw [← hor]
    exact pow_orderOf_eq_one r
  interval_cases k
  · exfalso
    apply hr1
    have h0 : s * r * s⁻¹ = 1 := by rw [← hkr, pow_zero]
    calc r = s⁻¹ * (s * r * s⁻¹) * s := by group
      _ = 1 := by rw [h0]; group
  · have hc : s * r * s⁻¹ = r := by rw [← hkr, pow_one]
    calc s * s * r * (s * s)⁻¹ = s * (s * r * s⁻¹) * s⁻¹ := by group
      _ = r := by rw [hc, hc]
  · have hc : s * r * s⁻¹ = r ^ 2 := hkr.symm
    calc s * s * r * (s * s)⁻¹ = s * (s * r * s⁻¹) * s⁻¹ := by group
      _ = s * r ^ 2 * s⁻¹ := by rw [hc]
      _ = (s * r * s⁻¹) ^ 2 := conj_pow.symm
      _ = (r ^ 2) ^ 2 := by rw [hc]
      _ = r := by rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hr3, one_mul]

end General

theorem j1_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .J1 := by
  intro D _ _ hD hs n hn K _ _ hK α hα hin S hSα hSn hSK _ Q hQ hQp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hs
  obtain ⟨t, ht, rfl, -, -, -, hScard, hZS⟩ := innerRoot_setup hD hn hK hα hin hSα hSn hSK
  have hQS : Q ≤ centralizer (S : Set D) := hQ.trans inf_le_right
  have h4 : 2 ^ 2 ∣ Nat.card S := by
    rw [hScard]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 hn) _
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := S) 2 h4
  have hcard := card_sup_of_le_centralizer hZS (map_subtype_le H) hQS
  rw [card_map_of_injective S.subtype_injective, hH] at hcard
  have hdvd := Subgroup.card_subgroup_dvd_card (Q ⊔ H.map S.subtype)
  have hDc : Nat.card D = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  rw [hcard, hDc] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  rw [hk] at hdvd ⊢
  by_contra hgt
  push Not at hgt
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> norm_num at hgt
  have := (Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 hk2) (2 ^ 2)).trans hdvd
  norm_num at this

open CFSG.ComponentClassification.M12Cover (FourClassesLarge centralizerEquiv
  centralizerSubgroupEquiv fourClassesLarge_m12) in
theorem m12_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .M12 := by
  intro D _ _ hD hs n hn K _ _ hK α hα hin S hSα hSn hSK hnf Q hQ hQp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hs
  obtain ⟨t, ht, rfl, -, -, -, hScard, hZS⟩ := innerRoot_setup hD hn hK hα hin hSα hSn hSK
  rw [Sporadic.eqLocus_conj t] at hnf hQ hSα
  have hQC : Q ≤ centralizer ({t} : Set D) := hQ.trans inf_le_left
  have hQS : Q ≤ centralizer (S : Set D) := hQ.trans inf_le_right
  have hle : Q ⊔ S ≤ centralizer ({t} : Set D) := sup_le hQC hSα
  have hcard : Nat.card ↥(Q ⊔ S) = Nat.card Q * Nat.card S :=
    card_sup_of_le_centralizer hZS le_rfl hQS
  have hdvd : Nat.card Q * Nat.card S ∣ Nat.card (centralizer ({t} : Set D)) :=
    hcard ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  rw [hk, hScard] at hdvd
  rw [hk]
  have hC := CFSG.Sporadic.Schreier.card_centralizer_involution_of_mulEquiv_M12 e ht
  have hS960 : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 960 :=
    (Dvd.intro_left _ rfl).trans (hdvd.trans (by rcases hC with h | h <;> rw [h] <;> norm_num))
  have := lt_of_sl2Order_dvd (by norm_num) (show 960 < 2 ^ 10 by norm_num) hS960
  have hn2 : n = 2 := by interval_cases n <;> first | rfl | norm_num at hS960
  subst hn2
  norm_num at hdvd hScard
  rcases hC with hC | hC
  · rw [hC] at hdvd
    have := (Dvd.intro_left _ rfl : 60 ∣ 2 ^ k * 60).trans hdvd
    norm_num at this
  rw [hC] at hdvd
  have h240 : (240 : ℕ) = 4 * 60 := by norm_num
  rw [h240] at hdvd
  have hk4 : 2 ^ k ∣ 4 := Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 60) hdvd
  by_contra hgt
  push Not at hgt
  have hk2 : k = 2 := by
    have h1 := Nat.le_of_dvd (by norm_num) hk4
    have hk3 : k ≤ 2 := by
      by_contra h
      push Not at h
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    interval_cases k <;> first | rfl | norm_num at hgt
  subst hk2
  have hQS_eq : Q ⊔ S = centralizer ({t} : Set D) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hC, hcard, hk, hScard]; norm_num)
  obtain ⟨g, hgQ, hgg⟩ := (hnf.mono hQ).exists_mul_self_ne_one (by rw [hk]; norm_num)
  have hg4 : g ^ 4 = 1 := by
    have h1 := Subgroup.orderOf_dvd_natCard Q hgQ
    rw [hk] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 (by simpa using h1)
  have hQc : IsMulCommutative Q := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hk
  have hgc : ∀ c ∈ centralizer ({t} : Set D), c * g = g * c := by
    intro c hc
    rw [← hQS_eq] at hc
    have hle' : Q ⊔ S ≤ centralizer ({g} : Set D) := by
      refine sup_le (fun q hq => ?_) (fun s hs => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hQc.is_comm.comm (⟨q, hq⟩ : Q) ⟨g, hgQ⟩)
      · rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.1 (hQS hgQ) s hs
    exact mem_centralizer_singleton_iff.1 (hle' hc)
  have hF : FourClassesLarge ↥(centralizer ({t} : Set D)) := by
    let e' : D ≃* NativeSporadic.M12 := e
    refine CFSG.ComponentClassification.M12Cover.FourClassesLarge.of_mulEquiv
      (centralizerEquiv e' t) ?_
    refine CFSG.ComponentClassification.M12Cover.FourClassesLarge.of_mulEquiv
      (centralizerSubgroupEquiv NativeSporadic.M12 (e' t)) ?_
    apply fourClassesLarge_m12 (e' t).2
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  set g' : centralizer ({t} : Set D) := ⟨g, hQC hgQ⟩ with hg'
  have h5 := hF g' (Subtype.ext (by simpa [hg'] using hg4))
    (fun h => hgg (by simpa [hg', pow_two] using congrArg Subtype.val h))
  have hsub : Subsingleton {y : centralizer ({t} : Set D) // IsConj g' y} := by
    have key : ∀ y : centralizer ({t} : Set D), IsConj g' y → y = g' := by
      intro y hy
      obtain ⟨c, rfl⟩ := isConj_iff.1 hy
      apply Subtype.ext
      simp only [hg', Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hgc c c.2, mul_inv_cancel_right]
    constructor
    rintro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩
    exact Subtype.ext ((key y₁ hy₁).trans (key y₂ hy₂).symm)
  have := Finite.card_le_one_iff_subsingleton.2 hsub
  omega

open CFSG.Sporadic.SmallOddCore
  (cti_j2_involution_local_components_ambient_centralizer_order_twelve) in
theorem j2_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .J2 := by
  refine InnerKernelSelector.of_false
    fun D _ _ hD hs n hn K _ _ hK α hα hin S hSα hSn hSK hnf => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, rfl, -, hcomp, -, hScard, hZS⟩ := innerRoot_setup hD hn hK hα hin hSα hSn hSK
  rw [Sporadic.eqLocus_conj t] at hnf hSα
  have h12 : Nat.card (centralizer (S : Set D)) = 12 := by
    obtain ⟨e⟩ := hs
    exact cti_j2_involution_local_components_ambient_centralizer_order_twelve ⟨e⟩ ht hcomp
  set Y := centralizer (S : Set D) with hY
  have htY : t ∈ Y := by
    rw [hY, mem_centralizer_iff]
    intro s hs
    exact mem_centralizer_singleton_iff.1 (hSα hs)
  set tY : Y := ⟨t, htY⟩ with htYdef
  have htY2 : orderOf tY = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hT : IsPGroup 2 (zpowers tY) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htY2, pow_one])
  obtain ⟨P, hP⟩ := hT.exists_le_sylow
  have htP : tY ∈ (P : Subgroup Y) := hP (mem_zpowers tY)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hcop := P.card_coprime_index
  have hmul := (P : Subgroup Y).card_mul_index
  rw [h12, hk] at hmul
  rw [hk] at hcop
  have h2P : 2 ∣ Nat.card (P : Subgroup Y) := by
    have := orderOf_dvd_natCard (⟨tY, htP⟩ : (P : Subgroup Y))
    rwa [Subgroup.orderOf_mk, htY2] at this
  rw [hk] at h2P
  have hk2 : k = 2 := by
    have hk12 : 2 ^ k ∣ 12 := ⟨_, hmul.symm⟩
    have hle : k ≤ 3 := by
      by_contra hc
      have : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := Nat.le_of_dvd (by norm_num) (this.trans hk12)
      norm_num at this
    interval_cases k
    · norm_num at h2P
    · exfalso
      have hi : (P : Subgroup Y).index = 6 := by omega
      rw [hi] at hcop
      norm_num at hcop
    · rfl
    · exfalso
      omega
  rw [hk2] at hk
  have hPc : IsMulCommutative (P : Subgroup Y) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hk
  have hPX : ∀ x ∈ (P : Subgroup Y),
      (x : D) ∈ centralizer ({t} : Set D) ⊓ centralizer (S : Set D) := by
    intro x hx
    refine mem_inf.2 ⟨?_, x.2⟩
    rw [mem_centralizer_singleton_iff]
    exact congrArg (fun z : (P : Subgroup Y) => ((z : Y) : D))
      (hPc.is_comm.comm ⟨x, hx⟩ ⟨tY, htP⟩)
  set Q := (P : Subgroup Y).map Y.subtype with hQdef
  have hQle : Q ≤ centralizer ({t} : Set D) ⊓ centralizer (S : Set D) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hPX x hx
  have hQcard : Nat.card Q = 4 := by
    rw [hQdef, card_map_of_injective Y.subtype_injective, hk]
    norm_num
  obtain ⟨_, ⟨sY, hsP, rfl⟩, hss⟩ :=
    (hnf.mono hQle).exists_mul_self_ne_one (by rw [hQcard]; norm_num)
  have hss' : (sY : D) * sY ≠ 1 := hss
  have hs4 : sY ^ 4 = 1 := by
    have h1 := Subgroup.orderOf_dvd_natCard (P : Subgroup Y) hsP
    rw [hk] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 (by simpa using h1)
  have hst : (sY : D) * sY = t := by
    have hmem : (sY : D) * sY ∈ centralizer ({t} : Set D) ⊓ centralizer (S : Set D) :=
      mul_mem (hPX sY hsP) (hPX sY hsP)
    have htmem : t ∈ centralizer ({t} : Set D) ⊓ centralizer (S : Set D) :=
      mem_inf.2 ⟨mem_centralizer_singleton_iff.2 rfl, htY⟩
    have hsq : (sY : D) * sY * ((sY : D) * sY) = 1 := by
      have h1 : (sY : D) ^ 4 = 1 := by simpa using congrArg Subtype.val hs4
      rw [← pow_two (sY : D), ← pow_add]
      exact h1
    have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
    rcases hnf _ hmem t htmem hsq htt (mem_centralizer_singleton_iff.1 hmem.1) with h | h | h
    · exact absurd h hss'
    · exact absurd (h ▸ ht) (by simp)
    · exact h
  have hsY4 : orderOf (⟨sY, hsP⟩ : (P : Subgroup Y)) = 4 := by
    rw [Subgroup.orderOf_mk]
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := sY) ?_ ?_
    · simpa using h
    · intro h
      apply hss'
      have h' := congrArg Subtype.val h
      simpa [pow_two] using h'
    · simpa using hs4
  have hcyc : IsCyclic (P : Subgroup Y) :=
    isCyclic_of_orderOf_eq_card (⟨sY, hsP⟩ : (P : Subgroup Y)) (by rw [hsY4, hk]; norm_num)
  obtain ⟨N, hNn, hNc⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two P hcyc
  have hN3 : Nat.card N = 3 := by
    have := hNc.card_mul_card
    rw [h12, hk] at this
    norm_num at this
    omega
  have htsq : tY = sY * sY := Subtype.ext hst.symm
  have hNt : ∀ r ∈ N, r * tY = tY * r := by
    intro r hr
    have h1 := sq_conj_eq_of_card_eq_three hN3 (s := sY) (fun r hr => hNn.conj_mem r hr sY) r hr
    rw [← htsq] at h1
    calc r * tY = tY * r * tY⁻¹ * tY := by rw [h1]
      _ = tY * r := by group
  have hYt : ∀ y : Y, y * tY = tY * y := by
    have htop : (⊤ : Subgroup Y) ≤ centralizer ({tY} : Set Y) := by
      rw [← hNc.sup_eq_top]
      refine sup_le (fun r hr => ?_) (fun x hx => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact hNt r hr
      · rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hPc.is_comm.comm ⟨x, hx⟩ ⟨tY, htP⟩)
    intro y
    exact mem_centralizer_singleton_iff.1 (htop (mem_top y))
  have hYC : Y ≤ centralizer ({t} : Set D) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hYt ⟨y, hy⟩)
  have hcard : Nat.card ↥(Y ⊔ S) = Nat.card Y * Nat.card S :=
    card_sup_of_le_centralizer hZS le_rfl le_rfl
  have hdvd : Nat.card Y * Nat.card S ∣ Nat.card (centralizer ({t} : Set D)) :=
    hcard ▸ Subgroup.card_dvd_of_le (sup_le hYC hSα)
  have h1920 := CFSG.ComponentClassification.FooteLit.KG.card_centralizer_dvd_of_J2 hs t ht
  rw [h12, hScard] at hdvd
  have hS1920 : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 1920 := (Dvd.intro_left _ rfl).trans (hdvd.trans h1920)
  have := lt_of_sl2Order_dvd (by norm_num) (show 1920 < 2 ^ 11 by norm_num) hS1920
  have hn2 : n = 2 := by interval_cases n <;> first | rfl | norm_num at hS1920
  subst hn2
  have := hdvd.trans h1920
  norm_num at this

theorem j3_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .J3 :=
  InnerKernelSelector.of_false fun D _ _ hD hs n hn K _ _ hK α hα hin S hSα hSn hSK _ => by
    obtain ⟨t, ht, rfl, hcomp, -, -, hScard, hZS⟩ := innerRoot_setup hD hn hK hα hin hSα hSn hSK
    obtain ⟨hperf, hC⟩ :=
      CFSG.ComponentClassification.FooteLit.KG.centralizer_perfect_card_of_J3 hs t ht
    have := hperf
    have hSt : S ≤ centralizer ({t} : Set D) := (Sporadic.eqLocus_conj t) ▸ hSα
    have hKcard : Nat.card (S.subgroupOf (centralizer ({t} : Set D))) =
        2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSt).toEquiv, hScard]
    have hZK : center (S.subgroupOf (centralizer ({t} : Set D))) = ⊥ :=
      CFSG.ComponentClassification.FooteLit.KG.center_eq_bot_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hSt) hZS
    have hdvd : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 1920 := by
      rw [← hKcard, ← hC]
      exact Subgroup.card_subgroup_dvd_card _
    have := lt_of_sl2Order_dvd (by norm_num) (show 1920 < 2 ^ 11 by norm_num) hdvd
    have hn2 : n = 2 := by interval_cases n <;> first | rfl | norm_num at hdvd
    subst hn2
    exact CFSG.ComponentClassification.FooteLit.KG.no_component_of_perfect hcomp hZK
      (by rw [hC, hKcard]; norm_num) (j := 5) (by norm_num) (by rw [hC, hKcard]; norm_num)

end CFSG.CGT.PushingUpLit.K1R
