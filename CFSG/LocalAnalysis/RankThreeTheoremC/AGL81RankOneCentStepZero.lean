module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneElevenEleven
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_central {K : Type} [Group K] [Finite K] [IsSimpleGroup K] {p : ℕ}
    (hp : p.Prime) {g : K} (hg1 : g ^ p ≠ 1) (hg2 : g ^ (p ^ 2) = 1) {k : K}
    (hk : ∀ k' : K, k * k' = k' * k) : k = 1 := by
  by_contra hk1
  have hcen : Subgroup.center K = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exfalso
      apply hk1
      have : k ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun g => (hk g).symm
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    · exact h
  letI : CommGroup K :=
    { (inferInstance : Group K) with
      mul_comm := fun a b => by
        have := Subgroup.mem_center_iff.mp (hcen ▸ Subgroup.mem_top a) b
        exact this.symm }
  have hprime := IsSimpleGroup.prime_card (α := K)
  have hgne : g ≠ 1 := fun h => hg1 (by rw [h, one_pow])
  have hord : orderOf g = Nat.card K := by
    have hdvd := orderOf_dvd_natCard g
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime _ hdvd) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hgne
    · exact h
  have hq : Nat.card K ∣ p ^ 2 := hord ▸ orderOf_dvd_of_pow_eq_one hg2
  have hqp : Nat.card K = p := (Nat.prime_dvd_prime_iff_eq hprime hp).mp
    (hprime.dvd_of_dvd_pow hq)
  exact hg1 (hqp ▸ hord ▸ pow_orderOf_eq_one g)

theorem eq_one_of_mem_core {p : ℕ} [Fact p.Prime] {H : Subgroup G} {x : H}
    (hx : x ∈ primeComplementCore (G := H) p) {n : ℕ} (hxp : x ^ (p ^ n) = 1) : x = 1 := by
  have hdvd : orderOf x ∣ Nat.card (primeComplementCore (G := H) p) := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : primeComplementCore (G := H) p)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one hxp)
  have hcop := (primeComplementCore_coprime (G := H) p).coprime_dvd_right hdvd
  rw [hk] at hcop
  rcases k with _ | k
  · exact orderOf_eq_one_iff.mp (by simpa using hk)
  · exact absurd (Nat.Coprime.coprime_dvd_right (dvd_pow_self p k.succ_ne_zero) hcop)
      (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime) |>.not.mpr (by simp))

theorem eq_one_of_mem_hyp111Pre_of_mem_d1PlusCore {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} [IsSimpleGroup ↥K] {g : K}
    (hg1 : g ^ p ≠ 1) (hg2 : g ^ (p ^ 2) = 1) {x : G} (hxK : x ∈ hyp111Pre p H K)
    (hxX : x ∈ d1PlusCore p H K) {n : ℕ} (hxp : x ^ (p ^ n) = 1) : x = 1 := by
  obtain ⟨x', hx'K, rfl⟩ := hxK
  obtain ⟨x'', hx''C, hx''⟩ := hxX
  have hx : x'' = x' := Subtype.ext hx''
  subst hx
  set k : K := ⟨QuotientGroup.mk' (primeComplementCore (G := H) p) x'', hx'K⟩
  have hk : ∀ k' : K, k * k' = k' * k := by
    intro k'
    have := Subgroup.mem_centralizer_iff.mp hx''C k'.1 k'.2
    exact Subtype.ext this.symm
  have hk1 := eq_one_of_central (Fact.out : p.Prime) hg1 hg2 hk
  have hcore : x'' ∈ primeComplementCore (G := H) p := by
    have : QuotientGroup.mk' (primeComplementCore (G := H) p) x'' = 1 :=
      congrArg Subtype.val hk1
    exact (QuotientGroup.eq_one_iff x'').mp this
  have hxp' : x'' ^ (p ^ n) = 1 := Subtype.ext (by simpa using hxp)
  rw [eq_one_of_mem_core hcore hxp']
  rfl

theorem elemAbelian_triple {p : ℕ} [Fact p.Prime] {H W : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} [IsSimpleGroup ↥K] (hKn : K.Normal)
    (hWH : W ≤ H) {y a z : G} (hzW : z ∈ W) (hzX : z ∈ d1PlusCore p H K) (hzo : orderOf z = p)
    (hzc : ∀ w ∈ W, w * z = z * w) (hyl : d1LiftX p H W K = Subgroup.zpowers y)
    (hyo : orderOf y = p ^ 2) (haW : a ∈ W) (hao : orderOf a = p)
    (haout : a ∉ hyp111Pre p H K ⊔ d1PlusCore p H K) {b : G}
    (hb : b ∈ Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers a) (hbZ : b ∉ Subgroup.zpowers (y ^ p)) :
    orderOf b = p ∧
      Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers b =
        Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers a ∧
      IsElemAbelian p (Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers z) ∧
      Nat.card ↥(Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers z) = p ^ 3 ∧
      Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers z ≤ W := by
  have hp : p.Prime := Fact.out
  have hyW : y ∈ W := d1LiftX_le p H W K (hyl ▸ Subgroup.mem_zpowers y)
  have hyK : y ∈ hyp111Pre p H K :=
    RankOne.d1LiftX_le_hyp111Pre p H W K (hyl ▸ Subgroup.mem_zpowers y)
  obtain ⟨y', hy'K, hy'0⟩ := hyK
  have hy' : (y' : G) = y := hy'0
  set g : K := ⟨QuotientGroup.mk' (primeComplementCore (G := H) p) y', hy'K⟩ with hgdef
  have hy'2 : y' ^ (p ^ 2) = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hy', ← hyo, pow_orderOf_eq_one]; rfl)
  have hg2 : g ^ (p ^ 2) = 1 := Subtype.ext (by
    show QuotientGroup.mk' _ y' ^ (p ^ 2) = 1
    rw [← map_pow, hy'2, map_one])
  have hg1 : g ^ p ≠ 1 := by
    intro h
    have h' : QuotientGroup.mk' (primeComplementCore (G := H) p) (y' ^ p) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val h
    have hc := (QuotientGroup.eq_one_iff (y' ^ p)).mp h'
    have hpp : (y' ^ p) ^ (p ^ 1) = 1 := by rw [← pow_mul, pow_one, ← sq, hy'2]
    have hy1 := eq_one_of_mem_core hc hpp
    have : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one (by
      rw [← hy', ← Subgroup.coe_pow, hy1]
      rfl)
    rw [hyo] at this
    exact absurd (Nat.le_of_dvd hp.pos this) (by nlinarith [hp.two_le])
  have hconj : a * y * a⁻¹ ∈ Subgroup.zpowers y := by
    rw [← hyl]
    exact RankOne.conj_mem_d1LiftX hKn haW (hWH haW) (hyl ▸ Subgroup.mem_zpowers y)
  have hap1 : a ^ p = 1 := hao ▸ pow_orderOf_eq_one a
  obtain ⟨-, hyp⟩ := RankOne.conj_pow_facts hyo hap1 hconj
  have hyp_ord : orderOf (y ^ p) = p := by
    rw [orderOf_pow_of_dvd hp.ne_zero (by rw [hyo]; exact dvd_pow_self p two_ne_zero),
      hyo, sq, Nat.mul_div_cancel _ hp.pos]
  have hyp_le : Subgroup.zpowers (y ^ p) ≤ Subgroup.zpowers y :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) p)
  have hypre : Subgroup.zpowers (y ^ p) ≤ hyp111Pre p H K := hyp_le.trans
    (hyl ▸ RankOne.d1LiftX_le_hyp111Pre p H W K)
  have ha_notin : a ∉ Subgroup.zpowers (y ^ p) := fun h => haout (Subgroup.mem_sup_left (hypre h))
  have hcomm : y ^ p * a = a * y ^ p := by
    calc y ^ p * a = a * y ^ p * a⁻¹ * a := by rw [hyp]
      _ = a * y ^ p := by group
  set E := Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers a with hEdef
  obtain ⟨hE, hEc⟩ := RankOne.elemAbelian_pair hp hyp_ord hao ha_notin hcomm
  have hb1 : b ≠ 1 := fun h => hbZ (h ▸ Subgroup.one_mem _)
  have hbo : orderOf b = p := orderOf_eq_prime (hE.2 b hb) hb1
  have hypE : y ^ p ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hcb : y ^ p * b = b * y ^ p := by
    have := hE.1.is_comm.comm ⟨y ^ p, hypE⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  obtain ⟨-, hEbc⟩ := RankOne.elemAbelian_pair hp hyp_ord hbo hbZ hcb
  have hEb : Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers b = E :=
    Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left (Subgroup.zpowers_le.mpr hb))
      (by rw [hEc, hEbc])
  have hEW : E ≤ W := sup_le
    (Subgroup.zpowers_le.mpr (W.pow_mem hyW p)) (Subgroup.zpowers_le.mpr haW)
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzo
    exact hp.one_lt.ne hzo
  have hzE : z ∉ E := by
    intro hzE
    by_cases hzy : z ∈ Subgroup.zpowers (y ^ p)
    · exact hz1 (eq_one_of_mem_hyp111Pre_of_mem_d1PlusCore hg1 hg2 (hypre hzy) hzX
        (n := 1) (by rw [pow_one, ← hzo, pow_orderOf_eq_one]))
    · have hcz : y ^ p * z = z * y ^ p := hzc _ (hEW hypE)
      obtain ⟨-, hc2⟩ := RankOne.elemAbelian_pair hp hyp_ord hzo hzy hcz
      have heq : Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers z = E :=
        Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left (Subgroup.zpowers_le.mpr hzE))
          (by rw [hEc, hc2])
      have haE : a ∈ Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers z :=
        heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
      exact haout ((sup_le_sup hypre (Subgroup.zpowers_le.mpr hzX)) haE)
  have hzp : z ^ p = 1 := hzo ▸ pow_orderOf_eq_one z
  obtain ⟨hE', hE'c⟩ := OtherCfg.isElemAbelian_sup_zpowers_gen hp hE hzp hzE
    (fun e he => hzc e (hEW he))
  rw [hEb]
  refine ⟨hbo, rfl, hE', ?_, sup_le hEW (Subgroup.zpowers_le.mpr hzW)⟩
  rw [hE'c, hEc]
  ring

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
