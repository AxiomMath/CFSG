module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SRT
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open scoped Pointwise

variable {S : Type} [Group S] [Finite S] {Q : Subgroup (MulAut S)} {x : S} {J : Subgroup S}
  {q : ℕ}

theorem I1433SCfg.pow_three (c : I1433SCfg Q x J q) : x ^ 3 = 1 := by
  rw [← c.order]
  exact pow_orderOf_eq_one x

theorem I1433SCfg.mem_zpowers_of_commute (c : I1433SCfg Q x J q) {z : S} (hz : z ∈ J)
    (hzc : ∀ l ∈ J, z * l = l * z) (hz3 : z ^ 3 = 1) : z ∈ Subgroup.zpowers x := by
  classical
  have hcent : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) ⟨z, hz⟩ : ↥J ⧸ GLAPPrimeCore 3 ↥J) ∈
      Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
    rw [Subgroup.mem_center_iff]
    intro w
    induction w using QuotientGroup.induction_on with
    | H w =>
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hzc w w.2).symm
  rw [← c.zctr] at hcent
  obtain ⟨w, hw, hweq⟩ := hcent
  have hwx : (w : S) ∈ Subgroup.zpowers x := Subgroup.mem_subgroupOf.1 hw
  have hNmem : w⁻¹ * ⟨z, hz⟩ ∈ GLAPPrimeCore 3 ↥J := QuotientGroup.eq.1 hweq
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hwx
  have hxz : Commute x z := (hzc x c.mem).symm
  have hwz : Commute (w : S) z := by
    rw [← hi]
    exact hxz.zpow_left i
  have hw3 : (w : S) ^ 3 = 1 := by
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, c.pow_three, one_zpow]
  have hu3 : (w⁻¹ * ⟨z, hz⟩ : ↥J) ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    rw [(hwz.inv_left).mul_pow, inv_pow, hw3, hz3, inv_one, one_mul]
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥J)) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥J)
  set u : ↥(GLAPPrimeCore 3 ↥J) := ⟨w⁻¹ * ⟨z, hz⟩, hNmem⟩ with hu
  have hu3' : u ^ 3 = 1 := Subtype.ext (by simpa [hu] using hu3)
  have hord : orderOf u ∣ Nat.gcd 3 (Nat.card (GLAPPrimeCore 3 ↥J)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu3') (orderOf_dvd_natCard u)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hord
  have h1 : (w⁻¹ * ⟨z, hz⟩ : ↥J) = 1 := congrArg Subtype.val hord
  have h2 : (⟨z, hz⟩ : ↥J) = w := (inv_mul_eq_one.1 h1).symm
  have h3 : z = (w : S) := congrArg Subtype.val h2
  rw [h3]
  exact hwx

theorem I1433SCfg.exists_order_three_not_mem_zpowers (c : I1433SCfg Q x J q)
    {yb : ↥J ⧸ GLAPPrimeCore 3 ↥J} (hyb3 : orderOf yb = 3)
    (hybc : yb ∉ Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J)) :
    ∃ y ∈ J, orderOf y = 3 ∧ y ∉ Subgroup.zpowers x := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup ↥J := (Subgroup.zpowers yb).comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) with hH
  have hmap : H.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) = Subgroup.zpowers yb :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J)) _
  have h3H : 3 ∣ Nat.card H := by
    have h := Subgroup.card_map_dvd H (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J))
    rw [hmap, Nat.card_zpowers, hyb3] at h
    exact h
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3 h3H
  set u : ↥J := (y' : ↥J) with hu
  have hu3 : orderOf u = 3 := by rw [hu, Subgroup.orderOf_coe, hy']
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥J)) := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥J)
  have huN : u ∉ (GLAPPrimeCore 3 ↥J) := by
    intro huN
    have h := orderOf_dvd_natCard (⟨u, huN⟩ : ↥(GLAPPrimeCore 3 ↥J))
    rw [Subgroup.orderOf_mk, hu3] at h
    exact Nat.Prime.ne_one Nat.prime_three ((Nat.coprime_self 3).1 (Nat.Coprime.coprime_dvd_right h hcop))
  have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) u ∈ Subgroup.zpowers yb := y'.2
  have hne : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) u ≠ 1 := by
    intro h
    exact huN ((QuotientGroup.eq_one_iff u).1 h)
  have hnc : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) u ∉ Subgroup.center (↥J ⧸ (GLAPPrimeCore 3 ↥J)) := by
    intro hc
    have hord : orderOf (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) u) = 3 := by
      have hd : orderOf (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) u) ∣ 3 := by
        rw [← hu3]
        exact orderOf_map_dvd _ _
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.1 h1) hne
      · exact h3
    have hle : Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) u) ≤ Subgroup.zpowers yb :=
      Subgroup.zpowers_le.2 hmem
    have heq : Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) u) = Subgroup.zpowers yb :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hyb3])
    have hybmem : yb ∈ Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) u) := heq ▸ Subgroup.mem_zpowers yb
    exact hybc ((Subgroup.zpowers_le.2 hc) hybmem)
  refine ⟨(u : S), u.2, by rw [Subgroup.orderOf_coe, hu3], fun hux => hnc ?_⟩
  rw [← c.zctr]
  exact ⟨u, Subgroup.mem_subgroupOf.2 hux, rfl⟩

private theorem inf_eq_bot_of_card_three {G : Type*} [Group G] {A B : Subgroup G}
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) (hne : ¬ B ≤ A) : A ⊓ B = ⊥ := by
  haveI : Fact (Nat.card ↥B).Prime := ⟨by rw [hB]; exact Nat.prime_three⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (A.subgroupOf B) with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    exact disjoint_iff.1 h
  · exact absurd (Subgroup.subgroupOf_eq_top.1 h) hne

theorem I1433SCfg.three_le_pRank_of_inner (c : I1433SCfg Q x J q) (hZ : Subgroup.center S = ⊥)
    (hin : ∀ α ∈ Q, ∃ g : S, α = MulAut.conj g)
    (hy : ∃ yb : ↥J ⧸ GLAPPrimeCore 3 ↥J, orderOf yb = 3 ∧
      yb ∉ Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J)) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha, b, hb, hab⟩ := c.nonabelian
  obtain ⟨g, rfl⟩ := hin a ha
  have hinj := conj_injective_of_center_eq_bot hZ
  have hgx : Commute g x := by
    have h1 := c.commute_conj ha
    rw [← map_mul, ← map_mul] at h1
    exact hinj h1
  have hgJ : ∀ l ∈ J, g * l = l * g := by
    intro l hl
    have h1 := c.centralizes J c.comp (MulAut.conj g) ha l hl
    rw [MulAut.conj_apply] at h1
    calc g * l = (g * l * g⁻¹) * g := by group
      _ = l * g := by rw [h1]
  have hg3 : g ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact c.exponent _ ha
  have hgnx : g ∉ Subgroup.zpowers x := by
    intro hg
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    apply hab
    have hz : MulAut.conj (x ^ i) ∈ (Subgroup.center ↥Q).map Q.subtype := by
      rw [c.center, map_zpow]
      exact Subgroup.zpow_mem_zpowers _ i
    obtain ⟨z, hz, hzx⟩ := hz
    have := (Subgroup.mem_center_iff.1 hz) ⟨b, hb⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    rw [← hzx]
    exact h2.symm
  have hg1 : g ≠ 1 := fun h => hgnx (h ▸ Subgroup.one_mem _)
  have hgo : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  obtain ⟨yb, hyb3, hybc⟩ := hy
  obtain ⟨y, hyJ, hyo, hynx⟩ := c.exists_order_three_not_mem_zpowers hyb3 hybc
  have hy3 : y ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have hxy : Commute x y := by
    have h := c.comp.1 hyJ
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    exact h.symm
  have hgy : Commute g y := hgJ y hyJ
  set X := Subgroup.zpowers x with hX
  set Gg := Subgroup.zpowers g with hGg
  set Y := Subgroup.zpowers y with hY
  have hXc : Nat.card X = 3 := by rw [hX, Nat.card_zpowers, c.order]
  have hGc : Nat.card Gg = 3 := by rw [hGg, Nat.card_zpowers, hgo]
  have hYc : Nat.card Y = 3 := by rw [hY, Nat.card_zpowers, hyo]
  have hcommXG : ∀ u ∈ X, ∀ v ∈ Gg, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact ((hgx.symm).zpow_zpow i j).eq
  have hXG : X ⊓ Gg = ⊥ := inf_eq_bot_of_card_three hXc hGc fun h => hgnx (h (Subgroup.mem_zpowers g))
  obtain ⟨hA1, hA2⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X Gg hcommXG
  rw [hXG, Subgroup.card_bot, mul_one, hXc, hGc] at hA1
  set A := X ⊔ Gg with hA
  have hAy : ∀ u ∈ A, ∀ v ∈ Y, u * v = v * u := by
    intro u hu v hv
    have hu' : u ∈ (X : Set S) * (Gg : Set S) := hA2 ▸ hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hu'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu₁
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu₂
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (((hxy.zpow_zpow i k).mul_left (hgy.zpow_zpow j k))).eq
  have hyA : y ∉ A := by
    intro hyA
    have hy' : y ∈ (X : Set S) * (Gg : Set S) := hA2 ▸ hyA
    obtain ⟨u₁, hu₁, u₂, hu₂, hyu⟩ := hy'
    simp only at hyu
    have hu₂J : u₂ ∈ J := by
      have : u₂ = u₁⁻¹ * y := by rw [← hyu]; group
      rw [this]
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu₁
      exact J.mul_mem (J.inv_mem (J.zpow_mem c.mem i)) hyJ
    by_cases hu₂1 : u₂ = 1
    · apply hynx
      rw [← hyu, hu₂1, mul_one]
      exact hu₁
    ·
      have hu₂o : orderOf u₂ = 3 := by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu₂
        refine orderOf_eq_prime ?_ hu₂1
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg3, one_zpow]
      have hle : Subgroup.zpowers u₂ ≤ Gg := Subgroup.zpowers_le.2 hu₂
      have heq : Subgroup.zpowers u₂ = Gg :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hgo, hu₂o])
      have hgJ' : g ∈ J := by
        have : g ∈ Subgroup.zpowers u₂ := heq ▸ Subgroup.mem_zpowers g
        exact (Subgroup.zpowers_le.2 hu₂J) this
      exact hgnx (c.mem_zpowers_of_commute hgJ' hgJ hg3)
  have hAY : A ⊓ Y = ⊥ := by
    haveI : Fact (Nat.card ↥Y).Prime := ⟨by rw [hYc]; exact Nat.prime_three⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (A.subgroupOf Y) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact disjoint_iff.1 h
    · exact absurd ((Subgroup.subgroupOf_eq_top.1 h) (Subgroup.mem_zpowers y)) hyA
  obtain ⟨hE1, hE2⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A Y hAy
  rw [hAY, Subgroup.card_bot, mul_one, hA1, hYc] at hE1
  set E := A ⊔ Y with hE
  have hEdecomp : ∀ e ∈ E, ∃ i j k : ℤ, e = x ^ i * g ^ j * y ^ k := by
    intro e he
    have he' : e ∈ (A : Set S) * (Y : Set S) := hE2 ▸ he
    obtain ⟨u, hu, v, hv, rfl⟩ := he'
    have hu' : u ∈ (X : Set S) * (Gg : Set S) := hA2 ▸ hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hu'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu₁
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu₂
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact ⟨i, j, k, rfl⟩
  have hcomm : ∀ i j k i' j' k' : ℤ,
      Commute (x ^ i * g ^ j * y ^ k) (x ^ i' * g ^ j' * y ^ k') := by
    intro i j k i' j' k'
    have h1 : ∀ (a b : ℤ), Commute (x ^ a) (g ^ b) := fun a b => (hgx.symm).zpow_zpow a b
    have h2 : ∀ (a b : ℤ), Commute (x ^ a) (y ^ b) := fun a b => hxy.zpow_zpow a b
    have h3 : ∀ (a b : ℤ), Commute (g ^ a) (y ^ b) := fun a b => hgy.zpow_zpow a b
    refine Commute.mul_left (Commute.mul_left ?_ ?_) ?_
    · exact Commute.mul_right (Commute.mul_right ((Commute.refl x).zpow_zpow i i') (h1 i j'))
        (h2 i k')
    · exact Commute.mul_right (Commute.mul_right (h1 i' j).symm ((Commute.refl g).zpow_zpow j j'))
        (h3 j k')
    · exact Commute.mul_right (Commute.mul_right (h2 i' k).symm (h3 j' k).symm)
        ((Commute.refl y).zpow_zpow k k')
  have hElem : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun e₁ e₂ => ?_⟩⟩, fun e he => ?_⟩
    · obtain ⟨i, j, k, he₁⟩ := hEdecomp e₁ e₁.2
      obtain ⟨i', j', k', he₂⟩ := hEdecomp e₂ e₂.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [he₁, he₂]
      exact (hcomm i j k i' j' k').eq
    · obtain ⟨i, j, k, rfl⟩ := hEdecomp e he
      have hxg : Commute (x ^ i) (g ^ j) := (hgx.symm).zpow_zpow i j
      have hxgy : Commute (x ^ i * g ^ j) (y ^ k) :=
        (hxy.zpow_zpow i k).mul_left (hgy.zpow_zpow j k)
      rw [hxgy.mul_pow, hxg.mul_pow]
      have hx3' : (x ^ i) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, c.pow_three, one_zpow]
      have hg3' : (g ^ j) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg3, one_zpow]
      have hy3' : (y ^ k) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
      rw [hx3', hg3', hy3', one_mul, one_mul]
  exact le_pRank 3 (by norm_num) le_top hElem (k := 3) (by rw [hE1]; norm_num)

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
