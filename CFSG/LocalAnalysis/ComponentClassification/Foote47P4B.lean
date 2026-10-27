module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47P4Aut

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

namespace P4Data

variable {M T S P : Subgroup G} {t z w : G}

theorem exists_normalizer_of_inner (h : FooteSec4 G L) (d : P4Data L M T S P t z w) {g : G}
    (hg : Valid P t z w g) (hin : g * t * g⁻¹ ∈ innerAct (footeF L t)) :
    ∃ g' q : G, g' ∈ normalizer (P : Set G) ∧ (q = t ∨ q = t * z) ∧ g' * t * g'⁻¹ = q * w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hd⟩ := d.c.hd
  have hto : orderOf (g * t * g⁻¹) = 2 := by
    rw [show g * t * g⁻¹ = MulAut.conj g t from rfl, MulEquiv.orderOf_eq, d.c.hv.ht]
  have htt' : IsConj t (g * t * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  obtain ⟨hne1, hne2⟩ := Valid.tstar_ne h d hg
  rcases d.inv_cases h hg.ht hin hto with h1 | ⟨q, r, hq, hr, hro, hqr, y, hyF, hyC, hy⟩
  · exfalso
    rcases h1 with h1 | h1 | h1
    · exact (d.not_isConj_t).1 (h1 ▸ htt')
    · exact hne1 h1
    · exact hne2 h1
  have htq : IsConj t (q * w) := htt'.trans (isConj_iff.mpr ⟨y⁻¹, by rw [hy]; group⟩)
  have hq' : q = t ∨ q = t * z := by
    rcases hq with rfl | rfl | rfl | rfl
    · exact absurd (by simpa using htq) (d.not_isConj_t).2.1
    · exact absurd htq (d.not_isConj_t).2.2
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hqP : q ∈ P := by
    rcases hq' with rfl | rfl
    · exact d.t_mem_P
    · exact mul_mem d.t_mem_P d.z_mem_P
  set g₁ := y⁻¹ * g with hg₁
  have hg₁t : g₁ * t * g₁⁻¹ = q * w := by
    rw [hg₁, show y⁻¹ * g * t * (y⁻¹ * g)⁻¹ = y⁻¹ * (g * t * g⁻¹) * y by group, hy]
    group
  have hqwc : ∀ p ∈ P, p * (q * w) = (q * w) * p := by
    intro p hp
    have h1 : p * q = q * p := by
      rcases hq' with rfl | rfl
      · exact d.t_comm hp
      · rw [← mul_assoc, d.t_comm hp, mul_assoc, d.z_comm (d.P_le_S hp), mul_assoc]
    rw [← mul_assoc, h1, mul_assoc, d.hwc p (d.P_le_S hp), mul_assoc]
  have hP' : IsSylowOf 2 (conjugate P g₁) (centralizer ({t} : Set G)) := by
    refine isSylowOf_of_card (fun x hx => ?_) ?_
    · have hx' := mem_conjugate_iff.mp hx
      rw [mem_centralizer_singleton_iff]
      have h1 := hqwc _ hx'
      rw [← hg₁t] at h1
      calc x * t = g₁⁻¹ * ((g₁ * x * g₁⁻¹) * (g₁ * t * g₁⁻¹)) * g₁ := by group
        _ = g₁⁻¹ * ((g₁ * t * g₁⁻¹) * (g₁ * x * g₁⁻¹)) * g₁ := by rw [h1]
        _ = t * x := by group
    · rw [card_conjugate_eq_card, d.c.hPsyl.card_eq]
  obtain ⟨k, hk, hkP⟩ := d.c.hPsyl.exists_mem_conj hP'
  have hkt : k * t * k⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp hk, mul_inv_cancel_right]
  refine ⟨g₁ * k, q, ?_, hq', ?_⟩
  · rw [mem_normalizer_iff]
    intro x
    have h1 := hkP (k * x * k⁻¹)
    rw [mem_conjugate_iff, show k⁻¹ * (k * x * k⁻¹) * k = x by group] at h1
    rw [show g₁ * k * x * (g₁ * k)⁻¹ = g₁ * (k * x * k⁻¹) * g₁⁻¹ by group]
    exact h1.symm
  · rw [show g₁ * k * t * (g₁ * k)⁻¹ = g₁ * (k * t * k⁻¹) * g₁⁻¹ by group, hkt, hg₁t]

theorem commutator_le_innerAct (h : FooteSec4 G L) (hOut : FooteL2OutAbelian)
    (d : P4Data L M T S P t z w) : ⁅P, P⁆ ≤ innerAct (footeF L t) := by
  obtain ⟨-, ⟨ε⟩⟩ := d.quotient_t h
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact commutator_mem_innerAct hOut h.footeFamilyType ε (d.P_le_normalizer h ha)
    (d.P_le_normalizer h hb)

theorem false_of_normalizer (h : FooteSec4 G L) (hOut : FooteL2OutAbelian)
    (hOF : Foote47OuterOrderFour) (d : P4Data L M T S P t z w) {g q : G}
    (hgP : g ∈ normalizer (P : Set G)) (hq : q = t ∨ q = t * z) (hgt : g * t * g⁻¹ = q * w) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hd⟩ := d.c.hd
  have dz := zData_of h d.c.hv.hM d.c.hTsyl hd.hz hd.hzT hd.hzc
  have htt : t * t = 1 := by rw [← sq, ← d.c.hv.ht]; exact pow_orderOf_eq_one t
  have hzQ : z ∈ T ⊓ centralizer ({t} : Set G) :=
    mem_inf.mpr ⟨hd.hzT, mem_centralizer_singleton_iff.mpr (hd.hzc t d.c.htT).symm⟩
  have htQ : t ∈ T ⊓ centralizer ({t} : Set G) :=
    mem_inf.mpr ⟨d.c.htT, mem_centralizer_singleton_iff.mpr rfl⟩
  have hqQ : q ∈ T ⊓ centralizer ({t} : Set G) := by
    rcases hq with rfl | rfl
    · exact htQ
    · exact mul_mem htQ hzQ
  have hw1 : w ≠ 1 := fun h1 => by have := d.hw; rw [h1, orderOf_one] at this; omega
  have htw : IsConj t (t * w) := by
    rcases hq with rfl | rfl
    · exact isConj_iff.mpr ⟨g, hgt⟩
    · exact (isConj_iff.mpr ⟨g, hgt⟩).trans d.isConj_tw_tzw.symm
  have htzw : IsConj t (t * z * w) := htw.trans d.isConj_tw_tzw
  have hgz : g ∉ centralizer ({z} : Set G) := by
    intro hgz
    have h1 : g * t * g⁻¹ ∈ coreActionKernel (footeF L z) :=
      FooteLit.conj_mem_coreActionKernel (dz.centralizer_le_normalizer h hgz) (dz.hTKle d.c.htT)
    have h2 : q * w ∈ T ⊓ centralizer ({t} : Set G) := by
      rw [← d.P_inf_coreActionKernel, ← hgt]
      exact mem_inf.mpr ⟨hgt ▸ mul_mem (d.Q_le_P hqQ) d.w_mem_P, h1⟩
    have h3 : w ∈ T ⊓ centralizer ({t} : Set G) := by
      have h4 : w = q⁻¹ * (q * w) := by group
      rw [h4]
      exact mul_mem (inv_mem hqQ) h2
    exact hw1 (d.eq_one_of_mem_Q_Ft h h3 d.hwF)
  have hzP : g * z * g⁻¹ ∈ P := (mem_normalizer_iff.mp hgP z).mp d.z_mem_P
  have hzo : orderOf (g * z * g⁻¹) = 2 := by
    rw [show g * z * g⁻¹ = MulAut.conj g z from rfl, MulEquiv.orderOf_eq, hd.hz]
  have hzz : IsConj z (g * z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have hzI : g * z * g⁻¹ ∉ innerAct (footeF L t) := by
    intro hzI
    rcases d.inv_cases h hzP hzI hzo with h1 | ⟨q', r', hq', -, -, -, y, -, -, hy⟩
    · rcases h1 with h1 | h1 | h1
      · apply hgz
        rw [mem_centralizer_singleton_iff]
        calc g * z = g * z * g⁻¹ * g := by group
          _ = z * g := by rw [h1]
      · exact (d.not_isConj_t).1 (h1 ▸ hzz).symm
      · exact (d.not_isConj_t).1 (d.isConj_t_tz.trans (h1 ▸ hzz).symm)
    · have hzq : IsConj z (q' * w) := hzz.trans (isConj_iff.mpr ⟨y⁻¹, by rw [hy]; group⟩)
      rcases hq' with rfl | rfl | rfl | rfl
      · exact d.hzw (by simpa using hzq)
      · exact d.hzzw hzq
      · exact (d.not_isConj_t).1 (htw.trans hzq.symm)
      · exact (d.not_isConj_t).1 (htzw.trans hzq.symm)
  obtain ⟨x₀, hx₀, hx₀z⟩ := hd.hroot
  have hx₀Q := hd.hQ₀ hx₀
  have hx₀P := d.Q_le_P hx₀Q
  have hz1 : z ≠ 1 := fun h1 => by have := hd.hz; rw [h1, orderOf_one] at this; omega
  have hx₀4 : orderOf x₀ = 4 := by
    have h1 : orderOf x₀ = 2 ^ 2 := orderOf_eq_prime_pow (p := 2) (n := 1)
      (by rw [pow_one, hx₀z]; exact hz1)
      (by rw [pow_succ, pow_one, pow_mul, hx₀z, ← hd.hz, pow_orderOf_eq_one])
    rw [h1]
    norm_num
  set x := g * x₀ * g⁻¹ with hx
  have hxP : x ∈ P := (mem_normalizer_iff.mp hgP x₀).mp hx₀P
  have hx4 : orderOf x = 4 := by
    rw [hx, show g * x₀ * g⁻¹ = MulAut.conj g x₀ from rfl, MulEquiv.orderOf_eq, hx₀4]
  have hx2 : x ^ 2 = g * z * g⁻¹ := by rw [hx, conj_pow, hx₀z]
  obtain ⟨r, hr, hxr⟩ := d.exists_commutator_ne_one h hOF hxP hx4 (hx2 ▸ hzI)
  have hP' := d.commutator_le_innerAct h hOut
  have hgP' : ∀ u ∈ ⁅P, P⁆, g * u * g⁻¹ ∈ ⁅P, P⁆ := by
    intro u hu
    have h1 : (⁅P, P⁆).map (MulAut.conj g).toMonoidHom = ⁅P, P⁆ := by
      rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hgP]
    rw [← h1]
    exact ⟨u, hu, rfl⟩
  have hQ₀P' : ∀ u ∈ Q₀, u ∈ ⁅P, P⁆ → u = 1 := by
    intro u hu hu'
    by_contra hu1
    have hup : IsPGroup 2 (zpowers u) :=
      (d.c.hPsyl.isPGroup.to_le (hd.hQ₀.trans d.Q_le_P)).to_le (zpowers_le.mpr hu)
    obtain ⟨n, hn⟩ := hup.exists_card_eq
    have hn1 : 1 ≤ n := by
      by_contra hn0
      have h2 : Nat.card (zpowers u) = 1 := by rw [hn]; simp [show n = 0 by omega]
      rw [Nat.card_zpowers, orderOf_eq_one_iff] at h2
      exact hu1 h2
    obtain ⟨⟨v, hvu⟩, hv⟩ := exists_prime_orderOf_dvd_card' (G := zpowers u) 2
      (hn ▸ dvd_pow_self 2 (by omega))
    have hvo : orderOf v = 2 := by rw [← hv, Subgroup.orderOf_mk]
    have hvz : v = z := hd.huniq v (zpowers_le.mpr hu hvu) hvo
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hvu
    apply hzI
    rw [← hvz, ← conj_zpow]
    exact zpow_mem (hP' (hgP' u hu')) m
  have hrP : r ∈ P := (mem_inf.mp hr).1
  set p := g⁻¹ * r * g with hp
  have hpP : p ∈ P := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hgP) r).mp hrP
    rwa [inv_inv] at h1
  set y := x₀ * p * x₀⁻¹ * p⁻¹ with hy
  have hyg : g * y * g⁻¹ = x * r * x⁻¹ * r⁻¹ := by
    rw [hy, hp, hx]
    group
  have hy1 : y ≠ 1 := by
    intro h1
    apply hxr
    have h2 : x * r * x⁻¹ * r⁻¹ = 1 := by rw [← hyg, h1]; group
    calc x * r * x⁻¹ = x * r * x⁻¹ * r⁻¹ * r := by group
      _ = r := by rw [h2, one_mul]
  have hyP' : y ∈ ⁅P, P⁆ := by
    rw [hy, ← commutatorElement_def]
    exact commutator_mem_commutator hx₀P hpP
  have hyQ : y ∈ T ⊓ centralizer ({t} : Set G) := by
    rw [← d.c.hQP]
    have hpN : p ∈ normalizer ((P ⊓ coreActionKernel (footeF L t) : Subgroup G) : Set G) :=
      mem_normalizer_inf' (le_normalizer hpP)
        (mem_normalizer_coreActionKernel (d.P_le_normalizer h hpP))
    have h1 : p * x₀⁻¹ * p⁻¹ ∈ P ⊓ coreActionKernel (footeF L t) :=
      (mem_normalizer_iff.mp hpN _).mp (by rw [d.c.hQP]; exact inv_mem hx₀Q)
    rw [hy, show x₀ * p * x₀⁻¹ * p⁻¹ = x₀ * (p * x₀⁻¹ * p⁻¹) by group]
    exact mul_mem (by rw [d.c.hQP]; exact hx₀Q) h1
  have hy2 : y ^ 2 = 1 := hQ₀P' _ (hd.sq_mem htt hyQ) (pow_mem hyP' 2)
  have hyQ₀ : y ∉ Q₀ := fun h1 => hy1 (hQ₀P' y h1 hyP')
  have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  have hty : IsConj t y := by
    rcases hd.inv_cases htt hyQ hyo with h1 | h1 | h1
    · exact absurd (h1 ▸ hd.hzQ₀) hyQ₀
    · rw [h1]
    · rw [h1]; exact d.isConj_t_tz
  have hcR : x * r * x⁻¹ * r⁻¹ ∈ P ⊓ footeF L t := by
    have hxN := d.P_le_normalizer h hxP
    refine mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem hxP hrP) (inv_mem hxP)) (inv_mem hrP),
      mul_mem ((mem_normalizer_iff.mp hxN r).mp (mem_inf.mp hr).2) (inv_mem (mem_inf.mp hr).2)⟩
  have hco : orderOf (x * r * x⁻¹ * r⁻¹) = 2 := by
    rw [← hyg, show g * y * g⁻¹ = MulAut.conj g y from rfl, MulEquiv.orderOf_eq, hyo]
  obtain ⟨y', -, -, hy'⟩ := d.exists_conj_w h hcR hco
  have htw' : IsConj t w := by
    refine hty.trans ((isConj_iff.mpr ⟨g, hyg⟩).trans ?_)
    exact (isConj_iff.mpr ⟨y', hy'.symm⟩).symm
  exact (d.not_isConj_t).2.1 htw'

end P4Data

end CFSG.ComponentClassification.Foote47
