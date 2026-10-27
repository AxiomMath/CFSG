module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx65
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.GH74.GLS.Stage2.Final.ModelGroupTheory
public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Abstract

variable {X : Type*} [Group X]

theorem odd_orderOf_of_mem_odd {N : Subgroup X} (hN : Odd (Nat.card N)) {n : X} (hn : n ∈ N) :
    Odd (orderOf n) :=
  Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N hn)

theorem eq_one_of_mul_self_of_mem_odd {N : Subgroup X} (hN : Odd (Nat.card N)) {n : X} (hn : n ∈ N)
    (hsq : n * n = 1) : n = 1 := by
  have h1 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have h2 := odd_orderOf_of_mem_odd hN hn
  have h3 : orderOf n = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd h2 (by decide)
  exact orderOf_eq_one_iff.1 h3

theorem exists_odd_conj {a b : X} (ha : a * a = 1) (hb : b * b = 1) (ho : Odd (orderOf (a * b))) :
    ∃ g ∈ zpowers (a * b), g * a * g⁻¹ = b := by
  obtain ⟨m, hm⟩ := ho
  set o : X := a * b with ho'
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hoinv : o⁻¹ = b * a := by
    rw [ho', mul_inv_rev, ha', hb']
  have hao : a * o * a⁻¹ = o⁻¹ := by
    rw [hoinv, ha', ho']
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha, one_mul]
  have ho2 : o ^ (2 * (m + 1)) = o := by
    have h1 : o ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one o
    calc o ^ (2 * (m + 1)) = o ^ (2 * m + 1 + 1) := by
          rw [show 2 * (m + 1) = 2 * m + 1 + 1 from by ring]
      _ = o ^ (2 * m + 1) * o := pow_succ _ _
      _ = o := by rw [h1, one_mul]
  refine ⟨(o ^ (m + 1))⁻¹, ?_, ?_⟩
  · exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers o) _)
  · have hpow : a * o ^ (m + 1) * a⁻¹ = (o⁻¹) ^ (m + 1) := by
      rw [← hao, conj_pow]
    have hcomm : a * o ^ (m + 1) = (o⁻¹) ^ (m + 1) * a := by
      calc a * o ^ (m + 1) = (a * o ^ (m + 1) * a⁻¹) * a := by group
        _ = (o⁻¹) ^ (m + 1) * a := by rw [hpow]
    calc (o ^ (m + 1))⁻¹ * a * ((o ^ (m + 1))⁻¹)⁻¹ = (o ^ (m + 1))⁻¹ * (a * o ^ (m + 1)) := by group
      _ = (o ^ (m + 1))⁻¹ * ((o⁻¹) ^ (m + 1) * a) := by rw [hcomm]
      _ = (o ^ (m + 1))⁻¹ * ((o ^ (m + 1))⁻¹ * a) := by rw [inv_pow]
      _ = (o ^ (m + 1) * o ^ (m + 1))⁻¹ * a := by group
      _ = (o ^ (2 * (m + 1)))⁻¹ * a := by rw [← pow_add, two_mul]
      _ = o⁻¹ * a := by rw [ho2]
      _ = b := by
        rw [hoinv]
        calc b * a * a = b * (a * a) := by group
          _ = b := by rw [ha, mul_one]

section Lift

variable [Finite X] {N : Subgroup X} [N.Normal]

theorem exists_invol_lift (hN : Odd (Nat.card N)) {Y : Subgroup X} {u : X} (hu : orderOf u = 2)
    (huY : QuotientGroup.mk' N u ∈ Y.map (QuotientGroup.mk' N)) :
    ∃ u₀ ∈ Y, orderOf u₀ = 2 ∧ u₀ * u ∈ N := by
  obtain ⟨k, hkY, hk⟩ := huY
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu, pow_two] at this
  have hkk : k * k ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    have h1 : (QuotientGroup.mk k : X ⧸ N) = QuotientGroup.mk u := hk
    rw [h1, ← QuotientGroup.mk_mul, hu2]
    rfl
  have hodd : Odd (orderOf (k * k)) := odd_orderOf_of_mem_odd hN hkk
  have hbar : orderOf (QuotientGroup.mk' N u) = 2 := by
    have hd : orderOf (QuotientGroup.mk' N u) ∣ 2 := hu ▸ orderOf_map_dvd (QuotientGroup.mk' N) u
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exfalso
      have h1 : QuotientGroup.mk' N u = 1 := orderOf_eq_one_iff.1 h
      have h2 : u ∈ N := (QuotientGroup.eq_one_iff u).1 h1
      have := odd_orderOf_of_mem_odd hN h2
      rw [hu] at this
      exact absurd this (by decide)
    · exact h
  have h2k : 2 ∣ orderOf k := by
    have := orderOf_map_dvd (QuotientGroup.mk' N) k
    rw [hk, hbar] at this
    exact this
  obtain ⟨m, hm⟩ := h2k
  have hkpos : 0 < orderOf k := orderOf_pos k
  have hm0 : 0 < m := by omega
  have hkk' : orderOf (k * k) = m := by
    rw [← pow_two, orderOf_pow_of_dvd (by norm_num) ⟨m, hm⟩, hm]
    omega
  have hmodd : Odd m := hkk' ▸ hodd
  have hmd : m ∣ orderOf k := ⟨2, by omega⟩
  refine ⟨k ^ m, Subgroup.pow_mem _ hkY _, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd hm0.ne' hmd, hm]
    exact Nat.mul_div_cancel 2 hm0
  · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
    have h1 : (QuotientGroup.mk k : X ⧸ N) = QuotientGroup.mk u := hk
    have h3 : (QuotientGroup.mk u : X ⧸ N) * QuotientGroup.mk u = 1 := by
      rw [← QuotientGroup.mk_mul, hu2]
      rfl
    obtain ⟨c, hc⟩ := hmodd
    rw [h1, hc, pow_succ, pow_mul, sq, h3, one_pow, one_mul, h3]

omit [Finite X] in
theorem exists_conj_of_bar (hN : Odd (Nat.card N)) {L : Subgroup X} {a b k : X} (ha : a ∈ L) (hb : b ∈ L)
    (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hk : QuotientGroup.mk' N k ∈ L.map (QuotientGroup.mk' N)) (hkab : k * a * k⁻¹ * b ∈ N) :
    ∃ g ∈ L, g * a * g⁻¹ = b := by
  obtain ⟨l, hlL, hl⟩ := hk
  have hal : l * a * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hlL ha) (L.inv_mem hlL)
  have ha'2 : (l * a * l⁻¹) * (l * a * l⁻¹) = 1 := by
    calc (l * a * l⁻¹) * (l * a * l⁻¹) = l * (a * a) * l⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hab : (l * a * l⁻¹) * b ∈ N := by
    have h1 : (QuotientGroup.mk l : X ⧸ N) = QuotientGroup.mk k := hl
    have h2 : (QuotientGroup.mk (k * a * k⁻¹ * b) : X ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hkab
    rw [← QuotientGroup.eq_one_iff]
    calc (QuotientGroup.mk (l * a * l⁻¹ * b) : X ⧸ N)
        = QuotientGroup.mk l * QuotientGroup.mk a * (QuotientGroup.mk l)⁻¹ * QuotientGroup.mk b := by
          simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      _ = QuotientGroup.mk k * QuotientGroup.mk a * (QuotientGroup.mk k)⁻¹ * QuotientGroup.mk b := by
          rw [h1]
      _ = QuotientGroup.mk (k * a * k⁻¹ * b) := by
          simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      _ = 1 := h2
  obtain ⟨g₁, hg₁, hg₁'⟩ := exists_odd_conj ha'2 hb2 (odd_orderOf_of_mem_odd hN hab)
  have hg₁L : g₁ ∈ L := (Subgroup.zpowers_le.2 (L.mul_mem hal hb)) hg₁
  refine ⟨g₁ * l, L.mul_mem hg₁L hlL, ?_⟩
  calc g₁ * l * a * (g₁ * l)⁻¹ = g₁ * (l * a * l⁻¹) * g₁⁻¹ := by group
    _ = b := hg₁'

omit [Finite X] in
theorem exists_conj_of_lifts (hN : Odd (Nat.card N)) {L : Subgroup X} {u v u₀ v₀ k : X} (hu : u ∈ L)
    (hv : v ∈ L) (hu2 : u * u = 1) (hv2 : v * v = 1) (hu₀2 : u₀ * u₀ = 1) (hv₀2 : v₀ * v₀ = 1)
    (hu₀ : u₀ * u ∈ N) (hv₀ : v₀ * v ∈ N)
    (hk : QuotientGroup.mk' N k ∈ L.map (QuotientGroup.mk' N)) (hkc : k * u₀ * k⁻¹ = v₀) :
    ∃ g ∈ L, g * u * g⁻¹ = v := by
  refine exists_conj_of_bar hN hu hv hu2 hv2 hk ?_
  rw [← QuotientGroup.eq_one_iff]
  have hmk : ∀ {a b : X}, a * a = 1 → a * b ∈ N → (QuotientGroup.mk b : X ⧸ N) = QuotientGroup.mk a := by
    intro a b ha hab
    have h1 : (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b = 1 := by
      rw [← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq_one_iff _).2 hab
    have h2 : (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk a = 1 := by
      rw [← QuotientGroup.mk_mul, ha]
      rfl
    exact (mul_left_cancel (h1.trans h2.symm))
  have e1 := hmk hu₀2 hu₀
  have e2 := hmk hv₀2 hv₀
  have e3 : (QuotientGroup.mk (k * u₀ * k⁻¹) : X ⧸ N) = QuotientGroup.mk v₀ := by rw [hkc]
  calc (QuotientGroup.mk (k * u * k⁻¹ * v) : X ⧸ N)
      = QuotientGroup.mk k * QuotientGroup.mk u * (QuotientGroup.mk k)⁻¹ * QuotientGroup.mk v := by
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    _ = QuotientGroup.mk k * QuotientGroup.mk u₀ * (QuotientGroup.mk k)⁻¹ * QuotientGroup.mk v₀ := by
        rw [e1, e2]
    _ = QuotientGroup.mk (k * u₀ * k⁻¹) * QuotientGroup.mk v₀ := by
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    _ = QuotientGroup.mk (v₀ * v₀) := by rw [e3, ← QuotientGroup.mk_mul]
    _ = 1 := by rw [hv₀2]; rfl

end Lift

end Abstract


section Glue

variable {G : Type} [Group G] [Finite G] {z : G} {K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem lc_le_cen (z : G) : LC z ≤ Cen z := Subgroup.map_subtype_le _

theorem invol_L_of_lift
    (h31 : ∀ u v : G, u ∈ K₁ ⊔ K₂ → v ∈ K₁ ⊔ K₂ → u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u ≠ z →
      v ≠ z → ∃ k ∈ K₁ ⊔ K₂, k * u * k⁻¹ = v)
    (hK : K₁ ⊔ K₂ ≤ Cz z) (hLB : ((K₁ ⊔ K₂).subgroupOf (Cz z)).map (piC z) = LBar z)
    {x : G} (hxP : x ∈ K₁ ⊔ K₂) (hx2 : orderOf x = 2) (hxz : x ≠ z) :
    ∀ u ∈ LC z, orderOf u = 2 → u ≠ z →
      IsConj x u ∧ ∀ v ∈ LC z, orderOf v = 2 → v ≠ z → IVK.ConjUnder (LC z) u v := by
  set N : Subgroup ↥(Cen z) := pPrimeCore 2 ↥(Cen z) with hNdef
  have hN : Odd (Nat.card N) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hmemL : ∀ {u : G} (hu : u ∈ LC z), (⟨u, lc_le_cen z hu⟩ : ↥(Cen z)) ∈
      (LC z).subgroupOf (Cen z) := fun hu => hu
  have hbarL : ((LC z).subgroupOf (Cen z)).map (QuotientGroup.mk' N) = LBar z := by
    unfold LBar barOf
    rfl
  have hlift : ∀ {u : G} (hu : u ∈ LC z), orderOf u = 2 →
      ∃ u₀ : ↥(Cen z), (u₀ : G) ∈ K₁ ⊔ K₂ ∧ orderOf u₀ = 2 ∧
        u₀ * (⟨u, lc_le_cen z hu⟩ : ↥(Cen z)) ∈ N := by
    intro u hu hu2
    have hu' : orderOf (⟨u, lc_le_cen z hu⟩ : ↥(Cen z)) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hu2
    have hY : QuotientGroup.mk' N (⟨u, lc_le_cen z hu⟩ : ↥(Cen z)) ∈
        ((K₁ ⊔ K₂).subgroupOf (Cz z)).map (QuotientGroup.mk' N) := by
      have h1 : ((K₁ ⊔ K₂).subgroupOf (Cz z)).map (QuotientGroup.mk' N) = LBar z := hLB
      rw [h1]
      exact ⟨⟨u, lc_le_cen z hu⟩, hu, rfl⟩
    obtain ⟨u₀, hu₀Y, hu₀o, hu₀N⟩ := exists_invol_lift hN hu' hY
    exact ⟨u₀, hu₀Y, hu₀o, hu₀N⟩
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    omega
  have hmul : ∀ {a : ↥(Cen z)}, orderOf a = 2 → a * a = 1 := by
    intro a ha
    have := pow_orderOf_eq_one a
    rwa [ha, pow_two] at this
  have hne : ∀ {u : G} (hu : u ∈ LC z), orderOf u = 2 → u ≠ z → ∀ {u₀ : ↥(Cen z)},
      orderOf u₀ = 2 → u₀ * (⟨u, lc_le_cen z hu⟩ : ↥(Cen z)) ∈ N → (u₀ : G) ≠ z := by
    intro u hu hu2 huz u₀ hu₀o hu₀N hu₀z
    have hu0 := hmul hu₀o
    have hzc : ((u₀ : ↥(Cen z)) : G) = z := hu₀z
    have hcomm : (u₀ : ↥(Cen z)) * ⟨u, lc_le_cen z hu⟩ = ⟨u, lc_le_cen z hu⟩ * u₀ := by
      apply Subtype.ext
      show (u₀ : G) * u = u * (u₀ : G)
      rw [hzc]
      exact (Subgroup.mem_centralizer_singleton_iff.1 (lc_le_cen z hu)).symm
    have hu1 : (⟨u, lc_le_cen z hu⟩ : ↥(Cen z)) * ⟨u, lc_le_cen z hu⟩ = 1 := by
      have : orderOf (⟨u, lc_le_cen z hu⟩ : ↥(Cen z)) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact hu2
      exact hmul this
    have hsq : (u₀ * ⟨u, lc_le_cen z hu⟩) * (u₀ * ⟨u, lc_le_cen z hu⟩) = 1 := by
      calc (u₀ * ⟨u, lc_le_cen z hu⟩) * (u₀ * ⟨u, lc_le_cen z hu⟩)
          = u₀ * (⟨u, lc_le_cen z hu⟩ * u₀) * ⟨u, lc_le_cen z hu⟩ := by group
        _ = u₀ * (u₀ * ⟨u, lc_le_cen z hu⟩) * ⟨u, lc_le_cen z hu⟩ := by rw [hcomm]
        _ = (u₀ * u₀) * (⟨u, lc_le_cen z hu⟩ * ⟨u, lc_le_cen z hu⟩) := by group
        _ = 1 := by rw [hu0, hu1, one_mul]
    have h1 := eq_one_of_mul_self_of_mem_odd hN hu₀N hsq
    have h2 : (⟨u, lc_le_cen z hu⟩ : ↥(Cen z)) = u₀⁻¹ := by
      have := mul_eq_one_iff_eq_inv.1 h1
      exact (inv_eq_of_mul_eq_one_right h1).symm ▸ rfl
    apply huz
    have h3 : (⟨u, lc_le_cen z hu⟩ : ↥(Cen z)) = u₀ := by
      rw [h2, inv_eq_of_mul_eq_one_right hu0]
    have h4 := congrArg Subtype.val h3
    exact h4.trans hzc
  intro u hu hu2 huz
  obtain ⟨u₀, hu₀K, hu₀o, hu₀N⟩ := hlift hu hu2
  have hu₀z := hne hu hu2 huz hu₀o hu₀N
  have hu₀1 : (u₀ : G) ≠ 1 := by
    intro h
    have : orderOf (u₀ : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu₀o
    rw [h, orderOf_one] at this
    omega
  have hu₀sq : (u₀ : G) * (u₀ : G) = 1 := by
    have := congrArg Subtype.val (hmul hu₀o)
    exact this
  have hxsq : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  refine ⟨?_, fun v hv hv2 hvz => ?_⟩
  ·
    obtain ⟨k, -, hk⟩ := h31 x (u₀ : G) hxP hu₀K hxsq hu₀sq hx1 hu₀1 hxz hu₀z
    have hxu₀ : IsConj x (u₀ : G) := isConj_iff.2 ⟨k, hk⟩
    obtain ⟨g, -, hg⟩ := exists_odd_conj (hmul hu₀o)
      (hmul (by rw [Subgroup.orderOf_mk]; exact hu2)) (odd_orderOf_of_mem_odd hN hu₀N)
    have hu₀u : IsConj (u₀ : G) u := by
      refine isConj_iff.2 ⟨(g : G), ?_⟩
      have := congrArg Subtype.val hg
      simpa using this
    exact hxu₀.trans hu₀u
  ·
    obtain ⟨v₀, hv₀K, hv₀o, hv₀N⟩ := hlift hv hv2
    have hv₀z := hne hv hv2 hvz hv₀o hv₀N
    have hv₀1 : (v₀ : G) ≠ 1 := by
      intro h
      have : orderOf (v₀ : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hv₀o
      rw [h, orderOf_one] at this
      omega
    have hv₀sq : (v₀ : G) * (v₀ : G) = 1 := by
      have := congrArg Subtype.val (hmul hv₀o)
      exact this
    obtain ⟨k, hkK, hk⟩ := h31 (u₀ : G) (v₀ : G) hu₀K hv₀K hu₀sq hv₀sq hu₀1 hv₀1 hu₀z hv₀z
    have hkC : k ∈ Cen z := hK hkK
    have hk' : QuotientGroup.mk' N (⟨k, hkC⟩ : ↥(Cen z)) ∈
        ((LC z).subgroupOf (Cen z)).map (QuotientGroup.mk' N) := by
      rw [hbarL, ← hLB]
      exact ⟨⟨k, hkC⟩, hkK, rfl⟩
    obtain ⟨g, hgL, hg⟩ := exists_conj_of_lifts hN (hmemL hu) (hmemL hv)
      (hmul (by rw [Subgroup.orderOf_mk]; exact hu2)) (hmul (by rw [Subgroup.orderOf_mk]; exact hv2))
      (hmul hu₀o) (hmul hv₀o) hu₀N hv₀N hk'
      (Subtype.ext (by simpa using hk))
    refine ⟨(g : G), ?_, ?_⟩
    · exact hgL
    · have := congrArg Subtype.val hg
      simpa using this

end Glue

end CFSG.GH74.GLS.Stage1.Main
