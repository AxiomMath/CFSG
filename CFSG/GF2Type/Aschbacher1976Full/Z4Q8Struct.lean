module

public import CFSG.GF2Type.Aschbacher1976Full.Z4Q8Gen

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Z4Q8

open CFSG CFSG.Blueprint CFSG.EvenSporadicStandard.Finkelstein77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_gen_Zc {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) :
    ∃ k : G, k ∈ Zc z ∧ orderOf k = 4 ∧ Subgroup.zpowers k = Zc z ∧ k ^ 2 = z := by
  obtain ⟨Z, A, hZeq, hcyc, -⟩ := unpack hZ hz
  have hcycZc : IsCyclic ↥(Zc z) := by rw [hZeq]; exact hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(Zc z))
  set k : G := (g : G) with hkdef
  have hkZ : k ∈ Zc z := g.2
  have hzp : Subgroup.zpowers k = Zc z := by
    apply le_antisymm
    · exact Subgroup.zpowers_le.mpr hkZ
    · intro x hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have := congrArg Subtype.val hn
      simpa using this
  have hord : orderOf k = 4 := by
    have h1 : orderOf g = Nat.card ↥(Zc z) := by
      apply orderOf_eq_card_of_forall_mem_zpowers
      intro x
      exact hg x
    rw [Subgroup.orderOf_coe] at *
    rw [h1, card_Zc hZ hz]
  refine ⟨k, hkZ, hord, hzp, ?_⟩
  have hk2Z : k ^ 2 ∈ Zc z := (Zc z).pow_mem hkZ 2
  have hk4 : (k ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    exact pow_eq_one_iff_modEq.mpr (by rw [hord]; decide)
  rcases involution_eq_one_or_eq hcycZc hz (z_mem_Zc hZ hz) hk2Z hk4 with h | h
  · exfalso
    have hdvd : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    norm_num at hdvd
  · exact h

theorem card_Hz_and_T {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {T : Subgroup G}
    (hTH : T ≤ Hz z) (hTp : IsPGroup 2 ↥T) (hFT : Fz z ≤ T) {y : G} (hyT : y ∈ T)
    (hyF : y ∉ Fz z) : Nat.card ↥(Hz z) = 96 ∧ Nat.card ↥T = 32 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm6, hH⟩ := card_Hz_eq_mul hZ hz
  obtain ⟨n, hTn⟩ := (IsPGroup.iff_card).mp hTp
  have hF16 := card_Fz hZ hz
  have hFdvdT : Nat.card ↥(Fz z) ∣ Nat.card ↥T := Subgroup.card_dvd_of_le hFT
  have hTdvdH : Nat.card ↥T ∣ Nat.card ↥(Hz z) := Subgroup.card_dvd_of_le hTH
  have hFT_ne : Fz z ≠ T := fun h => hyF (h ▸ hyT)
  have hTgt : 16 < Nat.card ↥T := by
    rcases lt_or_eq_of_le (Nat.le_of_dvd (by rw [hTn]; positivity) (by
      rw [← hF16]; exact hFdvdT) : 16 ≤ Nat.card ↥T) with h | h
    · exact h
    · exfalso
      exact hFT_ne (Subgroup.eq_of_le_of_card_ge hFT (by rw [hF16]; exact le_of_eq h.symm))
  have hn5 : 5 ≤ n := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ n ≤ 16 := by
      calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 16 := by norm_num
    rw [← hTn] at this
    omega
  have h32 : 32 ∣ Nat.card ↥T := by
    rw [hTn]
    exact (show (32 : ℕ) = 2 ^ 5 by norm_num) ▸ Nat.pow_dvd_pow 2 hn5
  have h32H : 32 ∣ 16 * m := by
    rw [← hH]
    exact h32.trans hTdvdH
  have hm2 : 2 ∣ m := by omega
  have hmle : m ≤ 6 := Nat.le_of_dvd (by norm_num) hm6
  have hm : m = 2 ∨ m = 6 := by
    interval_cases m <;> simp_all
  rcases hm with rfl | rfl
  ·
    exfalso
    have hHp : IsPGroup 2 ↥(Hz z) := IsPGroup.of_card (n := 5) (by rw [hH]; norm_num)
    have htop : (⊤ : Subgroup ↥(Hz z)) ≤ pCore 2 ↥(Hz z) :=
      le_sSup ⟨Subgroup.normal_top, hHp.of_equiv Subgroup.topEquiv.symm⟩
    have hgf : generalizedFitting ↥(Hz z) = ⊤ := by
      rw [generalizedFitting_Hz_eq_pCore hZ hz]
      exact top_le_iff.mp htop
    have hFH : Fz z = Hz z := by
      show (generalizedFitting ↥(Hz z)).map (Hz z).subtype = Hz z
      rw [hgf]
      ext x
      simp
    rw [hFH, hH] at hF16
    omega
  · refine ⟨by rw [hH], ?_⟩
    have hdvd : 2 ^ n ∣ 96 := by
      have h96 := hTdvdH
      rw [hTn, hH] at h96
      norm_num at h96
      exact h96
    have hle : 2 ^ n ≤ 96 := Nat.le_of_dvd (by norm_num) hdvd
    have hn6 : n ≤ 6 := by
      by_contra hn
      push Not at hn
      have : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    interval_cases n
    · rw [hTn]
      norm_num
    · norm_num at hdvd

theorem inv_mul_mem_of_card_two {T N : Subgroup G} (hNT : N ≤ T)
    (hcard : Nat.card ↥T = 2 * Nat.card ↥N) (hnorm : (N.subgroupOf T).Normal) {x s : G}
    (hx : x ∈ T) (hs : s ∈ T) (hxN : x ∉ N) (hsN : s ∉ N) : s⁻¹ * x ∈ N := by
  have hq : Nat.card (↥T ⧸ N.subgroupOf T) = 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf T)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv] at h1
    have hpos : 0 < Nat.card ↥N := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans (hcard.trans (by ring)))
  obtain ⟨a, b, -, hall⟩ := Nat.card_eq_two_iff.mp hq
  have hall' : ∀ w : ↥T ⧸ N.subgroupOf T, w = a ∨ w = b := fun w => by
    have hw : w ∈ ({a, b} : Set (↥T ⧸ N.subgroupOf T)) := by
      rw [hall]
      exact Set.mem_univ w
    simpa using hw
  set qx : ↥T ⧸ N.subgroupOf T := QuotientGroup.mk ⟨x, hx⟩ with hqx
  set qs : ↥T ⧸ N.subgroupOf T := QuotientGroup.mk ⟨s, hs⟩ with hqs
  have hx1 : qx ≠ 1 := by
    intro h
    rw [hqx, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact hxN h
  have hs1 : qs ≠ 1 := by
    intro h
    rw [hqs, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact hsN h
  have hqeq : qs = qx := by
    rcases hall' 1 with h1 | h1
    · rcases hall' qx with hx' | hx'
      · exact absurd (hx'.trans h1.symm) hx1
      rcases hall' qs with hs' | hs'
      · exact absurd (hs'.trans h1.symm) hs1
      rw [hx', hs']
    · rcases hall' qx with hx' | hx'
      · rcases hall' qs with hs' | hs'
        · rw [hx', hs']
        · exact absurd (hs'.trans h1.symm) hs1
      · exact absurd (hx'.trans h1.symm) hx1
  rw [hqs, hqx, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hqeq
  simpa using hqeq

theorem zpowers_inf_eq_bot {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {k y : G}
    (hkZp : Subgroup.zpowers k = Zc z) (hy4 : orderOf y = 4)
    (hyF : y ∉ Fz z) (htF : y ^ 2 ∈ Fz z) (htz : y ^ 2 ≠ z) :
    Subgroup.zpowers k ⊓ Subgroup.zpowers y = ⊥ := by
  have hcycZc : IsCyclic ↥(Zc z) := by
    obtain ⟨Z', A', hZeq, hcyc', -⟩ := unpack hZ hz
    rw [hZeq]
    exact hcyc'
  have ht2 : orderOf (y ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (n := 2) (by norm_num) (by rw [hy4]; norm_num), hy4]
  have hy4' : y ^ 4 = 1 := by
    rw [← hy4]
    exact pow_orderOf_eq_one y
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  obtain ⟨hwK, hwY⟩ := Subgroup.mem_inf.mp hw
  have hwZc : w ∈ Zc z := hkZp ▸ hwK
  have hwF : w ∈ Fz z := ((mem_Zc_iff hZ hz).mp hwZc).1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hwY
  obtain ⟨m, hm⟩ := Int.even_or_odd' j
  rcases hm with hm | hm
  ·
    have hw2 : w ∈ Subgroup.zpowers (y ^ 2) := by
      have e : w = (y ^ 2) ^ m := by
        rw [← hj, hm, zpow_mul]
        simp
      rw [e]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    rcases mem_zpowers_two ht2 hw2 with h1 | h1
    · exact h1
    · exfalso
      have hy2Z : y ^ 2 ∈ Zc z := h1 ▸ hwZc
      have hsq : (y ^ 2) ^ 2 = 1 := by
        rw [← pow_mul]
        exact hy4'
      rcases involution_eq_one_or_eq hcycZc hz (z_mem_Zc hZ hz) hy2Z hsq with h2 | h2
      · have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one h2
        rw [hy4] at hdvd
        norm_num at hdvd
      · exact htz h2
  ·
    exfalso
    apply hyF
    have e : w = (y ^ 2) ^ m * y := by
      rw [← hj, hm, zpow_add_one, zpow_mul]
      simp
    have hy_eq : y = ((y ^ 2) ^ m)⁻¹ * w := by
      rw [e]
      group
    rw [hy_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ htF _)) hwF

theorem card_A {k y : G} (hky : k * y = y * k) (hk4 : orderOf k = 4) (hy4 : orderOf y = 4)
    (hKY : Subgroup.zpowers k ⊓ Subgroup.zpowers y = ⊥) :
    Nat.card ↥(Subgroup.zpowers k ⊔ Subgroup.zpowers y) = 16 := by
  have hcomm : ∀ c ∈ Subgroup.zpowers k, ∀ d ∈ Subgroup.zpowers y, c * d = d * c := by
    intro c hc d hd
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact ((Commute.zpow_zpow (show Commute k y from hky) i j)).eq
  have key := natCard_inf_mul_natCard_sup (Subgroup.zpowers k) (Subgroup.zpowers y) hcomm
  rw [hKY, Subgroup.card_bot, Nat.card_zpowers, Nat.card_zpowers, hk4, hy4] at key
  omega

theorem involution_of_A {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) {k y : G}
    (hky : k * y = y * k) (hkZ : k ∈ Zc z) (hkZp : Subgroup.zpowers k = Zc z) (hy4 : orderOf y = 4)
    (hKY : Subgroup.zpowers k ⊓ Subgroup.zpowers y = ⊥) {x : G}
    (hx : x ∈ Subgroup.zpowers k ⊔ Subgroup.zpowers y) (hx2 : x ^ 2 = 1) :
    x = 1 ∨ x = z ∨ x = y ^ 2 ∨ x = z * y ^ 2 := by
  have hcycZc : IsCyclic ↥(Zc z) := by
    obtain ⟨Z', A', hZeq, hcyc', -⟩ := unpack hZ hz
    rw [hZeq]
    exact hcyc'
  have hcomm : ∀ c ∈ Subgroup.zpowers k, ∀ d ∈ Subgroup.zpowers y, c * d = d * c := by
    intro c hc d hd
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact ((Commute.zpow_zpow (show Commute k y from hky) i j)).eq
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_sup_iff' hcomm).mp hx
  have hcd : c ^ 2 * d ^ 2 = 1 := by
    rw [← hx2]
    calc c ^ 2 * d ^ 2 = c * (c * d) * d := by rw [sq, sq]; group
      _ = c * (d * c) * d := by rw [hcomm c hc d hd]
      _ = (c * d) ^ 2 := by rw [sq]; group
  have hc2 : c ^ 2 ∈ Subgroup.zpowers k ⊓ Subgroup.zpowers y := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ hc 2, ?_⟩
    have : c ^ 2 = (d ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hcd
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hd 2)
  rw [hKY, Subgroup.mem_bot] at hc2
  have hd2 : d ^ 2 = 1 := by
    rw [hc2, one_mul] at hcd
    exact hcd
  have hcZ : c = 1 ∨ c = z := by
    have hcZc : c ∈ Zc z := hkZp ▸ hc
    exact involution_eq_one_or_eq hcycZc hz (z_mem_Zc hZ hz) hcZc hc2
  have hy2 : orderOf (y ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (n := 2) (by norm_num) (by rw [hy4]; norm_num), hy4]
  have hdY : d = 1 ∨ d = y ^ 2 := by
    have hcycY : IsCyclic ↥(Subgroup.zpowers y) := inferInstance
    exact involution_eq_one_or_eq (Z := Subgroup.zpowers y) hcycY hy2
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) 2) hd hd2
  rcases hcZ with rfl | rfl <;> rcases hdY with rfl | rfl
  · left; simp
  · right; right; left; simp
  · right; left; simp
  · right; right; right; rfl

end CFSG.GF2Type.Aschbacher1976Full.Z4Q8
