module

public import CFSG.GH74.GLS.Stage4.Q9.OddPackage
public import CFSG.GH74.GLS.Stage4.Q9.SD32
public import CFSG.GH74.GLS.Stage4.Q9.Aut4
public import CFSG.GH74.GLS.Stage4.Q9.OddSmall5
public import CFSG.GH74.GLS.Stage4.Q9.Bound3

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

section SD32Facts

variable {G : Type*} [Group G]

private theorem zpow_eq_one_or_self_of_sq {w : G} (hw : w ^ 2 = 1) (k : ℤ) :
    w ^ k = 1 ∨ w ^ k = w := by
  have h2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hw]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

private theorem conj_zpow_of_conj {h t : G} (hth : t * h * t⁻¹ = h ^ 7) (k : ℤ) :
    t * h ^ k * t⁻¹ = h ^ (7 * k) := by
  rw [← conj_zpow, hth, ← zpow_natCast, ← zpow_mul]
  norm_num

private theorem zpowers_le_normalizer_zpowers {h t : G} (htt : t * t = 1)
    (hth : t * h * t⁻¹ = h ^ 7) :
    Subgroup.zpowers t ≤ Subgroup.normalizer (Subgroup.zpowers h : Set G) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [conj_zpow_of_conj hth k]
    exact Subgroup.mem_zpowers_iff.mpr ⟨7 * k, rfl⟩
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have e : t * (t * y * t⁻¹) * t⁻¹ = y := by
      calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
        _ = y := by rw [htt]; group
    rw [← e, ← hk, conj_zpow_of_conj hth k]
    exact Subgroup.mem_zpowers_iff.mpr ⟨7 * k, rfl⟩

private theorem mem_sup_zpowers_cases {h t : G} (htt : t * t = 1) (hth : t * h * t⁻¹ = h ^ 7)
    {s : G} (hs : s ∈ Subgroup.zpowers h ⊔ Subgroup.zpowers t) :
    s ∈ Subgroup.zpowers h ∨ s * t ∈ Subgroup.zpowers h := by
  have hs' : s ∈ (↑(Subgroup.zpowers h ⊔ Subgroup.zpowers t) : Set G) := hs
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (zpowers_le_normalizer_zpowers htt hth)] at hs'
  obtain ⟨a, ha, b, hb, hab⟩ := hs'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have htt' : t ^ 2 = 1 := by rw [pow_two]; exact htt
  have hab' : a * t ^ k = s := hab
  rcases zpow_eq_one_or_self_of_sq htt' k with h1 | h1
  · left
    rw [h1, mul_one] at hab'
    rw [← hab']
    exact ha
  · right
    rw [h1] at hab'
    rw [← hab', mul_assoc, htt, mul_one]
    exact ha

private theorem card_sup_zpowers_involution {h t : G} (htt : t * t = 1)
    (hth : t * h * t⁻¹ = h ^ 7) (htH : t ∉ Subgroup.zpowers h) :
    Nat.card ↥(Subgroup.zpowers h ⊔ Subgroup.zpowers t) = 2 * Nat.card (Subgroup.zpowers h) := by
  set H := Subgroup.zpowers h with hHdef
  set K := H ⊔ Subgroup.zpowers t with hK
  have hHK : H ≤ K := le_sup_left
  have htK : t ∈ K := mem_sup_right (mem_zpowers t)
  have hidx : (H.subgroupOf K).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htK⟩, fun b => ?_⟩
    simp only [mem_subgroupOf, Subgroup.coe_mul]
    rcases mem_sup_zpowers_cases htt hth b.2 with h1 | h1
    · refine Or.inr ⟨h1, fun h' => htH ?_⟩
      have := mul_mem (inv_mem h1) h'
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨h1, fun h' => htH ?_⟩
      have := mul_mem (inv_mem h') h1
      rwa [inv_mul_cancel_left] at this
  have hmul := Subgroup.relIndex_mul_card H K
  rw [inf_eq_left.mpr hHK] at hmul
  rw [← hmul]
  exact congrArg (· * Nat.card H) hidx

private theorem not_mem_zpowers_of_ne_pow_eight {h t : G} (hh : orderOf h = 16)
    (ht : orderOf t = 2) (hne : h ^ 8 ≠ t) : t ∉ Subgroup.zpowers h := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hsq : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hh16 : h ^ 16 = 1 := by rw [← hh]; exact pow_orderOf_eq_one h
  have hz2 : (h ^ 8) ^ 2 = 1 := by rw [← pow_mul]; exact hh16
  have h1 : h ^ (2 * k) = 1 := by
    rw [zpow_mul', hk, zpow_two, ← pow_two]
    exact hsq
  have hdvd : (16 : ℤ) ∣ 2 * k := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    simpa [hh] using this
  obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 8 * m := ⟨k / 8, by omega⟩
  have hkm : h ^ k = (h ^ 8) ^ m := by
    rw [hm, zpow_mul]
    norm_num
  rcases zpow_eq_one_or_self_of_sq hz2 m with h2 | h2
  · rw [hkm, h2] at hk
    have : orderOf t = 1 := by rw [← hk]; exact orderOf_one
    omega
  · rw [hkm, h2] at hk
    exact hne hk

private theorem eq_one_or_pow_eight_of_central {h t : G} (hh : orderOf h = 16) (htt : t * t = 1)
    (hth : t * h * t⁻¹ = h ^ 7) {s : G} (hs : s ∈ Subgroup.zpowers h ⊔ Subgroup.zpowers t)
    (hsh : s * h = h * s) (hst : s * t = t * s) : s = 1 ∨ s = h ^ 8 := by
  have hh16 : h ^ 16 = 1 := by rw [← hh]; exact pow_orderOf_eq_one h
  have hz2 : (h ^ 8) ^ 2 = 1 := by rw [← pow_mul]; exact hh16
  rcases mem_sup_zpowers_cases htt hth hs with h1 | h1
  ·
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp h1
    have e1 : t * h ^ i * t⁻¹ = h ^ i := by rw [← hst, mul_inv_cancel_right]
    have e2 : h ^ (7 * i) = h ^ i := by rw [← conj_zpow_of_conj hth i, e1]
    have e3 : h ^ (6 * i) = 1 := by
      calc h ^ (6 * i) = h ^ (7 * i) * (h ^ i)⁻¹ := by
            rw [← zpow_neg, ← zpow_add]
            congr 1
            ring
        _ = 1 := by rw [e2]; exact mul_inv_cancel _
    have e4 : (16 : ℤ) ∣ 6 * i := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr e3
      simpa [hh] using this
    obtain ⟨m, hm⟩ : ∃ m : ℤ, i = 8 * m := ⟨i / 8, by omega⟩
    have hkm : h ^ i = (h ^ 8) ^ m := by
      rw [hm, zpow_mul]
      norm_num
    rcases zpow_eq_one_or_self_of_sq hz2 m with h2 | h2
    · left
      rw [hkm, h2]
    · right
      rw [hkm, h2]
  ·
    exfalso
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hs_eq : s = h ^ i * t := by rw [hi, mul_assoc, htt, mul_one]
    have e1 : s * h = h ^ i * h ^ 7 * t := by
      rw [hs_eq]
      calc h ^ i * t * h = h ^ i * (t * h * t⁻¹) * t := by group
        _ = h ^ i * h ^ 7 * t := by rw [hth]
    have e2 : h * s = h * h ^ i * t := by rw [hs_eq, mul_assoc]
    have e3 : h ^ i * h ^ 7 = h ^ i * h := by
      have e := mul_right_cancel (e1.symm.trans (hsh.trans e2))
      rw [e]
      exact (Commute.self_zpow h i).eq
    have e4 : h ^ 7 = h := mul_left_cancel e3
    have e5 : h ^ 6 = 1 := by
      calc h ^ 6 = h ^ 7 * h⁻¹ := by group
        _ = 1 := by rw [e4]; exact mul_inv_cancel h
    have e6 : orderOf h ∣ 6 := orderOf_dvd_of_pow_eq_one e5
    rw [hh] at e6
    omega

private theorem conj_pow_four_involution {h t : G} (hh : orderOf h = 16) (hth : t * h * t⁻¹ = h ^ 7)
    (hzt : h ^ 8 * t = t * h ^ 8) : h ^ 4 * t * (h ^ 4)⁻¹ = h ^ 8 * t := by
  have hh16 : h ^ 16 = 1 := by rw [← hh]; exact pow_orderOf_eq_one h
  have e1 : t * h ^ 12 * t⁻¹ = h ^ 4 := by
    rw [← conj_pow, hth, ← pow_mul]
    rw [show 7 * 12 = 16 * 5 + 4 by norm_num, pow_add, pow_mul, hh16, one_pow, one_mul]
  have e2 : h ^ 4 * t = t * h ^ 12 := by
    rw [← e1]
    group
  calc h ^ 4 * t * (h ^ 4)⁻¹ = t * h ^ 12 * (h ^ 4)⁻¹ := by rw [e2]
    _ = t * h ^ 8 := by group
    _ = h ^ 8 * t := hzt.symm

end SD32Facts

theorem key5 {G : Type*} [Group G] [Finite G] {z t x h : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2) (hzt : z * t = t * z) (hne : z ≠ t)
    (hx5 : orderOf x = 5) (hxz : z * x = x * z) (hxt : t * x = x * t)
    (hone : ∀ u : G, orderOf u = 2 → IsConj z u)
    (hCpr : ∀ r : ℕ, r.Prime → r ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) →
      r = 2 ∨ r = 3 ∨ r = 5)
    (hC5 : (Nat.card (Subgroup.centralizer ({z} : Set G))).factorization 5 ≤ 2)
    (hG3 : (Nat.card G).factorization 3 ≤ 4)
    (hh : orderOf h = 16) (hth : t * h * t⁻¹ = h ^ 7) (hh8 : h ^ 8 = z) (hhx : h * x = x * h)
    (hC2 : (Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({z} : Set G))).factorization 2 = 5)
    (hoddC : ∀ M : Subgroup G, M ≤ Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({z} : Set G) →
      (∀ c ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ m ∈ M, c * m * c⁻¹ ∈ M) →
      Odd (Nat.card M) → M ≤ Subgroup.zpowers x)
    (Kb : Subgroup G) (hKbx : ∀ k ∈ Kb, k * x = x * k) (hzKb : z ∈ Kb)
    (hKbz : ∀ k ∈ Kb, z * k = k * z)
    (Pb : Subgroup G) (hPbK : Pb ≤ Kb) (hPb3 : IsPGroup 3 Pb) (hPb9 : Nat.card Pb = 9)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 9)
    (eb : ↥Kb ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (htns : ∀ n ∈ Subgroup.centralizer ({x} : Set G),
      (∀ y ∈ Subgroup.closure ({z, t} : Set G),
        n * y * n⁻¹ ∈ Subgroup.closure ({z, t} : Set G)) → orderOf n ≠ 3) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  classical
  have hz2 : z * z = 1 := by rw [← pow_two, ← hz]; exact pow_orderOf_eq_one z
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  have hmemA : ∀ g : G, g ∈ Subgroup.centralizer ({x} : Set G) ↔ g * x = x * g :=
    fun g => Subgroup.mem_centralizer_singleton_iff
  have hmemC : ∀ g : G, g ∈ Subgroup.centralizer ({z} : Set G) ↔ g * z = z * g :=
    fun g => Subgroup.mem_centralizer_singleton_iff
  have hzA : z ∈ Subgroup.centralizer ({x} : Set G) := (hmemA z).2 hxz
  have htA : t ∈ Subgroup.centralizer ({x} : Set G) := (hmemA t).2 hxt
  have hhA : h ∈ Subgroup.centralizer ({x} : Set G) := (hmemA h).2 hhx
  have hxA : x ∈ Subgroup.centralizer ({x} : Set G) := (hmemA x).2 rfl
  have hKA : ∀ k ∈ Kb, k ∈ Subgroup.centralizer ({x} : Set G) := fun k hk => (hmemA k).2 (hKbx k hk)
  have hht : h ^ 8 ≠ t := by rw [hh8]; exact hne
  have htnH : t ∉ Subgroup.zpowers h := not_mem_zpowers_of_ne_pow_eight hh ht hht
  set S : Subgroup G := Subgroup.zpowers h ⊔ Subgroup.zpowers t with hSdef
  have hcardS : Nat.card S = 32 := by
    rw [hSdef, card_sup_zpowers_involution ht2 hth htnH, Nat.card_zpowers, hh]
  have hhS : h ∈ S := mem_sup_left (mem_zpowers h)
  have htS : t ∈ S := mem_sup_right (mem_zpowers t)
  have hSA : S ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hhA) (Subgroup.zpowers_le.2 htA)
  have hzS : z ∈ S := hh8 ▸ S.pow_mem hhS 8
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 5) (by rw [hcardS]; norm_num)
  have hSC : S ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [hmemC, ← hh8]
      exact (Commute.self_pow h 8).eq
    · rw [hmemC]
      exact hzt.symm
  have hzZ : ∀ s ∈ S, s * z = z * s := fun s hs => (hmemC s).1 (hSC hs)
  have hZ : ∀ s ∈ S, (∀ w ∈ S, s * w = w * s) → s = 1 ∨ s = z := fun s hs hw => by
    rw [← hh8]
    exact eq_one_or_pow_eight_of_central hh ht2 hth hs (hw h hhS) (hw t htS)
  have hSyl : ¬ 2 ∣ S.relIndex (Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({z} : Set G)) := by
    intro h2
    have hSAC : S ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) :=
      le_inf hSA hSC
    have hmul : S.relIndex (Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({z} : Set G)) * Nat.card S =
        Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G)) := by
      simpa [inf_of_le_left hSAC] using
        S.relIndex_mul_card (Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ({z} : Set G))
    have hR : S.relIndex (Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({z} : Set G)) ≠ 0 :=
      left_ne_zero_of_mul (hmul ▸ Nat.card_pos.ne')
    have hS0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
    have h32 : (32 : ℕ).factorization 2 = 5 := by
      rw [show (32 : ℕ) = 2 ^ 5 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
      simp
    have hv : (S.relIndex (Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({z} : Set G)) * Nat.card S).factorization 2 = 5 := by
      rw [hmul]
      exact hC2
    rw [Nat.factorization_mul hR hS0, Finsupp.add_apply, hcardS, h32] at hv
    have hpos := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hR h2
    omega
  have hSidx : ¬ 2 ∣ S.relIndex (Subgroup.centralizer ({x} : Set G)) :=
    sylow_of_centralizer_two hz _ S hzA hSA hS2 hzS hzZ hZ hSyl
  have hn0A : h ^ 4 ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.pow_mem _ hhA 4
  have hn0z : h ^ 4 * z * (h ^ 4)⁻¹ = z := by rw [← hh8]; group
  have hn0t : h ^ 4 * t * (h ^ 4)⁻¹ = z * t := by
    rw [← hh8]
    exact conj_pow_four_involution hh hth (by rw [hh8]; exact hzt)
  have hfixz := normalizer_fixes_z hz ht hzt hne (Subgroup.centralizer ({x} : Set G)) hzA htA
    htns (h ^ 4) hn0A hn0z hn0t
  have hwc0 := isolated_of_normalizer_fixes (Subgroup.centralizer ({x} : Set G)) S hSA hS2 hSidx h t
    hhS htS hh ht2 hth hSdef hcardS (by rw [hh8]; exact hfixz)
  have hwc : ∀ g ∈ Subgroup.centralizer ({x} : Set G), g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z := by
    simpa only [hh8] using hwc0
  obtain ⟨O, hOA, hOnorm, hOodd, hOdec, hOmax, -, hOprime, -, h5t, h5zt⟩ :=
    oddcore_package hz ht hzt hne hone hCpr hC5 (Subgroup.centralizer ({x} : Set G)) S hzA
      (fun a ha => mul_mem (mul_mem htA ha) (inv_mem htA)) hSA hS2 hSidx hzS hzZ hwc
  have hxO : x ∈ O := by
    refine Subgroup.zpowers_le.1 (hOmax (Subgroup.zpowers x) (Subgroup.zpowers_le.2 hxA) ?_ ?_)
    · intro a ha n hn
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hc : Commute a x := (hmemA a).1 ha
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
    · rw [Nat.card_zpowers, hx5]
      exact ⟨2, rfl⟩
  have hKb1 : ∀ k ∈ Kb, k ∈ O → k = 1 :=
    sl2_nine_inf_odd_normal_trivial Kb O (fun k hk o ho => hOnorm k (hKA k hk) o ho) hOodd hF eb
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3O : (Nat.card O).factorization 3 ≤ 2 := by
    have hb := sylow_bound_of_normalizing 3 O Pb hPb3
      (fun q hq o ho => hOnorm q (hKA q (hPbK hq)) o ho) (fun y hy hyO => hKb1 y (hPbK hy) hyO)
    have hP3 : (Nat.card Pb).factorization 3 = 2 := by
      rw [hPb9, show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
      simp
    omega
  have hCOz : ∀ o ∈ O, z * o = o * z → o ∈ Subgroup.zpowers x := by
    intro o ho hzo
    have hOC : O ⊓ Subgroup.centralizer ({z} : Set G) ≤
        Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) :=
      inf_le_inf_right _ hOA
    have hOCnorm : ∀ c ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ m ∈ O ⊓ Subgroup.centralizer ({z} : Set G),
          c * m * c⁻¹ ∈ O ⊓ Subgroup.centralizer ({z} : Set G) := by
      intro c hc m hm
      refine ⟨hOnorm c hc.1 m hm.1, (hmemC _).2 ?_⟩
      have hcz : Commute c z := (hmemC c).1 hc.2
      have hmz : Commute m z := (hmemC m).1 hm.2
      exact ((hcz.mul_left hmz).mul_left hcz.inv_left).eq
    have hM := hoddC (O ⊓ Subgroup.centralizer ({z} : Set G)) hOC hOCnorm
      (Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le inf_le_left))
    exact hM ⟨ho, (hmemC o).2 hzo.symm⟩
  have hOx : ∀ o ∈ O, o ∈ Subgroup.zpowers x :=
    odd_core_small5 hz ht hzt hne hx5 hxz hxt O hOodd hOA hOnorm hxO hCOz hOprime h3O h5t h5zt Kb
      hKA hzKb hKbz hF eb
  intro a ha
  obtain ⟨c, -, hcz, o, ho, rfl⟩ := hOdec a ha
  rw [hmemC]
  have hoz : o * z = z * o := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hOx o ho)
    exact (Commute.zpow_left hxz.symm k).eq
  rw [mul_assoc, hoz, ← mul_assoc, hcz, mul_assoc]

end CFSG.GH74.GLS.Stage4.Q9
