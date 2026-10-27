module

public import CFSG.ClassicalInvolution.Q3.TL3TwistQuot
public import CFSG.ClassicalInvolution.Q3.TL3C1

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {N : Subgroup Y} [N.Normal]

omit [Finite Y] [N.Normal] in
theorem pow_conj_central {x t n : Y} (hn : ∀ a : Y, a * n = n * a) (h : x * t * x⁻¹ = t * n)
    (j : ℕ) : x ^ j * t * (x ^ j)⁻¹ = t * n ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hcomm : x * n ^ j * x⁻¹ = n ^ j := by
      have h1 : x * n ^ j = n ^ j * x := (Commute.pow_right (hn x) j).eq
      rw [h1]
      group
    calc x ^ (j + 1) * t * (x ^ (j + 1))⁻¹ = x * (x ^ j * t * (x ^ j)⁻¹) * x⁻¹ := by group
      _ = x * (t * n ^ j) * x⁻¹ := by rw [ih]
      _ = (x * t * x⁻¹) * (x * n ^ j * x⁻¹) := by group
      _ = (t * n) * n ^ j := by rw [h, hcomm]
      _ = t * n ^ (j + 1) := by rw [pow_succ]; group

omit [N.Normal] in
theorem eq_one_of_pow_odd {n : Y} {m : ℕ} (hm : Odd m) (h2 : IsPGroup 2 ↥(Subgroup.zpowers n))
    (h : n ^ m = 1) : n = 1 := by
  obtain ⟨a, ha⟩ := h2.exists_card_eq
  rw [Nat.card_zpowers] at ha
  have hdvd : orderOf n ∣ m := orderOf_dvd_of_pow_eq_one h
  rw [ha] at hdvd
  by_cases ha0 : a = 0
  · rw [ha0, pow_zero] at ha
    exact orderOf_eq_one_iff.mp ha
  · exfalso
    have h2m : 2 ∣ m := (dvd_pow_self 2 ha0).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2m)

theorem exists_lift_centralizer (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N) {m : ℕ}
    (hm : Odd m) {x : Y}
    (hx : QuotientGroup.mk' N x ∈
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)))
    (hxm : (QuotientGroup.mk' N x) ^ m = 1) :
    ∃ g ∈ Subgroup.centralizer ({t} : Set Y), g ^ m = 1 ∧
      QuotientGroup.mk' N g = QuotientGroup.mk' N x := by
  have hxN : x ^ m ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 := hxm
    rw [← map_pow] at h1
    exact h1
  obtain ⟨n', hn'N, hn'⟩ : ∃ n' ∈ N, n' ^ m = (x ^ m)⁻¹ := by
    have hcop : (Nat.card ↥N).Coprime m := by
      obtain ⟨a, ha⟩ := hN2.exists_card_eq
      rw [ha]
      exact (Nat.coprime_two_left.mpr hm).pow_left a
    obtain ⟨n', hn'⟩ := (powCoprime hcop).surjective ⟨(x ^ m)⁻¹, N.inv_mem hxN⟩
    exact ⟨n', n'.2, congrArg Subtype.val hn'⟩
  have hn'Z : ∀ a : Y, a * n' = n' * a := Subgroup.mem_center_iff.mp (hNc hn'N)
  set g : Y := x * n' with hg
  have hgm : g ^ m = 1 := by
    rw [hg, (show Commute x n' from hn'Z x).mul_pow, hn', mul_inv_cancel]
  have hgx : QuotientGroup.mk' N g = QuotientGroup.mk' N x := by
    have h1 : QuotientGroup.mk' N n' = 1 := (QuotientGroup.eq_one_iff n').mpr hn'N
    rw [hg, map_mul, h1, mul_one]
  have hcomm : QuotientGroup.mk' N (g * t * g⁻¹) = QuotientGroup.mk' N t := by
    rw [map_mul, map_mul, map_inv, hgx, Subgroup.mem_centralizer_singleton_iff.mp hx]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcomm
  have hnN : t⁻¹ * (g * t * g⁻¹) ∈ N := by
    have := N.inv_mem hcomm
    rwa [show ((g * t * g⁻¹)⁻¹ * t)⁻¹ = t⁻¹ * (g * t * g⁻¹) by group] at this
  set n : Y := t⁻¹ * (g * t * g⁻¹) with hnd
  have hnZ : ∀ a : Y, a * n = n * a := Subgroup.mem_center_iff.mp (hNc hnN)
  have hgtn : g * t * g⁻¹ = t * n := by rw [hnd]; group
  have hpow := pow_conj_central hnZ hgtn m
  rw [hgm, one_mul, inv_one, mul_one] at hpow
  have hnm : n ^ m = 1 := mul_left_cancel (a := t) (by rw [mul_one]; exact hpow.symm)
  have hn1 : n = 1 := eq_one_of_pow_odd hm
    (hN2.to_le (Subgroup.zpowers_le.mpr hnN)) hnm
  refine ⟨g, ?_, hgm, hgx⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [hn1, mul_one] at hgtn
  calc g * t = (g * t * g⁻¹) * g := by group
    _ = t * g := by rw [hgtn]

theorem oddCoreImg_centralizer_le (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N) :
    oddCoreImg (Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N))) ≤
      oddCoreImg ((Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N)) := by
  have hC1Cb : (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hg]
  have hodd : Odd (Nat.card (oddCoreImg
      (Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N))))) :=
    odd_natCard_oddCoreImg _
  have hle : oddCoreImg (Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N))) ≤
      (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) := by
    intro u hu
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N u
    have hpow : (QuotientGroup.mk' N x) ^ Nat.card (oddCoreImg
        (Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)))) = 1 := by
      have := pow_card_eq_one' (G := ↥(oddCoreImg
        (Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N))))) (x := ⟨_, hu⟩)
      exact congrArg Subtype.val this
    obtain ⟨g, hgC, -, hgx⟩ := exists_lift_centralizer (t := t) hNc hN2 hodd
      (oddCoreImg_le _ hu) hpow
    exact ⟨g, hgC, hgx⟩
  exact TC.le_oddCoreImg_of_normalizes hle
    (fun e he n hn => conj_mem_oddCoreImg (Subgroup.le_normalizer (hC1Cb he)) hn) hodd

theorem good_of_partial (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N)
    (h : ∃ (xb : Y ⧸ N) (k : ℕ),
      xb ∈ Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) ∧
      xb ∈ (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) ∧ xb ^ 3 ^ k = 1 ∧
      (∃ rb ∈ R.map (QuotientGroup.mk' N),
        ⁅xb, rb⁆ ∉ oddCoreImg (R.map (QuotientGroup.mk' N))) ∧
      ∀ c ∈ Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)),
        c ∈ (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) →
        (∀ rb ∈ R.map (QuotientGroup.mk' N),
          ⁅c, rb⁆ ∈ oddCoreImg (R.map (QuotientGroup.mk' N))) →
        ⁅xb, c⁆ ∈ oddCoreImg (Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) ⊓
          (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N))) :
    GoodThreeElement R t := by
  classical
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  obtain ⟨xb, k, hxbC, -, hxb3, ⟨rb, hrb, hxr⟩, hD⟩ := h
  obtain ⟨x0, rfl⟩ := QuotientGroup.mk'_surjective N xb
  have hmo : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨x', hx'C, hx'3, hmk⟩ := exists_lift_centralizer (t := t) hNc hN2 hmo hxbC hxb3
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hC1Cb : C.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hg]
  refine ⟨x', k, hx'C, hx'3, ?_, ?_⟩
  · obtain ⟨r, hr, rfl⟩ := hrb
    refine ⟨r, hr, fun hmem => hxr ?_⟩
    have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hmem
    rwa [TwistQ.oddCoreImg_map hRN, map_commutatorElement, hmk] at h1
  · intro y hyC hyR
    have hyb : QuotientGroup.mk' N y ∈
        Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp hyC]
    have hyRb : ∀ rb ∈ R.map (QuotientGroup.mk' N),
        ⁅QuotientGroup.mk' N y, rb⁆ ∈ oddCoreImg (R.map (QuotientGroup.mk' N)) := by
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_commutatorElement, ← TwistQ.oddCoreImg_map hRN]
      exact Subgroup.mem_map_of_mem _ (hyR r hr)
    have hw := hD _ hyb (Subgroup.mem_map_of_mem _ hyC) hyRb
    rw [← hmk, ← map_commutatorElement, inf_eq_right.mpr hC1Cb] at hw
    have hwC : ⁅x', y⁆ ∈ C := by
      rw [commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem hx'C hyC) (C.inv_mem hx'C)) (C.inv_mem hyC)
    set f := (QuotientGroup.mk' N).subgroupMap C with hf
    have hfs : Function.Surjective f := (QuotientGroup.mk' N).subgroupMap_surjective C
    have hker : f.ker = N.subgroupOf C := by
      ext c
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
      · intro h1
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h1)
    have hkc : f.ker ≤ Subgroup.center ↥C := by
      rw [hker]
      intro c hc
      rw [Subgroup.mem_center_iff]
      intro d
      exact Subtype.ext ((Subgroup.mem_center_iff.mp (hNc (Subgroup.mem_subgroupOf.mp hc))) d)
    have hk2 : IsPGroup 2 ↥f.ker := by
      rw [hker]
      exact hN2.comap_subtype
    have hle := TwistQ.comap_oddCore_le f hfs hkc hk2
    obtain ⟨u, hu, hwu⟩ := hw
    have hwmem : (⟨⁅x', y⁆, hwC⟩ : ↥C) ∈
        (classicalInvolutionOddCore ↥(C.map (QuotientGroup.mk' N))).comap f := by
      rw [Subgroup.mem_comap]
      have e : f ⟨_, hwC⟩ = u := Subtype.ext hwu.symm
      rw [e]
      exact hu
    have hw2 := hle hwmem
    rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at hw2
    obtain ⟨o, ho, z, hz, hoz⟩ := hw2
    have hzN : (z : Y) ∈ N := by
      rw [hker] at hz
      exact Subgroup.mem_subgroupOf.mp hz
    have hoz' : x' * y * x'⁻¹ * y⁻¹ = (o : Y) * (z : Y) := by
      rw [← commutatorElement_def]
      exact (congrArg Subtype.val hoz).symm
    have hoO : (o : Y) ∈ oddCoreImg C := ⟨o, ho, rfl⟩
    have hxO : ∀ u ∈ oddCoreImg C, x' * u * x'⁻¹ ∈ oddCoreImg C := fun u hu =>
      conj_mem_oddCoreImg (Subgroup.le_normalizer hx'C) hu
    have hz1 : (z : Y) = 1 := TwistQ.eq_one_of_comm (odd_natCard_oddCoreImg C) hxO hx'3 hoO
      (Subgroup.mem_center_iff.mp (hNc hzN)) (hN2.to_le (Subgroup.zpowers_le.mpr hzN)) hoz'
    rw [commutatorElement_def, hoz', hz1, mul_one]
    exact hoO

theorem good_of_twin (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N)
    (htN : t ∉ N)
    (h : GoodThreeElement (R.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N t)) :
    GoodThreeElement R t := by
  classical
  obtain ⟨xb, k, hxbC, hxb3, hnt, hD⟩ := h
  obtain ⟨x0, rfl⟩ := QuotientGroup.mk'_surjective N xb
  have hmo : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨g, hgC, -, hgx⟩ := exists_lift_centralizer (t := t) hNc hN2 hmo hxbC hxb3
  have hC1Cb : (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hg]
  refine good_of_partial hd hNc hN2 htN ⟨QuotientGroup.mk' N x0, k, hxbC, ?_, hxb3, hnt, ?_⟩
  · rw [← hgx]
    exact Subgroup.mem_map_of_mem _ hgC
  · intro c hcC _ hcR
    rw [inf_eq_right.mpr hC1Cb]
    exact oddCoreImg_centralizer_le (t := t) hNc hN2 (hD c hcC hcR)

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
