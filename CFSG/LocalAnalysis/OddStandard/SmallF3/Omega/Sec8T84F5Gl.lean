module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.HardMathSupport.MathTwE6.ExtraspecialComponents
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped Pointwise

theorem sec8t84_rank_glue {G : Type} [Group G] [Finite G] {O D1 D2 : Subgroup G}
    (hO : Odd (Nat.card O)) (hO1 : O ≤ D1) (hO2 : O ≤ D2) (h12 : D1 ⊓ D2 ≤ O)
    (hsq1 : ∀ x ∈ D1, x * x ∈ O) (hsq2 : ∀ x ∈ D2, x * x ∈ O)
    (hc1 : ∀ x ∈ D1, ∀ y ∈ D1, x * y * x⁻¹ * y⁻¹ ∈ O)
    (hc2 : ∀ x ∈ D2, ∀ y ∈ D2, x * y * x⁻¹ * y⁻¹ ∈ O)
    (hc12 : ∀ x ∈ D1, ∀ y ∈ D2, x * y * x⁻¹ * y⁻¹ ∈ O)
    (hn1 : ∀ x ∈ D1, ∀ o ∈ O, x * o * x⁻¹ ∈ O) (hn2 : ∀ x ∈ D2, ∀ o ∈ O, x * o * x⁻¹ ∈ O)
    (hcard1 : Nat.card D1 = 16 * Nat.card O) (hcard2 : Nat.card D2 = 16 * Nat.card O)
    {s : G} (hs : s ∈ D1 ⊔ D2) (hs2 : s * s = 1) :
    ∃ R : Subgroup G, R ≤ centralizer ({s} : Set G) ∧ IsElemAb2 R 8 := by
  classical
  let M : Subgroup G := D1 ⊔ D2
  have hO1M : O ≤ M := hO1.trans le_sup_left
  have hOD1D2 : D1 ⊓ D2 = O := le_antisymm h12 (le_inf hO1 hO2)
  have hconj12 : ∀ x ∈ D1, ∀ y ∈ D2, x * y * x⁻¹ ∈ D2 := by
    intro x hx y hy
    rw [show x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y by group]
    exact D2.mul_mem (hO2 (hc12 x hx y hy)) hy
  have hconj21 : ∀ x ∈ D2, ∀ y ∈ D1, x * y * x⁻¹ ∈ D1 := by
    intro x hx y hy
    have hc : x * y * x⁻¹ * y⁻¹ ∈ O := by
      have h := O.inv_mem (hc12 y hy x hx)
      rwa [show (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ by group] at h
    rw [show x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y by group]
    exact D1.mul_mem (hO1 hc) hy
  have hD1leN2 : D1 ≤ Subgroup.normalizer (D2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy; exact hconj12 x hx y hy
    · intro hy
      have h := hconj12 x⁻¹ (D1.inv_mem hx) (x * y * x⁻¹) hy
      convert h using 1
      group
  have hD2leN1 : D2 ≤ Subgroup.normalizer (D1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy; exact hconj21 x hx y hy
    · intro hy
      have h := hconj21 x⁻¹ (D2.inv_mem hx) (x * y * x⁻¹) hy
      convert h using 1
      group
  have hMmul : (↑M : Set G) = (D1 : Set G) * (D2 : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left D1 D2 hD2leN1
  have hcardM : Nat.card M = 2 ^ 8 * Nat.card O := by
    have h := CFSG.HardMathSupport.MathTwE6.card_sup_mul_card_inf_of_le_normalizer
      (G := G) (A := D1) (B := D2) hD2leN1
    rw [hOD1D2, hcard1, hcard2] at h
    have h' : Nat.card M * Nat.card O = (2 ^ 8 * Nat.card O) * Nat.card O := by
      rw [h]; ring
    exact Nat.mul_right_cancel Nat.card_pos h'
  have hfacM : (Nat.card M).factorization 2 = 8 := by
    rw [hcardM, Nat.factorization_mul (by norm_num) (Nat.card_pos.ne'),
      Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hO.not_two_dvd_nat, add_zero]
  have hNnorm : (O.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hO1M]
    intro h k hh hk
    have hk' : k ∈ (D1 : Set G) * (D2 : Set G) := by
      have hkM : k ∈ (↑M : Set G) := hk
      rwa [hMmul] at hkM
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hk'
    rw [show (a * b) * h * (a * b)⁻¹ = a * (b * h * b⁻¹) * a⁻¹ by group]
    exact hn1 a ha _ (hn2 b hb h hh)
  let N : Subgroup M := O.subgroupOf M
  haveI : N.Normal := hNnorm
  have hmemN : ∀ z : M, z ∈ N ↔ (z : G) ∈ O := by
    intro z
    change z ∈ O.subgroupOf M ↔ (z : G) ∈ O
    exact Subgroup.mem_subgroupOf
  let D1M : Subgroup M := D1.subgroupOf M
  let D2M : Subgroup M := D2.subgroupOf M
  let q : M →* M ⧸ N := QuotientGroup.mk' N
  let E1 : Subgroup (M ⧸ N) := D1M.map q
  let E2 : Subgroup (M ⧸ N) := D2M.map q
  have hE1 : CFSG.Open.IsElemAbelian 2 E1 := by
    refine CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (CFSG.IsElementaryAbelian.two_of_forall_mul_self ?_ ?_)
    · intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      show q a' * q b' = q b' * q a'
      have hcom : a' * b' * a'⁻¹ * b'⁻¹ ∈ N :=
        (hmemN _).mpr (by
          simpa using hc1 (a' : G) (Subgroup.mem_subgroupOf.mp ha')
            (b' : G) (Subgroup.mem_subgroupOf.mp hb'))
      rw [← map_mul, ← map_mul]
      change (((a' * b' : ↥M) : M ⧸ N)) = (((b' * a' : ↥M) : M ⧸ N))
      rw [QuotientGroup.eq_iff_div_mem]
      simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc] using hcom
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      show q a' * q a' = 1
      rw [← map_mul]
      change (((a' * a' : ↥M) : M ⧸ N)) = 1
      rw [QuotientGroup.eq_one_iff]
      exact (hmemN _).mpr (by
        simpa using hsq1 (a' : G) (Subgroup.mem_subgroupOf.mp ha'))
  have hE2 : CFSG.Open.IsElemAbelian 2 E2 := by
    refine CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (CFSG.IsElementaryAbelian.two_of_forall_mul_self ?_ ?_)
    · intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      show q a' * q b' = q b' * q a'
      have hcom : a' * b' * a'⁻¹ * b'⁻¹ ∈ N :=
        (hmemN _).mpr (by
          simpa using hc2 (a' : G) (Subgroup.mem_subgroupOf.mp ha')
            (b' : G) (Subgroup.mem_subgroupOf.mp hb'))
      rw [← map_mul, ← map_mul]
      change (((a' * b' : ↥M) : M ⧸ N)) = (((b' * a' : ↥M) : M ⧸ N))
      rw [QuotientGroup.eq_iff_div_mem]
      simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc] using hcom
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      show q a' * q a' = 1
      rw [← map_mul]
      change (((a' * a' : ↥M) : M ⧸ N)) = 1
      rw [QuotientGroup.eq_one_iff]
      exact (hmemN _).mpr (by
        simpa using hsq2 (a' : G) (Subgroup.mem_subgroupOf.mp ha'))
  have hcross : ∀ a ∈ E1, ∀ b ∈ E2, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    show q a' * q b' = q b' * q a'
    have hcom : a' * b' * a'⁻¹ * b'⁻¹ ∈ N :=
      (hmemN _).mpr (by
        simpa using hc12 (a' : G) (Subgroup.mem_subgroupOf.mp ha')
          (b' : G) (Subgroup.mem_subgroupOf.mp hb'))
    rw [← map_mul, ← map_mul]
    change (((a' * b' : ↥M) : M ⧸ N)) = (((b' * a' : ↥M) : M ⧸ N))
    rw [QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc] using hcom
  have hQ : CFSG.Open.IsElemAbelian 2 (E1 ⊔ E2) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE1 hE2 hcross
  have hsupM : D1M ⊔ D2M = ⊤ := by
    haveI : (D2.subgroupOf M).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hD1leN2 Subgroup.le_normalizer)
    apply le_antisymm le_top
    intro y _
    rw [Subgroup.mem_sup_of_normal_right]
    have hy : (y : G) ∈ (D1 : Set G) * (D2 : Set G) := by
      have hyM : (y : G) ∈ (↑M : Set G) := y.2
      rwa [hMmul] at hyM
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hy
    refine ⟨⟨a, Subgroup.mem_sup_left ha⟩, Subgroup.mem_subgroupOf.mpr ha,
      ⟨b, Subgroup.mem_sup_right hb⟩, Subgroup.mem_subgroupOf.mpr hb, ?_⟩
    exact Subtype.ext (by simpa using hab)
  have htopQ : E1 ⊔ E2 = ⊤ := by
    have h := Subgroup.map_sup D1M D2M q
    rw [hsupM, Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective N)] at h
    simpa [E1, E2] using h.symm
  have hall : ∀ z : M ⧸ N, z ∈ E1 ⊔ E2 := fun z => by
    rw [htopQ]; exact Subgroup.mem_top z
  have hQcomm : ∀ a b : M ⧸ N, a * b = b * a := fun a b => hQ.comm (hall a) (hall b)
  have hQsq : ∀ a : M ⧸ N, a * a = 1 := by
    intro a
    have := hQ.2 a (hall a)
    rwa [pow_two] at this
  have hsqM : ∀ x ∈ M, x * x ∈ O := by
    intro x hx
    let xm : M := ⟨x, hx⟩
    have h := hQsq (q xm)
    rw [← map_mul] at h
    change (((xm * xm : ↥M) : M ⧸ N)) = 1 at h
    rw [QuotientGroup.eq_one_iff] at h
    have h2 : ((xm * xm : ↥M) : G) ∈ O := (hmemN _).mp h
    simpa [xm, pow_two] using h2
  have hcommM : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ O := by
    intro x hx y hy
    let xm : M := ⟨x, hx⟩
    let ym : M := ⟨y, hy⟩
    have h1 : q xm * q ym = q ym * q xm := hQcomm (q xm) (q ym)
    have h : q (xm * ym * xm⁻¹ * ym⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    change (((xm * ym * xm⁻¹ * ym⁻¹ : ↥M) : M ⧸ N)) = 1 at h
    rw [QuotientGroup.eq_one_iff] at h
    have h2 : ((xm * ym * xm⁻¹ * ym⁻¹ : ↥M) : G) ∈ O := (hmemN _).mp h
    simpa [xm, ym] using h2
  have hsM : s ∈ M := hs
  let sm : M := ⟨s, hsM⟩
  have hsP : IsPGroup 2 (Subgroup.zpowers sm) := by
    have horder : orderOf sm ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact Subtype.ext (by simpa [sm, pow_two] using hs2)
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rwa [Nat.card_zpowers, pow_one]
  obtain ⟨Qsyl, hsQsyl⟩ := hsP.exists_le_sylow
  let R : Subgroup G := (Qsyl : Subgroup M).map M.subtype
  have hRle : R ≤ M := Subgroup.map_subtype_le (H := M) (Qsyl : Subgroup M)
  have hcardR : Nat.card R = 2 ^ 8 := by
    have hmap : Nat.card R = Nat.card (Qsyl : Subgroup M) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (Qsyl : Subgroup M) M.subtype
        M.subtype_injective).toEquiv).symm
    rw [hmap, Qsyl.card_eq_multiplicity, hfacM]
  have hsR : s ∈ R := ⟨sm, hsQsyl (Subgroup.mem_zpowers sm), rfl⟩
  have hcop : (Nat.card R).Coprime (Nat.card O) := by
    rw [hcardR, Nat.coprime_pow_left_iff (by norm_num : 0 < 8)]
    exact Nat.prime_two.coprime_iff_not_dvd.mpr hO.not_two_dvd_nat
  have hRinf : R ⊓ O = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hRsq : ∀ x ∈ R, x * x = 1 := by
    intro x hx
    have hxO : x * x ∈ O := hsqM x (hRle hx)
    have hxR : x * x ∈ R := R.mul_mem hx hx
    have h := hRinf ▸ (show x * x ∈ R ⊓ O from ⟨hxR, hxO⟩)
    simpa using h
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    have hcO : x * y * x⁻¹ * y⁻¹ ∈ O := hcommM x (hRle hx) y (hRle hy)
    have hcR : x * y * x⁻¹ * y⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy)
    have hc1 : x * y * x⁻¹ * y⁻¹ = 1 := by
      have h := hRinf ▸ (show x * y * x⁻¹ * y⁻¹ ∈ R ⊓ O from ⟨hcR, hcO⟩)
      simpa using h
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = 1 * (y * x) := by rw [hc1]
      _ = y * x := one_mul _
  have hRelem : CFSG.Open.IsElemAbelian 2 R :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (CFSG.IsElementaryAbelian.two_of_forall_mul_self hRcomm hRsq)
  have hRab : IsElemAb2 R 8 := ⟨hRelem, hcardR⟩
  have hcent : R ≤ centralizer ({s} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hRcomm x hx s hsR
  exact ⟨R, hcent, hRab⟩

end CFSG.OddStandard.SmallF3.Omega
