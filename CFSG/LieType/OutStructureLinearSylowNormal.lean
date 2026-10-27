module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBULinearUnitaryOuterExtraspecial
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.GorensteinLyons.LinearUnitaryOuter
open CFSG.ClassicalGroups.UnitaryFlag

theorem not_dvd_totient_of_forall_prime_dvd {k p : ℕ} (hp : p.Prime) (hpk : ¬ p ∣ k)
    (hℓ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ k → ¬ p ∣ ℓ - 1) : ¬ p ∣ Nat.totient k := by
  intro h
  rw [Nat.totient_eq_div_primeFactors_mul] at h
  rcases hp.dvd_mul.mp h with h1 | h2
  · exact hpk (h1.trans (Nat.div_dvd_of_dvd (Nat.prod_primeFactors_dvd k)))
  · obtain ⟨ℓ, hℓmem, hpℓ⟩ := (hp.prime.dvd_finsetProd_iff (fun ℓ => ℓ - 1)).mp h2
    exact hℓ ℓ (Nat.prime_of_mem_primeFactors hℓmem) (Nat.dvd_of_mem_primeFactors hℓmem) hpℓ

section Abstract

variable {G : Type*} [Group G] [Finite G]

private def powKer (D : Subgroup G) (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (m : ℕ) :
    Subgroup G where
  carrier := {x | x ∈ D ∧ x ^ m = 1}
  one_mem' := ⟨D.one_mem, one_pow m⟩
  mul_mem' := by
    rintro x y ⟨hxD, hx⟩ ⟨hyD, hy⟩
    refine ⟨D.mul_mem hxD hyD, ?_⟩
    rw [(Commute.mul_pow (hD x hxD y hyD) m), hx, hy, one_mul]
  inv_mem' := by
    rintro x ⟨hxD, hx⟩
    exact ⟨D.inv_mem hxD, by rw [inv_pow, hx, inv_one]⟩

omit [Finite G] in
private theorem powKer_le (D : Subgroup G) (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (m : ℕ) :
    powKer D hD m ≤ D := fun _ hx => hx.1

omit [Finite G] in
private theorem powKer_normal (D : Subgroup G) [D.Normal] (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (m : ℕ) : (powKer D hD m).Normal where
  conj_mem x hx g := by
    refine ⟨‹D.Normal›.conj_mem x hx.1 g, ?_⟩
    rw [conj_pow, hx.2, mul_one, mul_inv_cancel]

theorem sylow_normal_of_normal_cyclic_of_not_dvd_sub_one {p : ℕ} [hp : Fact p.Prime]
    (D : Subgroup G) [hDn : D.Normal] (hDcyc : IsCyclic ↥D)
    (hab : ∀ x y : G ⧸ D, x * y = y * x)
    (hℓ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card D → ¬ p ∣ ℓ - 1) (S : Sylow p G) :
    (S : Subgroup G).Normal := by
  classical
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    let : CommGroup ↥D := IsCyclic.commGroup
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥D) ⟨y, hy⟩)
  set n := Nat.card D with hn
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  set a := n.factorization p
  set m := n / p ^ a with hm
  have hnam : p ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hpm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp.out hn0
  have hcop : Nat.Coprime (p ^ a) m :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm)
  let D' := powKer D hDcomm m
  let Dp := powKer D hDcomm (p ^ a)
  have : D'.Normal := powKer_normal D hDcomm m
  have : Dp.Normal := powKer_normal D hDcomm (p ^ a)
  have hDpg : IsPGroup p Dp := fun x => ⟨a, Subtype.ext (by simpa using x.2.2)⟩
  have hDpS : Dp ≤ S := by
    have h := S.3 (hDpg.to_sup_of_normal_left S.isPGroup') le_sup_right
    rw [← h]
    exact le_sup_left
  have hdec : ∀ d ∈ D, ∃ x ∈ Dp, ∃ y ∈ D', d = x * y := by
    intro d hd
    have hdn : d ^ n = 1 := by
      have h := congrArg Subtype.val (pow_card_eq_one' (G := ↥D) (x := (⟨d, hd⟩ : ↥D)))
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * (m : ℤ) + v * ((p ^ a : ℕ) : ℤ) = 1 := by
      have h := Nat.gcd_eq_gcd_ab m (p ^ a)
      rw [Nat.gcd_comm, hcop.gcd_eq_one] at h
      exact ⟨Nat.gcdA m (p ^ a), Nat.gcdB m (p ^ a), by push_cast at h ⊢; linear_combination -h⟩
    have hdnz : d ^ (n : ℤ) = 1 := by rw [zpow_natCast, hdn]
    refine ⟨d ^ (u * (m : ℤ)), ⟨D.zpow_mem hd _, ?_⟩, d ^ (v * ((p ^ a : ℕ) : ℤ)),
      ⟨D.zpow_mem hd _, ?_⟩, ?_⟩
    · rw [← zpow_natCast, ← zpow_mul, show u * (m : ℤ) * ((p ^ a : ℕ) : ℤ) = (n : ℤ) * u by
        rw [← hnam]; push_cast; ring, zpow_mul, hdnz, one_zpow]
    · rw [← zpow_natCast, ← zpow_mul, show v * ((p ^ a : ℕ) : ℤ) * (m : ℤ) = (n : ℤ) * v by
        rw [← hnam]; push_cast; ring, zpow_mul, hdnz, one_zpow]
    · rw [← zpow_add, huv, zpow_one]
  have : IsCyclic ↥D' := Subgroup.isCyclic_of_le (powKer_le D hDcomm m)
  have hD'exp : ∀ y : ↥D', y ^ m = 1 := fun y => Subtype.ext (by simpa using y.2.2)
  have hD'prime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card D' → ℓ ∣ m := by
    intro ℓ hℓp hℓd
    have : Fact ℓ.Prime := ⟨hℓp⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥D') ℓ hℓd
    rw [← hy]
    exact orderOf_dvd_of_pow_eq_one (hD'exp y)
  have hpD' : ¬ p ∣ Nat.card D' := fun h => hpm (hD'prime p hp.out h)
  have hD'ℓ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card D' → ¬ p ∣ ℓ - 1 := by
    intro ℓ hℓp hℓd
    refine hℓ ℓ hℓp ?_
    rw [← hnam]
    exact (hD'prime ℓ hℓp hℓd).mul_left _
  have hAutD' : ¬ p ∣ Nat.card (MulAut ↥D') := by
    rw [IsCyclic.card_mulAut]
    exact not_dvd_totient_of_forall_prime_dvd hp.out hpD' hD'ℓ
  have hcent : ∀ s ∈ (S : Subgroup G), ∀ y ∈ D', s * y = y * s := by
    let ψ : (S : Subgroup G) →* MulAut ↥D' :=
      (MulAut.conjNormal (H := D')).comp (S : Subgroup G).subtype
    have hψp : IsPGroup p ψ.range :=
      S.isPGroup'.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    have hψbot : ψ.range = ⊥ := by
      obtain ⟨k, hk⟩ := hψp.exists_card_eq
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, pow_zero] at hk
        exact Subgroup.eq_bot_of_card_eq _ hk
      · exfalso
        apply hAutD'
        exact (dvd_pow_self p hkpos.ne').trans (hk ▸ Subgroup.card_subgroup_dvd_card _)
    intro s hs y hy
    have h1 : ψ ⟨s, hs⟩ = 1 := by
      have hmem : ψ ⟨s, hs⟩ ∈ ψ.range := ⟨_, rfl⟩
      rw [hψbot] at hmem
      exact hmem
    have h2 := congrArg (fun f : MulAut ↥D' => ((f ⟨y, hy⟩ : ↥D') : G)) h1
    have h3 : s * y * s⁻¹ = y := by
      simpa [ψ, MulAut.conjNormal_apply] using h2
    calc s * y = (s * y * s⁻¹) * s := by group
      _ = y * s := by rw [h3]
  have hDN : D ≤ Subgroup.normalizer (S : Set G) := by
    intro d hd
    obtain ⟨x, hx, y, hy, rfl⟩ := hdec d hd
    refine Subgroup.mul_mem _ (Subgroup.le_normalizer (hDpS hx)) ?_
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro s hs
    exact hcent s hs y hy
  have hSDn : ((S : Subgroup G) ⊔ D).Normal := by
    let mk : G →* G ⧸ D := QuotientGroup.mk' D
    have hmap' : ((S : Subgroup G) ⊔ D).map mk = (S : Subgroup G).map mk := by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
    have hpre : ((S : Subgroup G).map mk).comap mk = (S : Subgroup G) ⊔ D := by
      rw [← hmap']
      exact Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact le_sup_right)
    rw [← hpre]
    have : IsMulCommutative (G ⧸ D) := IsMulCommutative.of_comm hab
    exact (inferInstance : ((S : Subgroup G).map mk).Normal).comap mk
  have := hSDn
  have hfr := Sylow.normalizer_sup_eq_top' (N := (S : Subgroup G) ⊔ D) S le_sup_left
  have hle : (S : Subgroup G) ⊔ D ≤ Subgroup.normalizer (S : Set G) :=
    sup_le Subgroup.le_normalizer hDN
  have htop : Subgroup.normalizer (S : Set G) = ⊤ := by
    rw [eq_top_iff, ← hfr]
    exact sup_le le_rfl hle
  exact Subgroup.normalizer_eq_top_iff.mp htop

end Abstract

theorem linear_outer_sylow_normal_of_not_dvd_sub_one (N : ℕ) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hN : 3 ≤ N)
    (hℓ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.gcd N (Nat.card K - 1) → ¬ p ∣ ℓ - 1) :
    ∀ S : Sylow p (Outer (projectiveSL N K)),
      (S : Subgroup (Outer (projectiveSL N K))).Normal := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨D, hDn, hDcyc, hDcard, hDcomm, -⟩ := linear_outer_filtration (K := K) (n := N) hN
  have : D.Normal := hDn
  intro S
  exact sylow_normal_of_normal_cyclic_of_not_dvd_sub_one D hDcyc hDcomm
    (fun ℓ hℓp hℓd => hℓ ℓ hℓp (hℓd.trans hDcard)) S

theorem unitary_outer_sylow_normal_of_not_dvd_sub_one {p₀ f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p₀ f K) (hN : 3 ≤ N) (hq : ¬(N = 3 ∧ p₀ ^ f = 2)) {p : ℕ}
    (hp : p.Prime)
    (hℓ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.gcd N (p₀ ^ f + 1) → ¬ p ∣ ℓ - 1) :
    ∀ S : Sylow p (Outer (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))),
      (S : Subgroup (Outer (primeFormP h
        ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)))).Normal := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := h.finite
  obtain ⟨D, hDn, hDcyc, hDcard, hDquot⟩ := unitary_outer_filtration h hN hq
  have : D.Normal := hDn
  have hcomm : ∀ x y : Outer (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) ⧸ D,
      x * y = y * x := by
    have := hDquot
    exact fun x y => mul_comm' x y
  intro S
  exact sylow_normal_of_normal_cyclic_of_not_dvd_sub_one D hDcyc hcomm
    (fun ℓ hℓp hℓd => hℓ ℓ hℓp (hℓd.trans hDcard)) S

end CFSG.LieType.OutStructure
