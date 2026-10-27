module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.GroupTheory.WielandtProductAux

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem isElemAbelian_of_card_prime {r : ℕ} [Fact r.Prime] {X : Subgroup G}
    (hXcard : Nat.card X = r) : CFSG.Open.IsElemAbelian r X := by
  haveI : IsCyclic X := isCyclic_of_prime_card (p := r) hXcard
  refine ⟨inferInstance, fun x hx => ?_⟩
  have h := pow_card_eq_one' (G := X) (x := ⟨x, hx⟩)
  rw [hXcard] at h
  exact congrArg Subtype.val h

theorem dvd_card_of_one_le_pRank {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (h : 1 ≤ CFSG.Open.pRank p H) : p ∣ Nat.card H := by
  obtain ⟨F, hFH, -, hFcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  have h1 : p ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_pow_self p (by omega)
  exact h1.trans (Subgroup.card_dvd_of_le hFH)

theorem exists_mem_orderOf_eq_of_one_le_pRank {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (h : 1 ≤ CFSG.Open.pRank p H) : ∃ x ∈ H, orderOf x = p := by
  obtain ⟨F, hFH, hFabel, hFcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  have hFbig : 1 < Nat.card F := by
    rw [hFcard]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  haveI : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp hFbig
  obtain ⟨x₀, hx₀⟩ := exists_ne (1 : F)
  refine ⟨(x₀ : G), hFH x₀.2, ?_⟩
  have hx1 : (x₀ : G) ≠ 1 := fun h1 => hx₀ (Subtype.ext h1)
  have hdvd : orderOf (x₀ : G) ∣ p :=
    orderOf_dvd_of_pow_eq_one (hFabel.2 (x₀ : G) x₀.2)
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · exact absurd (orderOf_eq_one_iff.mp h1) hx1
  · exact hp'

theorem isElemAbelian_sup_zpowers_of_commute {r : ℕ} [Fact r.Prime] {X : Subgroup G}
    (hXcard : Nat.card X = r) {v : G} (hvord : orderOf v = r) (hvX : v ∉ X)
    (hcomm : ∀ a ∈ X, a * v = v * a) :
    CFSG.Open.IsElemAbelian r (X ⊔ Subgroup.zpowers v) ∧
      Nat.card (X ⊔ Subgroup.zpowers v : Subgroup G) = r ^ 2 := by
  classical
  have hr := (Fact.out : r.Prime)
  have hvpow : v ^ r = 1 := by
    rw [← hvord]
    exact pow_orderOf_eq_one v
  have hXea : CFSG.Open.IsElemAbelian r X := isElemAbelian_of_card_prime hXcard
  have hWea : CFSG.Open.IsElemAbelian r (Subgroup.zpowers v) :=
    CFSG.Open.isElemAbelian_zpowers hvpow
  have hWcard : Nat.card (Subgroup.zpowers v) = r := by
    rw [Nat.card_zpowers, hvord]
  have hc : ∀ a ∈ X, ∀ b ∈ Subgroup.zpowers v, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hav : Commute a v := hcomm a ha
    exact (hav.zpow_right n).eq
  have hWcent : Subgroup.zpowers v ≤ Subgroup.centralizer (X : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hc a ha b hb
  have hWnorm : Subgroup.zpowers v ≤ Subgroup.normalizer (X : Set G) :=
    hWcent.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hdisj : Disjoint X (Subgroup.zpowers v) := by
    rw [disjoint_iff]
    have hdvd : Nat.card (X ⊓ Subgroup.zpowers v : Subgroup G) ∣ r := by
      have := Subgroup.card_dvd_of_le
        (inf_le_right : X ⊓ Subgroup.zpowers v ≤ Subgroup.zpowers v)
      rwa [hWcard] at this
    rcases (Nat.dvd_prime hr).mp hdvd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : X ⊓ Subgroup.zpowers v = Subgroup.zpowers v :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hWcard, h2])
      have hv : v ∈ X ⊓ Subgroup.zpowers v := by
        rw [heq]
        exact Subgroup.mem_zpowers v
      exact hvX hv.1
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute hXea hWea hc, ?_⟩
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer X
    (Subgroup.zpowers v) hWnorm hdisj, hXcard, hWcard, pow_two]

theorem exists_isElemAbelian_card_sq_of_le_of_card_prime {r : ℕ} [Fact r.Prime]
    {B X : Subgroup G} (hB : IsPGroup r B) (hBr : 2 ≤ CFSG.Open.pRank r B)
    (hXB : X ≤ B) (hXcard : Nat.card X = r) :
    ∃ E : Subgroup G, X ≤ E ∧ E ≤ B ∧ CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2 := by
  classical
  have hr := (Fact.out : r.Prime)
  have hBne : B ≠ ⊥ := by
    rintro rfl
    have h0 : CFSG.Open.pRank r (⊥ : Subgroup G) ≤ 0 := by
      refine CFSG.SectionRank.pRank_le (p := r) (H := ⊥) (k := 0) hr.one_lt ?_
      intro E hE _
      rw [le_bot_iff] at hE
      rw [hE, Subgroup.card_bot]
      simp
    omega
  obtain ⟨z, hzB, hzord, hzcent⟩ :=
    CFSG.GroupTheory.WielandtProduct.exists_orderOf_eq_commute_of_isPGroup hB hBne
  by_cases hzX : z ∈ X
  ·
    have hXeq : X = Subgroup.zpowers z := by
      have hle : Subgroup.zpowers z ≤ X := Subgroup.zpowers_le.mpr hzX
      have hcard : Nat.card X ≤ Nat.card (Subgroup.zpowers z) := by
        rw [Nat.card_zpowers, hzord, hXcard]
      exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
    have hXcentB : X ≤ Subgroup.centralizer (B : Set G) := by
      rw [hXeq]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact ((hzcent b hb).zpow_left n).eq.symm
    obtain ⟨E0, hE0B, hE0ea, hE0card⟩ := CFSG.SectionRank.exists_pRank hr.one_lt B
    have hE0big : r ^ 2 ≤ Nat.card E0 := by
      rw [hE0card]
      exact Nat.pow_le_pow_right hr.pos hBr
    have hXlt : Nat.card X < Nat.card E0 := by
      rw [hXcard]
      calc r = r ^ 1 := (pow_one r).symm
        _ < r ^ 2 := Nat.pow_lt_pow_right hr.one_lt (by omega)
        _ ≤ Nat.card E0 := hE0big
    have hex : ∃ v ∈ E0, v ∉ X := by
      by_contra h
      have hle : E0 ≤ X := by
        intro v hv
        by_contra hvX
        exact h ⟨v, hv, hvX⟩
      have := Subgroup.card_le_of_le hle
      omega
    obtain ⟨v, hvE0, hvX⟩ := hex
    have hvB : v ∈ B := hE0B hvE0
    have hv1 : v ≠ 1 := by
      intro h
      exact hvX (h ▸ X.one_mem)
    have hvpow : v ^ r = 1 := hE0ea.2 v hvE0
    have hvord : orderOf v = r := orderOf_eq_prime hvpow hv1
    have hcomm : ∀ a ∈ X, a * v = v * a := by
      intro a ha
      exact (Subgroup.mem_centralizer_iff.1 (hXcentB ha) v hvB).symm
    obtain ⟨hea, hcard⟩ := isElemAbelian_sup_zpowers_of_commute hXcard hvord hvX hcomm
    exact ⟨X ⊔ Subgroup.zpowers v, le_sup_left,
      sup_le hXB (Subgroup.zpowers_le.mpr hvB), hea, hcard⟩
  · obtain ⟨hea, hcard⟩ := isElemAbelian_sup_zpowers_of_commute hXcard hzord hzX
      (fun a ha => (hzcent a (hXB ha)).symm)
    exact ⟨X ⊔ Subgroup.zpowers z, le_sup_left,
      sup_le hXB (Subgroup.zpowers_le.mpr hzB), hea, hcard⟩

theorem exists_sylow_le_normalizer_of_isPGroup {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {W A : Subgroup G} (hA : IsPGroup p A) (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hW : ¬ p ∣ Nat.card W) :
    ∃ S : Sylow q W, A ≤ Subgroup.normalizer (((S : Subgroup W).map W.subtype : Subgroup G) : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hcard : ¬ p ∣ Nat.card (Sylow q W) := by
    rintro h
    exact hW (h.trans ((default : Sylow q W).card_dvd_index.trans (Subgroup.index_dvd_card _)))
  letI : MulDistribMulAction ↥A ↥W := Subgroup.conjMulDistribMulActionOfLeNormalizer A W hAW
  letI : MulAction ↥A (Sylow q W) := Sylow.pointwiseMulAction
  obtain ⟨S, hS⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q W) hcard
  refine ⟨S, fun a ha => ?_⟩
  have hfix : (⟨a, ha⟩ : ↥A) • (S : Subgroup ↥W) = S := by
    rw [← Sylow.pointwise_smul_def]
    exact congrArg Sylow.toSubgroup (hS ⟨a, ha⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : (⟨a, ha⟩ : ↥A) • s ∈ (S : Subgroup ↥W) :=
      hfix ▸ Subgroup.smul_mem_pointwise_smul s (⟨a, ha⟩ : ↥A) (S : Subgroup ↥W) hs
    exact ⟨(⟨a, ha⟩ : ↥A) • s, hs', rfl⟩
  · rintro ⟨s', hs', hs'x⟩
    rw [← hfix] at hs'
    obtain ⟨s, hs, rfl⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists s' (⟨a, ha⟩ : ↥A) (S : Subgroup ↥W)).1 hs'
    refine ⟨s, hs, ?_⟩
    have h1 : a * (s : G) * a⁻¹ = a * x * a⁻¹ := hs'x
    simpa using h1

end CFSG.GroupTheory
