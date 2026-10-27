module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem ker_le_center {p : ℕ} {S : Subgroup Ω} (hcore : GLAPPrimeCore p ↥S = ⊥) :
    (chevQuotHom p S).ker ≤ Subgroup.center ↥S := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro s
  have hx' : pQuotHom p S x ∈ Subgroup.center (PQuot p S) := by
    rw [MonoidHom.mem_ker] at hx
    have h : (QuotientGroup.mk' (Subgroup.center (PQuot p S))) (pQuotHom p S x) = 1 := hx
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hc : pQuotHom p S (s * x * s⁻¹ * x⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      Subgroup.mem_center_iff.1 hx' (pQuotHom p S s)]
    group
  have hk : s * x * s⁻¹ * x⁻¹ ∈ (pQuotHom p S).ker := hc
  rw [ker_pQuotHom, hcore, Subgroup.mem_bot] at hk
  calc s * x = s * x * s⁻¹ * x⁻¹ * x * s := by group
    _ = x * s := by rw [hk]; group

theorem exists_involution_fixed {p : ℕ} {S E₁ : Subgroup Ω} (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hne : GLAPLayer p (S ⊓ Subgroup.centralizer (E₁ : Set Ω)) ≠ ⊥) :
    ∃ t : PSimple p S, orderOf t = 2 ∧ ∀ (e : Ω) (he : e ∈ Subgroup.normalizer (S : Set Ω)),
      e ∈ E₁ → chevAut p S ⟨e, he⟩ t = t := by
  classical
  obtain ⟨P, hP⟩ : ∃ P, GLAPComponent p (S ⊓ Subgroup.centralizer (E₁ : Set Ω)) P := by
    by_contra hno
    push Not at hno
    exact hne (sSup_eq_bot.2 fun J hJ => absurd hJ (hno J))
  have hPX : P ≤ S ⊓ Subgroup.centralizer (E₁ : Set Ω) := hP.1
  have hPS : P ≤ S := hPX.trans inf_le_left
  have hperf : ⁅P, P⁆ = P := glaPComponent_perfect hP
  have hPne : P ≠ ⊥ := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hP
  have hP'map : (P.subgroupOf S).map S.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPS
  have hP'perf : ⁅P.subgroupOf S, P.subgroupOf S⁆ = P.subgroupOf S := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_commutator, hP'map, hperf]
  set Q : Subgroup (PSimple p S) := (P.subgroupOf S).map (chevQuotHom p S) with hQ
  have hQperf : ⁅Q, Q⁆ = Q := by rw [hQ, ← Subgroup.map_commutator, hP'perf]
  have hQne : Q ≠ ⊥ := by
    intro hQbot
    have hle : P.subgroupOf S ≤ (chevQuotHom p S).ker := by
      rw [← Subgroup.map_eq_bot_iff]
      exact hQbot
    have hcen : P.subgroupOf S ≤ Subgroup.center ↥S := hle.trans (ker_le_center hcore)
    have hbot : ⁅P.subgroupOf S, P.subgroupOf S⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 (hcen ha) b).symm
    apply hPne
    rw [← hP'map, ← hP'perf, hbot, Subgroup.map_bot]
  have heven : 2 ∣ Nat.card ↥Q := by
    by_contra hodd
    haveI : Group.IsSolvable ↥Q :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd))
    haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQne
    have hQtop : commutator ↥Q = ⊤ := by
      apply Subgroup.map_injective Q.subtype_injective
      rw [map_commutator_eq, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hQperf]
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥Q)).ne hQtop
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 2 heven
  refine ⟨(t : PSimple p S), by rw [Subgroup.orderOf_coe]; exact ht, ?_⟩
  intro e he heE
  obtain ⟨k, hk, hkt⟩ := t.2
  rw [← hkt, chevAut_chevQuotHom]
  have hkE : (k : Ω) ∈ Subgroup.centralizer (E₁ : Set Ω) := (hPX (Subgroup.mem_subgroupOf.1 hk)).2
  have hkfix : k ∈ fixSubgroup (S.normalizerMonoidHom ⟨e, he⟩) := by
    rw [fixSubgroup_normalizerMonoidHom he, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨k.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_iff.1 hkE e heE
    first
    | exact h
    | exact h.symm
  rw [mem_fixSubgroup.1 hkfix]

private theorem card_inf_ker_mul_card_map {M : Type} [Group M] (f : Ω →* M) (H : Subgroup Ω) :
    Nat.card ↥(H ⊓ f.ker) * Nat.card ↥(H.map f) = Nat.card ↥H := by
  have h := Subgroup.card_ker_mul_card_range (f.domRestrict H)
  rw [MonoidHom.domRestrict_range] at h
  have hker : (f.domRestrict H).ker = f.ker.subgroupOf H := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  rw [hker] at h
  have e : Nat.card ↥(f.ker.subgroupOf H) = Nat.card ↥(H ⊓ f.ker) := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← e]
  exact h

theorem card_map_ge_of_inf_ker_le {M : Type} [Group M] {p : ℕ} (hp : 0 < p) (f : Ω →* M)
    {E₁ Z : Subgroup Ω} (hE : Nat.card ↥E₁ = p ^ 3) (hZ : Nat.card ↥Z = p) (hker : E₁ ⊓ f.ker ≤ Z) :
    p ^ 2 ≤ Nat.card ↥(E₁.map f) := by
  have h := card_inf_ker_mul_card_map f E₁
  have h1 : Nat.card ↥(E₁ ⊓ f.ker) ≤ p := hZ ▸ Subgroup.card_le_of_le hker
  have h2 : p ^ 3 ≤ p * Nat.card ↥(E₁.map f) := by
    rw [← hE, ← h]
    exact Nat.mul_le_mul_right _ h1
  have h3 : p * p ^ 2 ≤ p * Nat.card ↥(E₁.map f) := by
    have e3 : p * p ^ 2 = p ^ 3 := by ring
    rw [e3]
    exact h2
  exact Nat.le_of_mul_le_mul_left h3 hp

end CFSG.LocalAnalysis.GLTheoremA.S265F3

end
