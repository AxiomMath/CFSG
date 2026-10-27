module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
public import CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
public import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
public import CFSG.FeitThompson.Representations.CoprimePrimeAutFixedConjugacyClasses
import CFSG.FeitThompson.Local.InvariantMaximalPrimeSubgroupsConjugate
import CFSG.FeitThompson.Local.RankThreeCoprimePlaneGeneration
import CFSG.FeitThompson.Local.CoprimePlaneGeneratesSolvableGroup
import CFSG.FeitThompson.Foundations.PGroupNilpotent
import CFSG.FeitThompson.Foundations.NonabelianPGroupInvariantCentralDerived
import CFSG.FeitThompson.Local.ConjugationUniqueMaximalOvergroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {d p q : ℕ}

theorem pow_eq_one_of_mem_of_mulEquiv {E : Subgroup G} (hp : p.Prime)
    (e : ↥E ≃* Multiplicative (Fin d → ZMod p)) {x : G} (hx : x ∈ E) : x ^ p = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h : (⟨x, hx⟩ : ↥E) ^ p = 1 := by
    refine e.injective ?_
    rw [map_pow, map_one]
    refine Multiplicative.toAdd.injective ?_
    simp only [toAdd_pow, toAdd_one]
    funext i
    simp
  simpa using congrArg (Subtype.val (p := fun y : G => y ∈ E)) h

theorem natCard_eq_pow_of_mulEquiv {E : Subgroup G}
    (e : ↥E ≃* Multiplicative (Fin d → ZMod p)) : Nat.card ↥E = p ^ d := by
  rw [Nat.card_congr e.toEquiv, natCard_multiplicative_pi_zmod]

private theorem isSolvable_of_isPGroup [Finite G] {Q : Subgroup G} (hq : q.Prime)
    (hQ : IsPGroup q Q) : Group.IsSolvable Q := by
  have := Fact.mk hq
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have := isNilpotent_of_natCard_eq_prime_pow hq hn
  infer_instance

theorem centralizer_singleton_lt_top_of_mem_of_lt_top [IsSimpleGroup G] {A : Subgroup G}
    (hAtop : A < ⊤) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    centralizer ({a} : Set G) < ⊤ := by
  have hzbot : ⊥ < zpowers a := by
    refine bot_lt_iff_ne_bot.2 fun h => ha1 ?_
    simpa [h] using Subgroup.mem_zpowers a
  have hztop : zpowers a < ⊤ := lt_of_le_of_lt (Subgroup.zpowers_le.2 ha) hAtop
  have hcl : centralizer ((zpowers a : Subgroup G) : Set G) = centralizer ({a} : Set G) := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_closure _
  refine lt_of_le_of_lt ?_ (normalizer_lt_top_of_isSimpleGroup hzbot hztop)
  rw [← hcl]
  exact Subgroup.centralizer_le_normalizer _

theorem map_subtype_fixedPoints_conjOnNormalized {Q E : Subgroup G}
    (hEN : E ≤ normalizer (Q : Set G)) (S : Subgroup ↥E) :
    (FixedPoints.subgroup ((conjOnNormalized Q hEN).comp S.subtype).range ↥Q).map Q.subtype
      = Q ⊓ centralizer ((S.map E.subtype : Subgroup G) : Set G) := by
  ext z
  constructor
  · rintro hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    rw [mem_fixedPoints_comp_subtype_iff] at hx
    refine ⟨x.2, mem_centralizer_iff.2 fun g hg => ?_⟩
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hg
    have h := congrArg (Subtype.val (p := fun y : G => y ∈ Q)) (hx b hb)
    rw [conjOnNormalized_apply_coe] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm ▸ rfl
  · rintro ⟨hzQ, hzc⟩
    refine Subgroup.mem_map.2 ⟨⟨z, hzQ⟩, ?_, rfl⟩
    rw [mem_fixedPoints_comp_subtype_iff]
    intro b hb
    refine Subtype.ext ?_
    rw [conjOnNormalized_apply_coe]
    exact mul_inv_eq_iff_eq_mul.2
      (mem_centralizer_iff.1 hzc (b : G) (Subgroup.mem_map_of_mem E.subtype hb))

theorem map_subtype_autFixedSubgroup_conjOnNormalized {Q D : Subgroup G}
    (hDN : D ≤ normalizer (Q : Set G)) (a : ↥D) :
    (autFixedSubgroup (conjOnNormalized Q hDN a)).map Q.subtype
      = Q ⊓ centralizer ({(a : G)} : Set G) := by
  ext z
  constructor
  · rintro hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    have h := congrArg (Subtype.val (p := fun y : G => y ∈ Q)) (mem_autFixedSubgroup.1 hx)
    rw [conjOnNormalized_apply_coe] at h
    refine ⟨x.2, mem_centralizer_iff.2 ?_⟩
    rintro g (rfl : g = (a : G))
    exact (mul_inv_eq_iff_eq_mul.1 h).symm ▸ rfl
  · rintro ⟨hzQ, hzc⟩
    refine Subgroup.mem_map.2 ⟨⟨z, hzQ⟩, mem_autFixedSubgroup.2 (Subtype.ext ?_), rfl⟩
    rw [conjOnNormalized_apply_coe]
    exact mul_inv_eq_iff_eq_mul.2 (mem_centralizer_iff.1 hzc (a : G) rfl)

theorem exists_plane_inf_centralizer_ne_bot [Finite G] {E Q : Subgroup G} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (e : ↥E ≃* Multiplicative (Fin 3 → ZMod p))
    (hQ : IsPGroup q Q) (hQbot : Q ≠ ⊥) (hEN : E ≤ normalizer (Q : Set G)) :
    ∃ D : Subgroup G, D ≤ E ∧ Nat.card D = p ^ 2 ∧
      (Q ⊓ centralizer (D : Set G) : Subgroup G) ≠ ⊥ := by
  have := Fact.mk hq
  have hsolv : Group.IsSolvable ↥Q := isSolvable_of_isPGroup hq hQ
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hcop : p.Coprime (Nat.card ↥Q) := by
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp hq).2 hpq)
  have hsup := iSup_fixedPoints_subgroupsOfCard_eq_top_of_mulEquiv (E := ↥E) (V := ↥Q) hp e
    (conjOnNormalized Q hEN) hcop
  have hnt : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQbot
  have hne : ¬ ∀ (S : Subgroup ↥E) (_ : S ∈ subgroupsOfCard ↥E (p ^ 2)),
      FixedPoints.subgroup ((conjOnNormalized Q hEN).comp S.subtype).range ↥Q = ⊥ := by
    intro h
    rw [← iSup₂_eq_bot] at h
    exact bot_ne_top (h.symm.trans hsup)
  simp only [not_forall] at hne
  obtain ⟨S, hS, hSne⟩ := hne
  refine ⟨S.map E.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact mem_subgroupsOfCard.1 hS
  · rw [← map_subtype_fixedPoints_conjOnNormalized hEN S]
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ Q.subtype_injective]

theorem exists_mem_inf_centralizer_singleton_ne_bot [Finite G] {D Q : Subgroup G} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hDcard : Nat.card D = p ^ 2) (hDexp : ∀ x ∈ D, x ^ p = 1)
    (hQ : IsPGroup q Q) (hQbot : Q ≠ ⊥) (hDN : D ≤ normalizer (Q : Set G)) :
    ∃ a ∈ D, a ≠ 1 ∧ (Q ⊓ centralizer ({a} : Set G) : Subgroup G) ≠ ⊥ := by
  have := Fact.mk hq
  have hsolv : Group.IsSolvable ↥Q := isSolvable_of_isPGroup hq hQ
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hcop : p.Coprime (Nat.card ↥Q) := by
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp hq).2 hpq)
  have hexp : ∀ a : ↥D, a ^ p = 1 := fun a => Subtype.ext (by simpa using hDexp (a : G) a.2)
  have hsup := iSup_autFixedSubgroup_eq_top (A := ↥D) (K := ↥Q) hp hDcard hexp
    (conjOnNormalized Q hDN) ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop)
  have hnt : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQbot
  have hne : ¬ ∀ (a : ↥D) (_ : a ≠ 1), autFixedSubgroup (conjOnNormalized Q hDN a) = ⊥ := by
    intro h
    rw [← iSup₂_eq_bot] at h
    exact bot_ne_top (h.symm.trans hsup)
  simp only [not_forall] at hne
  obtain ⟨a, ha1, hane⟩ := hne
  refine ⟨(a : G), a.2, fun h => ha1 (Subtype.ext h), ?_⟩
  rw [← map_subtype_autFixedSubgroup_conjOnNormalized hDN a]
  rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ Q.subtype_injective]

theorem exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_rank_three_le_centre [Finite G]
    [IsSimpleGroup G] (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    {A E Q₁ Q₂ : Subgroup G} (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A)
    (hq : q.Prime) (hqπ : q ∉ subgroupPrimeSupport A) (hp : p.Prime)
    (hEA : E ≤ A ⊓ centralizer (A : Set G))
    (hE : Nonempty (↥E ≃* Multiplicative (Fin 3 → ZMod p)))
    (hQ₁ : Q₁ ∈ maximalNormalizedPSubgroups A q)
    (hQ₂ : Q₂ ∈ maximalNormalizedPSubgroups A q) :
    ∃ k ∈ constrainedCentralizerCore A, MulAut.conj k⁻¹ • Q₁ = Q₂ := by
  obtain ⟨e⟩ := hE
  by_cases hQ₁bot : Q₁ = ⊥
  · refine ⟨1, one_mem _, ?_⟩
    have h : Q₂ = Q₁ :=
      eq_of_mem_of_le hQ₁ (isPGroup_of_mem hQ₂) (le_normalizer_of_mem hQ₂) (hQ₁bot ▸ bot_le)
    simp [h]
  by_cases hQ₂bot : Q₂ = ⊥
  · refine ⟨1, one_mem _, ?_⟩
    have h : Q₁ = Q₂ :=
      eq_of_mem_of_le hQ₂ (isPGroup_of_mem hQ₁) (le_normalizer_of_mem hQ₁) (hQ₂bot ▸ bot_le)
    simp [h]
  have hEle : E ≤ A := hEA.trans inf_le_left
  have hEc : E ≤ centralizer (A : Set G) := hEA.trans inf_le_right
  have hEcard : Nat.card ↥E = p ^ 3 := natCard_eq_pow_of_mulEquiv e
  have hpπ : p ∈ subgroupPrimeSupport A := by
    refine mem_subgroupPrimeSupport_iff.2 (Nat.mem_primeFactors.2 ⟨hp, ?_, Nat.card_pos.ne'⟩)
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hEle)
    rw [hEcard]
    exact dvd_pow_self p three_ne_zero
  have hpq : p ≠ q := fun h => hqπ (h ▸ hpπ)
  obtain ⟨D, hDE, hDcard, hD1⟩ := exists_plane_inf_centralizer_ne_bot hp hq hpq e
    (isPGroup_of_mem hQ₁) hQ₁bot (hEle.trans (le_normalizer_of_mem hQ₁))
  obtain ⟨a, haD, ha1, hn2⟩ := exists_mem_inf_centralizer_singleton_ne_bot hp hq hpq hDcard
    (fun x hx => pow_eq_one_of_mem_of_mulEquiv hp e (hDE hx)) (isPGroup_of_mem hQ₂) hQ₂bot
    ((hDE.trans hEle).trans (le_normalizer_of_mem hQ₂))
  have hHtop : centralizer ({a} : Set G) < ⊤ :=
    centralizer_singleton_lt_top_of_mem_of_lt_top hAtop (hEle (hDE haD)) ha1
  have hAH : A ≤ centralizer ({a} : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun g hg => by
      cases hg
      exact (mem_centralizer_iff.1 (hEc (hDE haD)) x hx).symm
  have hn1 : (Q₁ ⊓ centralizer ({a} : Set G) : Subgroup G) ≠ ⊥ := fun h =>
    hD1 (le_bot_iff.1 (le_trans (inf_le_inf_left Q₁
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD))) h.le))
  exact exists_mem_constrainedCentralizerCore_conj_inv_smul_eq hsolv hAbot hAtop hcon hq hqπ
    hQ₁ hQ₂ hHtop hAH hn1 hn2

theorem exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_le_map_center [Finite G]
    [IsSimpleGroup G] (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    {A E Q₁ Q₂ : Subgroup G} (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A)
    (hq : q.Prime) (hqπ : q ∉ subgroupPrimeSupport A) (hp : p.Prime)
    (hEA : E ≤ (Subgroup.center ↥A).map A.subtype)
    (hE : Nonempty (↥E ≃* Multiplicative (Fin 3 → ZMod p)))
    (hQ₁ : Q₁ ∈ maximalNormalizedPSubgroups A q)
    (hQ₂ : Q₂ ∈ maximalNormalizedPSubgroups A q) :
    ∃ k ∈ constrainedCentralizerCore A, MulAut.conj k⁻¹ • Q₁ = Q₂ :=
  exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_rank_three_le_centre hsolv hAbot hAtop
    hcon hq hqπ hp (map_subtype_center_eq_inf_centralizer A ▸ hEA) hE hQ₁ hQ₂

theorem exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_rank_three_of_odd [Finite G]
    (_hodd : Odd (Nat.card G)) (hsimple : IsSimpleGroup G) (_hG : ¬ IsMulCommutative G)
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {A Q₁ Q₂ : Subgroup G}
    (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A) (hq : q.Prime)
    (hqπ : q ∉ subgroupPrimeSupport A) (hp : p.Prime)
    (hZ : ∃ E : Subgroup G, E ≤ A ⊓ centralizer (A : Set G) ∧
      Nonempty (↥E ≃* Multiplicative (Fin 3 → ZMod p)))
    (hQ₁ : Q₁ ∈ maximalNormalizedPSubgroups A q)
    (hQ₂ : Q₂ ∈ maximalNormalizedPSubgroups A q) :
    ∃ k ∈ constrainedCentralizerCore A, MulAut.conj k⁻¹ • Q₁ = Q₂ :=
  have := hsimple
  have ⟨_, hEA, hE⟩ := hZ
  exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_rank_three_le_centre hsolv hAbot hAtop
    hcon hq hqπ hp hEA hE hQ₁ hQ₂

theorem exists_mem_constrainedCentralizerCore_forall_mem_iff_of_rank_three_le_centre [Finite G]
    [IsSimpleGroup G] (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    {A E Q₁ Q₂ : Subgroup G} (hAbot : ⊥ < A) (hAtop : A < ⊤) (hcon : IsConstrained A)
    (hq : q.Prime) (hqπ : q ∉ subgroupPrimeSupport A) (hp : p.Prime)
    (hEA : E ≤ A ⊓ centralizer (A : Set G))
    (hE : Nonempty (↥E ≃* Multiplicative (Fin 3 → ZMod p)))
    (hQ₁ : Q₁ ∈ maximalNormalizedPSubgroups A q)
    (hQ₂ : Q₂ ∈ maximalNormalizedPSubgroups A q) :
    ∃ k ∈ constrainedCentralizerCore A, ∀ x : G, x ∈ Q₂ ↔ k * x * k⁻¹ ∈ Q₁ := by
  obtain ⟨k, hk, hkeq⟩ :=
    exists_mem_constrainedCentralizerCore_conj_inv_smul_eq_of_rank_three_le_centre hsolv hAbot
      hAtop hcon hq hqπ hp hEA hE hQ₁ hQ₂
  exact ⟨k, hk, fun x => by rw [← hkeq, mem_conj_inv_smul_iff]⟩

end

end CFSG.FeitThompson
