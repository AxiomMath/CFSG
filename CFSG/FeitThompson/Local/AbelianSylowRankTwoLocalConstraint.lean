module

public import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
public import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
public import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
import CFSG.FeitThompson.Local.CoprimePlaneGeneratesSolvableGroup
import CFSG.FeitThompson.Local.FixedFreeComplementsInvariantSections
import CFSG.FeitThompson.Local.PrimeFittingNormalSelfCentralizingAbelian
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.SelfCentralizingAbelianSylowConstraint
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem subgroupCenterTorsionBy_eq_map_torsionBy (Q : Subgroup G) (n : ℕ) :
    subgroupCenterTorsionBy Q n = (torsionBy (center ↥Q) n).map Q.subtype := by
  ext z
  simp only [mem_subgroupCenterTorsionBy, Subgroup.mem_map, mem_torsionBy, coe_subtype]
  constructor
  · rintro ⟨hzQ, hcomm, hzn⟩
    exact ⟨⟨z, hzQ⟩, ⟨mem_center_iff.2 fun x => Subtype.ext (hcomm x x.2),
      Subtype.ext (by simpa using hzn)⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hwn⟩, rfl⟩
    exact ⟨w.2, fun x hx => congrArg Subtype.val (mem_center_iff.1 hw ⟨x, hx⟩),
      by simpa using congrArg Subtype.val hwn⟩

theorem mem_elementaryAbelianRanks_subgroupOf (hp : p.Prime) {A Q : Subgroup G} (hAQ : A ≤ Q)
    {d : ℕ} (h : d ∈ elementaryAbelianRanks p ↥A) :
    d ∈ elementaryAbelianRanks p ↥(A.subgroupOf Q) := by
  obtain ⟨D, hDA, hcomm, hexp, hcard⟩ := (mem_elementaryAbelianRanks_subgroup_iff hp).1 h
  refine (mem_elementaryAbelianRanks_subgroup_iff hp).2
    ⟨D.subgroupOf Q, Subgroup.comap_mono hDA, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.1 hx) _ (Subgroup.mem_subgroupOf.1 hy))
  · intro x hx
    exact Subtype.ext (by simpa using hexp _ (Subgroup.mem_subgroupOf.1 hx))
  · rw [natCard_subgroupOf_of_le (hDA.trans hAQ), hcard]

theorem ne_bot_of_two_mem_elementaryAbelianRanks (hp : p.Prime) {A : Subgroup G}
    (hA : 2 ∈ elementaryAbelianRanks p ↥A) : A ≠ ⊥ := by
  obtain ⟨D, hDA, -, -, hDcard⟩ := (mem_elementaryAbelianRanks_subgroup_iff hp).1 hA
  intro h
  rw [h, le_bot_iff] at hDA
  rw [hDA, Subgroup.card_bot] at hDcard
  exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne' hDcard.symm

theorem exists_controlled_normal_plane_subgroup [Finite G] (hp : p.Prime) (P : Sylow p G)
    {A : Subgroup G} (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A)
    (hA : 2 ∈ elementaryAbelianRanks p ↥A) :
    ∃ B ≤ A, (B.subgroupOf (P : Subgroup G)).Normal ∧ Nat.card ↥B = p ^ 2 ∧
      (∀ x ∈ B, x ^ p = 1) ∧
      (B ≤ subgroupCenterTorsionBy (P : Subgroup G) p ∨
        (Nat.card ↥(subgroupCenterTorsionBy (P : Subgroup G) p) = p ∧
          subgroupCenterTorsionBy (P : Subgroup G) p ≤ B)) := by
  have := Fact.mk hp
  have hAP : A ≤ (P : Subgroup G) := hAself ▸ inf_le_right
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_inf_centralizer_eq hAself
  have hAcomm' : IsMulCommutative ↥(A.subgroupOf (P : Subgroup G)) :=
    isMulCommutative_subgroupOf_of_isMulCommutative hAcomm
  have hAn := hAnormal
  obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
  have hself' : centralizer ((A.subgroupOf (P : Subgroup G) : Subgroup ↥(P : Subgroup G))
      : Set ↥(P : Subgroup G)) = A.subgroupOf (P : Subgroup G) :=
    (centralizer_subgroupOf_eq_iff hAP).2 (by rw [inf_comm]; exact hAself)
  obtain ⟨B', hB'A, hB'normal, hB'card, hB'exp, hB'Z⟩ :=
    exists_controlled_normal_plane' hp ha (A.subgroupOf (P : Subgroup G)) hself'
      (mem_elementaryAbelianRanks_subgroupOf hp hAP hA)
  refine ⟨B'.map (P : Subgroup G).subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hAP]
    exact Subgroup.map_mono hB'A
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (P : Subgroup G).subtype_injective]
    exact hB'normal
  · rw [Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective, hB'card]
  · rintro x ⟨w, hw, rfl⟩
    simpa using congrArg Subtype.val (hB'exp w hw)
  · rw [subgroupCenterTorsionBy_eq_map_torsionBy]
    rcases hB'Z with h | ⟨h1, h2⟩
    · exact Or.inl (Subgroup.map_mono h)
    · exact Or.inr ⟨by rw [Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective, h1],
        Subgroup.map_mono h2⟩

theorem subgroupPrimeSupportCompl_eq_of_isPGroup [Finite G] (hp : p.Prime) {A : Subgroup G}
    (hA : IsPGroup p ↥A) (hAbot : A ≠ ⊥) :
    subgroupPrimeSupportCompl A = {q : ℕ | q.Prime ∧ q ≠ p} := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hAbot (Subgroup.card_eq_one.1 (by simpa using hn))
  have hsupp : subgroupPrimeSupport A = {p} := by
    rw [subgroupPrimeSupport_def, hn, Nat.primeFactors_pow _ hn0, hp.primeFactors]
    simp
  ext q
  simp [mem_subgroupPrimeSupportCompl_iff, hsupp]

theorem isPiSubgroup_setOf_prime_ne_iff [Finite G] (hp : p.Prime) {Y : Subgroup G} :
    IsPiSubgroup {q : ℕ | q.Prime ∧ q ≠ p} Y ↔ ¬ p ∣ Nat.card ↥Y := by
  rw [isPiSubgroup_iff]
  refine ⟨fun h hdvd => (h p (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩)).2 rfl,
    fun h q hq => ⟨Nat.prime_of_mem_primeFactors hq,
      fun hqp => h (hqp ▸ Nat.dvd_of_mem_primeFactors hq)⟩⟩

theorem map_piCore_setOf_prime_ne_eq_pComplCoreIn [Finite G] (X : Subgroup G) :
    (piCore {q : ℕ | q.Prime ∧ q ≠ p} ↥X).map X.subtype = pComplCoreIn p X := by
  rw [pComplCoreIn_eq, pComplCore_eq_piCore]

theorem lt_top_of_normal_selfCentralizing_sylow [Finite G] [IsSimpleGroup G]
    (hGnc : ¬ IsMulCommutative G) (hp : p.Prime) (P : Sylow p G) {A : Subgroup G}
    (hAP : A ≤ (P : Subgroup G)) (hA : 2 ∈ elementaryAbelianRanks p ↥A) : A < ⊤ :=
  lt_top_of_isPGroup hGnc hp (ne_bot_of_two_mem_elementaryAbelianRanks hp hA)
    (P.isPGroup'.to_le hAP)

theorem le_pComplCoreIn_of_normal_selfCentralizing_sylow [Finite G] [IsSimpleGroup G]
    (hGnc : ¬ IsMulCommutative G) (hGodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H) (hp : p.Prime) (P : Sylow p G)
    {A : Subgroup G} (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A)
    (hA : 2 ∈ elementaryAbelianRanks p ↥A) {X : Subgroup G} (hXtop : X ≠ ⊤) (hAX : A ≤ X)
    {Y : Subgroup G} (hYX : Y ≤ X) (hYp : ¬ p ∣ Nat.card ↥Y)
    (hYA : A ≤ normalizer (Y : Set G)) : Y ≤ pComplCoreIn p X := by
  have := Fact.mk hp
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_inf_centralizer_eq hAself
  have hAP : A ≤ (P : Subgroup G) := hAself ▸ inf_le_right
  obtain ⟨B, hBA, hBnormal, hBcard, hBexp, hBZ⟩ :=
    exists_controlled_normal_plane_subgroup hp P hAnormal hAself hA
  have hXsolv : Group.IsSolvable ↥X := hsolv X hXtop
  have hYsolv : Group.IsSolvable ↥Y := by
    have := hXsolv; exact isSolvable_of_le hYX
  have hBN : B ≤ normalizer (Y : Set G) := hBA.trans hYA
  set ρ : ↥B →* MulAut ↥Y := conjOnNormalized Y hBN with hρ
  have hexp : ∀ b : ↥B, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBexp b b.2)
  have htop : ⨆ (b : ↥B) (_ : b ≠ 1), autFixedSubgroup (ρ b) = ⊤ :=
    iSup_autFixedSubgroup_eq_top hp hBcard hexp ρ hYp
  have hgoal : (⊤ : Subgroup ↥Y) ≤ (pComplCoreIn p X).subgroupOf Y := by
    rw [← htop]
    refine iSup₂_le fun b hb => ?_
    set C : Subgroup G := Y ⊓ centralizer ({(b : G)} : Set G) with hC
    have hfix : autFixedSubgroup (ρ b) ≤ C.subgroupOf Y := by
      intro v hv
      have hvb : (b : G) * (v : G) * (b : G)⁻¹ = (v : G) := by
        have := congrArg Subtype.val (mem_autFixedSubgroup.1 hv)
        rwa [hρ, coe_conjOnNormalized_apply] at this
      exact Subgroup.mem_subgroupOf.2 ⟨v.2,
        mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hvb).symm⟩
    refine hfix.trans (Subgroup.comap_mono ?_)
    have hbB : (b : G) ∈ B := b.2
    have hb1 : (b : G) ≠ 1 := fun h => hb (Subtype.ext h)
    have hCz : C ≤ centralizer ({(b : G)} : Set G) := inf_le_right
    have hCY : C ≤ Y := inf_le_left
    have hCX : C ≤ X := hCY.trans hYX
    have hCp : ¬ p ∣ Nat.card ↥C := fun h => hYp (h.trans (Subgroup.card_dvd_of_le hCY))
    have hCA : A ≤ normalizer (C : Set G) := by
      refine le_trans (le_inf hYA ?_) (normalizer_inf_le_normalizer_inf _ _)
      exact le_trans (le_trans (Subgroup.le_centralizer_iff_isMulCommutative.2 hAcomm)
        (Subgroup.centralizer_le (by simpa using hBA hbB)))
        (Subgroup.le_normalizer (H := centralizer ({(b : G)} : Set G)))
    have hCcore : C ≤ pComplCoreIn p (centralizer ({(b : G)} : Set G)) :=
      le_pComplCoreIn_of_mem_controlledPlane hGnc hGodd hsolv hp P hAnormal hAself hBA hBnormal
        hBcard hBZ hbB hb1 hCz hCp hCA
    have hzpowX : (zpowers (b : G) : Subgroup G) ≤ X := by
      rw [Subgroup.zpowers_le]; exact hAX (hBA hbB)
    have hzpow : IsPGroup p ↥(zpowers (b : G)) :=
      P.isPGroup'.to_le (by rw [Subgroup.zpowers_le]; exact hAP (hBA hbB))
    have hcentEq : X ⊓ centralizer ((zpowers (b : G) : Subgroup G) : Set G)
        = X ⊓ centralizer ({(b : G)} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    refine le_trans (le_pComplCoreIn_inf_of_le_pComplCoreIn hp hCX hCz hCcore) ?_
    rw [← hcentEq]
    exact pComplCoreIn_inf_centralizer_le_pComplCoreIn hp hXsolv hzpowX hzpow
  intro y hy
  exact Subgroup.mem_subgroupOf.1 (hgoal (Subgroup.mem_top (⟨y, hy⟩ : ↥Y)))

theorem isConstrained_of_normal_selfCentralizing_sylow [Finite G] [IsSimpleGroup G]
    (hGnc : ¬ IsMulCommutative G) (hGodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable ↥H) (hp : p.Prime) (P : Sylow p G)
    {A : Subgroup G} (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A)
    (hA : 2 ∈ elementaryAbelianRanks p ↥A) : IsConstrained A := by
  have hAP : A ≤ (P : Subgroup G) := hAself ▸ inf_le_right
  have hpi : subgroupPrimeSupportCompl A = {q : ℕ | q.Prime ∧ q ≠ p} :=
    subgroupPrimeSupportCompl_eq_of_isPGroup hp (P.isPGroup'.to_le hAP)
      (ne_bot_of_two_mem_elementaryAbelianRanks hp hA)
  refine isConstrained_iff.2 fun X hXlt hAX Y hYX hYpi hYA => ?_
  rw [hpi, map_piCore_setOf_prime_ne_eq_pComplCoreIn]
  rw [hpi, isPiSubgroup_setOf_prime_ne_iff hp] at hYpi
  exact le_pComplCoreIn_of_normal_selfCentralizing_sylow hGnc hGodd hsolv hp P hAnormal hAself hA
    hXlt.ne hAX hYX hYpi hYA

end

end CFSG.FeitThompson
