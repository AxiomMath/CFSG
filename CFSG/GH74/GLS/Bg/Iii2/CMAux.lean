module

public import CFSG.GH74.GLS.C3.Layer1.St1RigDiag3

public section

namespace CFSG.GH74.GLS.Bg.Iii2.CMEngine

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.TwoThin
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

section Abstract

theorem false_of_perfect_odd {Z : Type} [Group Z] [Finite Z] {D : Subgroup Z} (hperf : ⁅D, D⁆ = D)
    (hne : D ≠ ⊥) (hodd : Odd (Nat.card D)) : False := by
  have hsolv : Group.IsSolvable D := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hne
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial D
  have : Group.IsPerfect D := Subgroup.isPerfect_iff.mpr hperf
  have h2 : commutator D = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [h2] at h1
  exact lt_irrefl _ h1

theorem range_swapDiag_conj' {Z : Type} [Group Z] {L L' : Subgroup Z} {s : Z} (hss : s * s = 1)
    (hAB : ⁅L, conjSub s⁻¹ L⁆ = ⊥) (hL' : L' = conjSub s⁻¹ L)
    (hAB' : ⁅L', conjSub s⁻¹ L'⁆ = ⊥) : (swapDiag hAB').range = (swapDiag hAB).range := by
  subst hL'
  exact range_swapDiag_conj hss hAB hAB'

end Abstract

section Bar

variable {G : Type} [Group G]

theorem mem_normalizer_cmap_self_iff {x : G} {J : Subgroup G} :
    x ∈ normalizer ((cmap x J : Subgroup G) : Set G) ↔ x ∈ normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h j
    have h1 := h (x * j * x⁻¹)
    rw [mem_cmap, mem_cmap] at h1
    have e1 : x⁻¹ * (x * j * x⁻¹) * x = j := by group
    have e2 : x⁻¹ * (x * (x * j * x⁻¹) * x⁻¹) * x = x * j * x⁻¹ := by group
    rw [e1, e2] at h1
    exact h1
  · intro h j
    rw [mem_cmap, mem_cmap]
    have h1 := h (x⁻¹ * j * x)
    have e1 : x * (x⁻¹ * j * x) * x⁻¹ = j := by group
    have e2 : x⁻¹ * (x * j * x⁻¹) * x = j := by group
    rw [e1] at h1
    rw [e2]
    exact h1

theorem bar_cmap {u q : G} (hq : q ∈ centralizer ({u} : Set G)) (X : Subgroup G) :
    bar u (cmap q X) = conjSub (sbar q hq) (bar u X) := by
  ext z
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hm' : q⁻¹ * (m : G) * q ∈ X := mem_cmap.mp (Subgroup.mem_subgroupOf.mp hm)
    have hmY : q⁻¹ * (m : G) * q ∈ centralizer ({u} : Set G) :=
      mul_mem (mul_mem (inv_mem hq) m.2) hq
    refine ⟨barMk _ ⟨q⁻¹ * m * q, hmY⟩, ⟨⟨q⁻¹ * m * q, hmY⟩, Subgroup.mem_subgroupOf.mpr hm', rfl⟩, ?_⟩
    change sbar q hq * barMk _ ⟨q⁻¹ * m * q, hmY⟩ * (sbar q hq)⁻¹ = barMk _ m
    simp only [sbar, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    change q * (q⁻¹ * m * q) * q⁻¹ = m
    group
  · rintro ⟨w, ⟨m, hm, rfl⟩, rfl⟩
    have hm' : (m : G) ∈ X := Subgroup.mem_subgroupOf.mp hm
    refine ⟨⟨q, hq⟩ * m * ⟨q, hq⟩⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      rw [mem_cmap]
      change q⁻¹ * (q * (m : G) * q⁻¹) * q ∈ X
      have : q⁻¹ * (q * (m : G) * q⁻¹) * q = m := by group
      rw [this]
      exact hm'
    · change _ = sbar q hq * barMk _ m * (sbar q hq)⁻¹
      simp only [sbar, ← map_inv, ← map_mul]

variable [Finite G]

theorem odd_card_bar_pPrimeCoreOf (u : G) (K : Subgroup G) :
    Odd (Nat.card (bar u (pPrimeCoreOf 2 K))) := by
  have h1 : Nat.card (bar u (pPrimeCoreOf 2 K)) ∣
      Nat.card ((pPrimeCoreOf 2 K).subgroupOf (centralizer ({u} : Set G))) :=
    Subgroup.card_map_dvd _ _
  have h2 : Nat.card ((pPrimeCoreOf 2 K).subgroupOf (centralizer ({u} : Set G))) ∣
      Nat.card (pPrimeCoreOf 2 K) :=
    Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.subtype_injective _)
  exact (card_pPrimeCoreOf_odd K).of_dvd_nat (h1.trans h2)

theorem lam_le_of_bar_le {x u : G} {K J Λ : Subgroup G} (hΛ : IsLam x u K Λ)
    (hJ : IsPCompIn 2 (centralizer ({u} : Set G)) J) (hle : bar u Λ ≤ bar u J) : Λ ≤ J := by
  have hperf : Group.IsPerfect ↥(Λ.subgroupOf (centralizer ({u} : Set G))) :=
    Subgroup.isPerfect_iff.mpr (lam_perfect_Y hΛ)
  have hJ2 : TwoComponents.IsTwoComponent (J.subgroupOf (centralizer ({u} : Set G))) :=
    (isPCompIn_two_iff.mp hJ).2
  intro a ha
  have haY : a ∈ centralizer ({u} : Set G) := (Subgroup.mem_inf.mp (hΛ.le ha)).2
  have := le_of_perfect_map_le hperf hJ2 hle
    (Subgroup.mem_subgroupOf.mpr ha : (⟨a, haY⟩ : ↥(centralizer ({u} : Set G))) ∈ _)
  exact Subgroup.mem_subgroupOf.mp this

theorem bar_lam_ne_of_ne {x u : G} {K K' Λ Λ' : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hK' : IsPCompIn 2 (centralizer ({x} : Set G)) K')
    (hne : K ≠ K') (hΛ : IsLam x u K Λ) (hΛ' : IsLam x u K' Λ') : bar u Λ ≠ bar u Λ' := by
  intro hD
  have hperf : ⁅bar u Λ, bar u Λ⁆ = bar u Λ := bar_lam_perfect hΛ
  have hne0 : bar u Λ ≠ ⊥ := bar_lam_ne_bot hΛ
  have hcs : K' ≤ cSec K := le_cSec_of_ne hK' hK hne.symm
  have hle : ⁅bar u Λ, bar u Λ'⁆ ≤ bar u (pPrimeCoreOf 2 K) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨m, hm, rfl⟩ := hg₁
    obtain ⟨m', hm', rfl⟩ := hg₂
    have hmK : (m : G) ∈ K := (Subgroup.mem_inf.mp (hΛ.le (Subgroup.mem_subgroupOf.mp hm))).1
    have hm'K' : (m' : G) ∈ K' := (Subgroup.mem_inf.mp (hΛ'.le (Subgroup.mem_subgroupOf.mp hm'))).1
    refine ⟨⁅m, m'⁆, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact (hcs hm'K').2.2 _ hmK
    · simp only [commutatorElement_def, map_mul, map_inv]
  rw [← hD, hperf] at hle
  exact false_of_perfect_odd hperf hne0
    ((odd_card_bar_pPrimeCoreOf u K).of_dvd_nat (Subgroup.card_dvd_of_le hle))

end Bar

section Step

variable {G : Type} [Group G] [Finite G]

structure StepData (x u : G) (hxY : x ∈ centralizer ({u} : Set G)) (K J Λ : Subgroup G) : Prop where
  lam : IsLam x u K Λ
  cases : (x ∈ normalizer (J : Set G) ∧ bar u Λ = bar u J) ∨
    (x ∉ normalizer (J : Set G) ∧ ∃ hAB : ⁅bar u J, conjSub (sbar x hxY)⁻¹ (bar u J)⁆ = ⊥,
      bar u Λ = (swapDiag hAB).range)

theorem exists_stepData {x u : G} {K J : Subgroup G} (hK : IsRigidRankOneComp x K)
    (hlt : PumpUpLT 2 x K u J) (hxY : x ∈ centralizer ({u} : Set G)) :
    ∃ Λ : Subgroup G, StepData x u hxY K J Λ := by
  obtain ⟨e⟩ := hK.1.2 u J (LongPumpUp.single' hlt)
  have hle : hatCard J ≤ hatCard K := (Nat.card_congr e.toEquiv).le
  obtain ⟨Λ, hΛ, -, -, -, -, hcases⟩ := rigid_step hlt hxY hle
  refine ⟨Λ, hΛ, ?_⟩
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, hAB, -, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, hAB, h2⟩

variable {x u : G} {hxY : x ∈ centralizer ({u} : Set G)}

omit [Finite G] in
theorem StepData.bar_eq_of_eq {K K' J Λ Λ' : Subgroup G} (h : StepData x u hxY K J Λ)
    (h' : StepData x u hxY K' J Λ') : bar u Λ = bar u Λ' := by
  rcases h.cases with ⟨hxN, hv⟩ | ⟨hxN, hAB, hD⟩ <;>
    rcases h'.cases with ⟨hxN', hv'⟩ | ⟨hxN', hAB', hD'⟩
  · rw [hv, hv']
  · exact absurd hxN hxN'
  · exact absurd hxN' hxN
  · rw [hD, hD']

theorem StepData.bar_eq_of_cmap (hxo : orderOf x = 2) {K K' J Λ Λ' : Subgroup G}
    (h : StepData x u hxY K J Λ) (hx : x ∉ normalizer (J : Set G))
    (h' : StepData x u hxY K' (cmap x J) Λ') : bar u Λ = bar u Λ' := by
  rcases h.cases with ⟨hxN, -⟩ | ⟨-, hAB, hD⟩
  · exact absurd hxN hx
  rcases h'.cases with ⟨hxN', -⟩ | ⟨-, hAB', hD'⟩
  · exact absurd (mem_normalizer_cmap_self_iff.mp hxN') hx
  · have hss : sbar x hxY * sbar x hxY = 1 := by
      have := pow_orderOf_eq_one (sbar x hxY)
      rwa [orderOf_sbar hxo hxY, sq] at this
    have hsinv : (sbar x hxY)⁻¹ = sbar x hxY := inv_eq_of_mul_eq_one_left hss
    have hL' : bar u (cmap x J) = conjSub (sbar x hxY)⁻¹ (bar u J) := by
      rw [bar_cmap hxY, hsinv]
    rw [hD, hD']
    exact (range_swapDiag_conj' hss hAB hL' hAB').symm

end Step

end CFSG.GH74.GLS.Bg.Iii2.CMEngine
