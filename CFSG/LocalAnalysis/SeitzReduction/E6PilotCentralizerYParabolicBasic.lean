module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYLeviBasic

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open scoped Pointwise

local instance e6CentralizerYParabolicBasicNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def yHigh : List (Fin Tag.E6.rank → ℤ) :=
  [![1, 1, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]]

@[expose] def yU5 : List (Fin Tag.E6.rank → ℤ) := yAlphaAS :: yBetaAS :: yHigh

theorem yConj_check :
    ∀ δ ∈ rootFinset .E6, 0 < height δ →
      (yAlphaAS + δ ∈ rootFinset .E6 → yAlphaAS + δ ∈ yHigh) ∧
      (yBetaAS + δ ∈ rootFinset .E6 → yBetaAS + δ ∈ yHigh) := by
  decide +kernel

theorem yU5_check :
    (∀ ζ ∈ yU5, ζ ∈ rootFinset .E6 ∧ 0 < height ζ ∧ iform ζ yLamAS = 2) ∧ yU5.Nodup ∧
    (∀ ζ ∈ yU5, ∀ ζ' ∈ yU5, 0 ≤ iform ζ ζ') ∧
    (∀ γ ∈ rootFinset .E6, (0 < height γ ∧ (γ 0 ≠ 0 ∨ γ 5 ≠ 0) ∧ 9 ≤ height γ) ↔ γ ∈ yHigh) ∧
    (∀ a ∈ yU5, ∀ b ∈ yU5, iform a b = 0 →
      (a = yAlphaAS ∧ b = yBetaAS) ∨ (a = yBetaAS ∧ b = yAlphaAS)) ∧
    (∀ γ ∈ rootFinset .E6, iform γ yLamAS ≤ 2) := by
  decide +kernel

theorem mem_yU5_of_mem_yHigh {ζ : Fin Tag.E6.rank → ℤ} (h : ζ ∈ yHigh) : ζ ∈ yU5 :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

section High

variable (K : Type) [Field K]

@[expose] noncomputable def yHighSpan : Subgroup (ModGL .E6 K) :=
  rootSpan .E6 K {ζ | ζ ∈ yHigh}

variable {K}

theorem yHigh_eq_parabolicRadicalRootsGe :
    {ζ | ζ ∈ yHigh} = parabolicRadicalRootsGe .E6 nodes16 9 := by
  ext γ
  simp only [parabolicRadicalRootsGe, parabolicRadicalRoots_nodes16, Set.mem_ofPred_eq]
  constructor
  · intro h
    obtain ⟨hr, hpos, hlev⟩ := yU5_check.1 γ (mem_yU5_of_mem_yHigh h)
    refine ⟨⟨mem_rootFinset.1 hr, by omega⟩, ?_⟩
    exact ((yU5_check.2.2.2.1 γ hr).2 h).2.2
  · rintro ⟨⟨hr, hlev⟩, hh⟩
    refine (yU5_check.2.2.2.1 γ (mem_rootFinset.2 hr)).1 ⟨?_, ?_, hh⟩
    · exact ((yLamAS_check.1 γ (mem_rootFinset.2 hr)).2.1.1 hlev).1
    · have h1 := ((yLamAS_check.1 γ (mem_rootFinset.2 hr)).2.1.1 hlev).2
      by_contra hc
      push Not at hc
      exact h1 hc

theorem yHighSpan_eq : yHighSpan K = parabolicRadicalGe .E6 K nodes16 9 := by
  rw [yHighSpan, yHigh_eq_parabolicRadicalRootsGe]
  rfl


theorem borelGroup_le_normalizer_yHighSpan :
    borelGroup .E6 K ≤ normalizer (yHighSpan K : Set (ModGL .E6 K)) := by
  rw [yHighSpan_eq]
  exact (parabolic_root_radical_Levi_factors .E6 K nodes16).2.2.1 9


theorem commute_of_mem_yHighSpan {h : ModGL .E6 K} (hh : h ∈ yHighSpan K)
    {ζ : Fin Tag.E6.rank → ℤ} (hζ : ζ ∈ yU5) (c : K) : Commute h (pinnedX .E6 K ζ c) := by
  have hle : yHighSpan K ≤ centralizer ({pinnedX .E6 K ζ c} : Set (ModGL .E6 K)) := by
    refine iSup₂_le fun ξ hξ => (closure_le _).2 ?_
    rintro _ ⟨d, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have hξ' : ξ ∈ yU5 := mem_yU5_of_mem_yHigh hξ
    exact (classD4_commute_pinnedX e6_simplyLaced (mem_rootFinset.1 (yU5_check.1 ξ hξ').1)
      (mem_rootFinset.1 (yU5_check.1 ζ hζ).1) (yU5_check.2.2.1 ξ hξ' ζ hζ) d c).eq
  exact mem_centralizer_singleton_iff.1 (hle hh)

end High

theorem coe_e6ASRep_one_eq {K : Type} [Field K] :
    (e6ASRep K 1 : ModGL .E6 K) = pinnedX .E6 K yAlphaAS 1 * pinnedX .E6 K yBetaAS 1 := by
  simp [e6ASRep, yGenCheck.2.2.2.2]

section Borel

variable {K : Type} [Field K]


theorem conj_pinnedX_mem_of_pos [CharP K 2] {ζ : Fin Tag.E6.rank → ℤ}
    (hζ : ζ = yAlphaAS ∨ ζ = yBetaAS) {δ : Fin Tag.E6.rank → ℤ} (hδ : IsRoot .E6 δ)
    (hpos : 0 < height δ) (s l : K) :
    (pinnedX .E6 K ζ l)⁻¹ * (pinnedX .E6 K δ s * pinnedX .E6 K ζ l * (pinnedX .E6 K δ s)⁻¹) ∈
      yHighSpan K := by
  have hζ5 : ζ ∈ yU5 := by rcases hζ with rfl | rfl <;> simp [yU5]
  obtain ⟨hζr, hζpos, -⟩ := yU5_check.1 ζ hζ5
  have hζr' := mem_rootFinset.1 hζr
  by_cases hδζ : δ = ζ
  · subst hδζ
    rw [show pinnedX .E6 K δ s * pinnedX .E6 K δ l = pinnedX .E6 K δ l * pinnedX .E6 K δ s by
      rw [← pinnedX_add, ← pinnedX_add, add_comm], mul_inv_cancel_right, inv_mul_cancel]
    exact one_mem _
  by_cases hr : IsRoot .E6 (δ + ζ)
  · have hmem : δ + ζ ∈ yHigh := by
      rcases hζ with rfl | rfl
      · rw [add_comm]
        exact (yConj_check δ (mem_rootFinset.2 hδ) hpos).1 (by
          rw [add_comm]; exact mem_rootFinset.2 hr)
      · rw [add_comm]
        exact (yConj_check δ (mem_rootFinset.2 hδ) hpos).2 (by
          rw [add_comm]; exact mem_rootFinset.2 hr)
    obtain ⟨hε, hcomm⟩ := (simply_laced_root_commutator_unit.{0} Tag.E6 (Or.inr (Or.inl rfl)) hδ
      hζr' hδζ (fun e => hr.ne_zero (by rw [e, neg_add_cancel]))).1 hr
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hε1 : (commConst Tag.E6 δ ζ (1, 1) : K) = 1 := by
      rcases hε with h | h
      · rw [h, Int.cast_one]
      · rw [h, Int.cast_neg, Int.cast_one]
        linear_combination -h2
    have hc := hcomm K s l
    rw [hε1, one_mul, commutatorElement_def] at hc
    have e : pinnedX .E6 K δ s * pinnedX .E6 K ζ l * (pinnedX .E6 K δ s)⁻¹ =
        pinnedX .E6 K (δ + ζ) (s * l) * pinnedX .E6 K ζ l := by
      rw [← hc]; group
    have hX : pinnedX .E6 K (δ + ζ) (s * l) ∈ yHighSpan K :=
      pinnedX_mem_rootSpan (S := {ξ | ξ ∈ yHigh}) hmem (s * l)
    rw [e, (commute_of_mem_yHighSpan hX hζ5 l).eq, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hX
  · have hc := (simply_laced_root_commutator_unit.{0} Tag.E6 (Or.inr (Or.inl rfl)) hδ hζr'
      hδζ (fun e => by
        have h1 : 0 < height (-ζ) := by rw [← e]; exact hpos
        rw [height_neg] at h1
        omega)).2 hr K _ (mem_rootSubgroup.2 ⟨s, rfl⟩) _ (mem_rootSubgroup.2 ⟨l, rfl⟩)
    rw [hc.eq, mul_inv_cancel_right, inv_mul_cancel]
    exact one_mem _

theorem conj_pinnedX_mem_of_mem_posUnipotent [CharP K 2] {ζ : Fin Tag.E6.rank → ℤ}
    (hζ : ζ = yAlphaAS ∨ ζ = yBetaAS) {u : ModGL .E6 K} (hu : u ∈ posUnipotent .E6 K) (l : K) :
    (pinnedX .E6 K ζ l)⁻¹ * (u * pinnedX .E6 K ζ l * u⁻¹) ∈ yHighSpan K := by
  have hB : posUnipotent .E6 K ≤ normalizer (yHighSpan K : Set (ModGL .E6 K)) :=
    le_sup_right.trans borelGroup_le_normalizer_yHighSpan
  rw [posUnipotent, rootSpan_eq_closure] at hu
  induction hu using Subgroup.closure_induction generalizing l with
  | mem x hx =>
    obtain ⟨δ, ⟨hδ, hpos⟩, s, rfl⟩ := hx
    exact conj_pinnedX_mem_of_pos hζ hδ hpos s l
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxN : x ∈ normalizer (yHighSpan K : Set (ModGL .E6 K)) := hB (by
      rw [posUnipotent, rootSpan_eq_closure]; exact hx)
    have e : (pinnedX .E6 K ζ l)⁻¹ * (x * y * pinnedX .E6 K ζ l * (x * y)⁻¹) =
        ((pinnedX .E6 K ζ l)⁻¹ * (x * pinnedX .E6 K ζ l * x⁻¹)) *
          (x * ((pinnedX .E6 K ζ l)⁻¹ * (y * pinnedX .E6 K ζ l * y⁻¹)) * x⁻¹) := by group
    rw [e]
    exact mul_mem (ihx l) ((mem_normalizer_iff.1 hxN _).1 (ihy l))
  | inv x hx ihx =>
    have hxN : x ∈ normalizer (yHighSpan K : Set (ModGL .E6 K)) := hB (by
      rw [posUnipotent, rootSpan_eq_closure]; exact hx)
    have e : (pinnedX .E6 K ζ l)⁻¹ * (x⁻¹ * pinnedX .E6 K ζ l * x⁻¹⁻¹) =
        x⁻¹ * ((pinnedX .E6 K ζ l)⁻¹ * (x * pinnedX .E6 K ζ l * x⁻¹))⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem hxN) _).1 (inv_mem (ihx l))

theorem exists_conj_e6ASRep_one_of_mem_borelGroup [CharP K 2] {b : ModGL .E6 K}
    (hb : b ∈ borelGroup .E6 K) :
    ∃ l m : K, l ≠ 0 ∧ m ≠ 0 ∧ ∃ h ∈ yHighSpan K,
      b * (e6ASRep K 1 : ModGL .E6 K) * b⁻¹ =
        pinnedX .E6 K yAlphaAS l * pinnedX .E6 K yBetaAS m * h := by
  have hb' : b ∈ (torusGroup .E6 K : Set (ModGL .E6 K)) *
      (posUnipotent .E6 K : Set (ModGL .E6 K)) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ torusGroup_le_normalizer_posUnipotent]
    exact hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb'
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hα5 : yAlphaAS ∈ yU5 := by simp [yU5]
  have hβ5 : yBetaAS ∈ yU5 := by simp [yU5]
  have hαr := mem_rootFinset.1 (yU5_check.1 _ hα5).1
  have hβr := mem_rootFinset.1 (yU5_check.1 _ hβ5).1
  have h1 := conj_pinnedX_mem_of_mem_posUnipotent (K := K) (Or.inl rfl) hu 1
  have h2 := conj_pinnedX_mem_of_mem_posUnipotent (K := K) (Or.inr rfl) hu 1
  set h₁ := (pinnedX .E6 K yAlphaAS 1)⁻¹ * (u * pinnedX .E6 K yAlphaAS 1 * u⁻¹) with hh₁
  set h₂ := (pinnedX .E6 K yBetaAS 1)⁻¹ * (u * pinnedX .E6 K yBetaAS 1 * u⁻¹) with hh₂
  have hTN : rootDiagUnit .E6 a ∈ normalizer (yHighSpan K : Set (ModGL .E6 K)) :=
    borelGroup_le_normalizer_yHighSpan (mem_sup_left ht)
  refine ⟨(rootChar a yAlphaAS : K), (rootChar a yBetaAS : K), Units.ne_zero _, Units.ne_zero _,
    rootDiagUnit .E6 a * (h₁ * h₂) * (rootDiagUnit .E6 a)⁻¹,
    (mem_normalizer_iff.1 hTN _).1 (mul_mem h1 h2), ?_⟩
  have e1 : u * pinnedX .E6 K yAlphaAS 1 * u⁻¹ = pinnedX .E6 K yAlphaAS 1 * h₁ := by
    rw [hh₁]; group
  have e2 : u * pinnedX .E6 K yBetaAS 1 * u⁻¹ = pinnedX .E6 K yBetaAS 1 * h₂ := by
    rw [hh₂]; group
  have hc : Commute h₁ (pinnedX .E6 K yBetaAS 1) := commute_of_mem_yHighSpan h1 hβ5 1
  have ey : u * (e6ASRep K 1 : ModGL .E6 K) * u⁻¹ =
      pinnedX .E6 K yAlphaAS 1 * pinnedX .E6 K yBetaAS 1 * (h₁ * h₂) := by
    rw [coe_e6ASRep_one_eq]
    calc u * (pinnedX .E6 K yAlphaAS 1 * pinnedX .E6 K yBetaAS 1) * u⁻¹
        = (u * pinnedX .E6 K yAlphaAS 1 * u⁻¹) * (u * pinnedX .E6 K yBetaAS 1 * u⁻¹) := by group
      _ = pinnedX .E6 K yAlphaAS 1 * (h₁ * pinnedX .E6 K yBetaAS 1) * h₂ := by
          rw [e1, e2]; group
      _ = _ := by rw [hc.eq]; group
  have et := fun ζ (hζ : IsRoot .E6 ζ) => rootDiagUnit_conj_pinnedX (K := K) a hζ (1 : K)
  calc rootDiagUnit .E6 a * u * (e6ASRep K 1 : ModGL .E6 K) * (rootDiagUnit .E6 a * u)⁻¹
      = rootDiagUnit .E6 a * (u * (e6ASRep K 1 : ModGL .E6 K) * u⁻¹) *
          (rootDiagUnit .E6 a)⁻¹ := by group
    _ = (rootDiagUnit .E6 a * pinnedX .E6 K yAlphaAS 1 * (rootDiagUnit .E6 a)⁻¹) *
          (rootDiagUnit .E6 a * pinnedX .E6 K yBetaAS 1 * (rootDiagUnit .E6 a)⁻¹) *
          (rootDiagUnit .E6 a * (h₁ * h₂) * (rootDiagUnit .E6 a)⁻¹) := by rw [ey]; group
    _ = _ := by rw [et _ hαr, et _ hβr, mul_one, mul_one]

end Borel

end CFSG.SeitzReduction.E6Pilot
