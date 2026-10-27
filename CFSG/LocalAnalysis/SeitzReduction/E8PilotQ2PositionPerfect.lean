module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionB

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement


section Generic

variable {τ : Tag} {K : Type} [Field K]

theorem eGenRoot_of_nonneg_highNode {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h0 : 0 ≤ α (highNode τ)) : eGenRoot τ α = true := by
  simp only [eGenRoot, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  rcases IsRoot.height_pos_or_neg hα with hp | hn
  · exact Or.inl hp
  · exact Or.inr ⟨hn, le_antisymm ((IsRoot.height_neg_iff hα).1 hn (highNode τ)) h0⟩

variable (τ K) in
@[expose] noncomputable def eGenSpan : Subgroup (ModGL τ K) :=
  closure ((fun γ => pinnedX τ K γ 1) '' {γ | IsRoot τ γ ∧ eGenRoot τ γ = true})

theorem pinnedX_one_mem_eGenSpan {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hg : eGenRoot τ γ = true) : pinnedX τ K γ 1 ∈ eGenSpan τ K :=
  subset_closure ⟨γ, ⟨hγ, hg⟩, rfl⟩

theorem eGenSpan_le_adjointGroup : eGenSpan τ K ≤ adjointGroup τ K := by
  refine (closure_le _).2 ?_
  rintro _ ⟨γ, -, rfl⟩
  exact pinnedX_mem_adjointGroup _ _

theorem commute_pinnedX_one_highRoot_of_eGenRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hg : eGenRoot τ γ = true) :
    pinnedX τ K γ 1 * pinnedX τ K (highRoot τ) 1 = pinnedX τ K (highRoot τ) 1 * pinnedX τ K γ 1 := by
  have hchk := eTwoCheck_eq_true hτ
  by_cases hpos : 0 < height γ
  · exact (commute_pinnedX_highRoot K hγ hpos 1 1).eq
  · have hneg : height γ < 0 := by
      have hg' := hg
      simp only [eGenRoot, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hg'
      rcases hg' with h | ⟨h, -⟩
      · exact absurd h hpos
      · exact h
    obtain ⟨hr, hnr⟩ := (eTwoCheck_sound hchk hγ hg).2 hneg
    have hne : γ ≠ highRoot τ := fun e => by
      rw [e] at hneg
      exact absurd (height_highRoot_pos τ) (not_lt.2 hneg.le)
    exact ((simply_laced_root_commutator_unit.{0} τ (Or.inr hτ) hγ (isRoot_highRoot τ) hne
      hr).2 hnr K _ (mem_rootSubgroup.2 ⟨1, rfl⟩) _ (mem_rootSubgroup.2 ⟨1, rfl⟩)).eq

theorem eGenSpan_le_centralizer (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    eGenSpan τ K ≤ centralizer ({pinnedX τ K (highRoot τ) 1} : Set (ModGL τ K)) := by
  refine (closure_le _).2 ?_
  rintro _ ⟨γ, ⟨hγ, hg⟩, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  exact commute_pinnedX_one_highRoot_of_eGenRoot hτ hγ hg

theorem eGenSpan_le_commutator [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    eGenSpan τ K ≤ ⁅eGenSpan τ K, eGenSpan τ K⁆ := by
  have hchk := eTwoCheck_eq_true hτ
  refine (closure_le _).2 ?_
  rintro _ ⟨γ, ⟨hγ, hg⟩, rfl⟩
  obtain ⟨⟨a, b, ha, hb, hga, hgb, hab, hne, hne'⟩, -⟩ := eTwoCheck_sound hchk hγ hg
  obtain ⟨hε, hc⟩ := (simply_laced_root_commutator_unit.{0} τ (Or.inr hτ) ha hb hne hne').1
    (hab ▸ hγ)
  have e : pinnedX τ K γ 1 = ⁅pinnedX τ K a 1, pinnedX τ K b 1⁆ := by
    rw [hc K 1 1, hab, mul_one, mul_one]
    rcases hε with h | h <;> rw [h] <;> simp [CharTwo.neg_eq]
  show pinnedX τ K γ 1 ∈ ⁅eGenSpan τ K, eGenSpan τ K⁆
  rw [e]
  exact commutator_mem_commutator (pinnedX_one_mem_eGenSpan ha hga)
    (pinnedX_one_mem_eGenSpan hb hgb)

theorem commutator_eGenSpan_eq_self [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ⁅eGenSpan τ K, eGenSpan τ K⁆ = eGenSpan τ K := by
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (eGenSpan_le_commutator hτ)
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem rootSubgroup_le_eGenSpan_two (hK : Nat.card K = 2) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hg : eGenRoot τ α = true) : rootSubgroup τ K α ≤ eGenSpan τ K := by
  refine (closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rcases eq_zero_or_eq_one_of_card_eq_two hK c with rfl | rfl
  · rw [SetLike.mem_coe, pinnedX_zero]
    exact one_mem _
  · exact pinnedX_one_mem_eGenSpan hα hg

theorem centralizer_pinnedX_highRoot_inf_le_eGenSpan (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : Nat.card K = 2) :
    centralizer ({pinnedX τ K (highRoot τ) 1} : Set (ModGL τ K)) ⊓ adjointGroup τ K ≤
      eGenSpan τ K := by
  rw [EPilot.centralizer_pinnedX_highRoot_inf_eq hτ one_ne_zero]
  refine sup_le (iSup₂_le fun α hα => ?_) (iSup₂_le fun α hα => ?_)
  · obtain ⟨hr, hpos⟩ := EPilot.mem_parabolicRadicalRoots_perpNodes.1 hα
    exact rootSubgroup_le_eGenSpan_two hK hr (eGenRoot_of_nonneg_highNode hr hpos.le)
  · obtain ⟨hr, hzero⟩ := EPilot.mem_perpRoots_iff.1 hα
    exact rootSubgroup_le_eGenSpan_two hK hr (eGenRoot_of_nonneg_highNode hr hzero.ge)

theorem centralizer_pinnedX_highRoot_inf_eq_eGenSpan (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : Nat.card K = 2) :
    centralizer ({pinnedX τ K (highRoot τ) 1} : Set (ModGL τ K)) ⊓ adjointGroup τ K =
      eGenSpan τ K :=
  le_antisymm (centralizer_pinnedX_highRoot_inf_le_eGenSpan hτ hK)
    (le_inf (eGenSpan_le_centralizer hτ) eGenSpan_le_adjointGroup)

theorem commutator_centralizer_pinnedElt_highRoot_two [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hK : Nat.card K = 2) :
    ⁅centralizer ({EPilot.pinnedElt τ (highRoot τ) (1 : K)} : Set (adjointGroup τ K)),
        centralizer ({EPilot.pinnedElt τ (highRoot τ) (1 : K)} : Set (adjointGroup τ K))⁆ =
      centralizer ({EPilot.pinnedElt τ (highRoot τ) (1 : K)} : Set (adjointGroup τ K)) := by
  have h : centralizer ({EPilot.pinnedElt τ (highRoot τ) (1 : K)} : Set (adjointGroup τ K)) =
      (eGenSpan τ K).subgroupOf (adjointGroup τ K) := by
    rw [F4Pilot.centralizer_eq_subgroupOf]
    exact congrArg (fun H => H.subgroupOf (adjointGroup τ K))
      (centralizer_pinnedX_highRoot_inf_eq_eGenSpan hτ hK)
  rw [h]
  exact CFSG.SeitzReduction.commutator_subgroupOf_eq_self eGenSpan_le_adjointGroup
    (commutator_eGenSpan_eq_self hτ)

end Generic

section E8


variable {K : Type} [Field K]

theorem commutator_centralizer_pinnedElt_highRoot_E8_of_one_le {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    ⁅centralizer ({EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)} : Set (adjointGroup .E8 K)),
        centralizer ({EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)} :
          Set (adjointGroup .E8 K))⁆ =
      centralizer ({EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)} : Set (adjointGroup .E8 K)) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    exact commutator_centralizer_pinnedElt_highRoot_two (Or.inr (Or.inr rfl)) (by simpa using hK)
  · refine commutator_centralizer_pinnedElt_highRoot_E8 ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h

theorem commutator_centralizer_repXE8_two [CharP K 2] (hK : Nat.card K = 2) :
    ⁅centralizer ({repXE8 K} : Set (adjointGroup .E8 K)),
        centralizer ({repXE8 K} : Set (adjointGroup .E8 K))⁆ =
      centralizer ({repXE8 K} : Set (adjointGroup .E8 K)) := by
  obtain ⟨n, hn⟩ := exists_conj_pinnedElt_highRoot_eq_repXE8 (K := K)
  rw [← hn, ← map_conj_centralizer_singleton, ← map_commutator,
    commutator_centralizer_pinnedElt_highRoot_two (Or.inr (Or.inr rfl)) hK]

theorem commutator_centralizer_repXE8_of_one_le {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    ⁅centralizer ({repXE8 K} : Set (adjointGroup .E8 K)),
        centralizer ({repXE8 K} : Set (adjointGroup .E8 K))⁆ =
      centralizer ({repXE8 K} : Set (adjointGroup .E8 K)) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    exact commutator_centralizer_repXE8_two (by simpa using hK)
  · refine commutator_centralizer_repXE8 ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h

theorem forall_normal_isPGroup_eq_bot_xLeviE8_of_one_le {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (N : Subgroup (xLeviE8 K)) (hN : N.Normal) (hN2 : IsPGroup 2 N) :
    N = ⊥ := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQ, hQM, -, hMN⟩ := isTwoRadicalDecomp_repXE8 (K := K)
  exact EPilot.forall_normal_isPGroup_eq_bot_of_isSimpleGroup_of_perfect hQ hMN
    isSimpleGroup_xLeviE8
    (by rw [hQM]; exact commutator_centralizer_repXE8_of_one_le hf hK) N hN hN2

end E8

end CFSG.SeitzReduction.E8Pilot
