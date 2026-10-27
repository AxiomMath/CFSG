module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

omit [Finite G] in
theorem le_A_of_l34SuzOddData (hD : L34SuzOddData A V K y) : K ≤ A := by
  rw [hD.K_eq]
  exact (Subgroup.commutator_le_self _).trans inf_le_left

omit [Finite G] in
theorem le_centralizer_of_l34SuzOddData (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) :
    K ≤ centralizer ({u} : Set G) := by
  rw [hD.K_eq]
  refine (Subgroup.commutator_le_self _).trans (inf_le_right.trans ?_)
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 hu)

theorem exists_involution_mem_of_l34SuzOddData (hD : L34SuzOddData A V K y) :
    ∃ v ∈ K, v * v = 1 ∧ v ≠ 1 := by
  have hKA : K ≤ A := le_A_of_l34SuzOddData hD
  have hdvd : Nat.card ↥((K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))) ∣
      Nat.card ↥(K.subgroupOf A) := Subgroup.card_map_dvd _ _
  rw [hD.card_image, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv] at hdvd
  have h2 : 2 ∣ Nat.card K := (by norm_num : 2 ∣ 20160).trans hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (p := 2) h2
  refine ⟨x, x.2, ?_, ?_⟩
  · have h := pow_orderOf_eq_one x
    rw [hx, pow_two] at h
    exact congrArg Subtype.val h
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)

theorem isPerfect_of_l34SuzOddSetting (hS : L34SuzOddSetting A t) : Group.IsPerfect ↥A :=
  hS.standard.1.1

end CFSG.ComponentClassification.GrSLit.L34Sec5S
