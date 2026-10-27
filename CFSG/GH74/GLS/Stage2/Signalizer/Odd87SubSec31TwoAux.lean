module

public import CFSG.GH74.GLS.Classes
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.GroupTheory.LocalCores.Components

public section

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Components

variable {X : Type} [Group X]

theorem comp_eq_of_le_quasisimple {K J : Subgroup X} (hK : IsQuasisimple ↥K) (hJ : IsComponent J)
    (hJK : J ≤ K) : J = K := by
  have hJQ : IsComponent (J.subgroupOf K) := CFSG.LocalCores.component_overgroup hJ hJK
  by_cases htop : J.subgroupOf K = ⊤
  · exact le_antisymm hJK (Subgroup.subgroupOf_eq_top.mp htop)
  · exfalso
    obtain ⟨M, hMn, hJM, hMlt⟩ := hJQ.2.lt_normal.resolve_left htop
    have hMc : M ≤ center ↥K :=
      (CFSG.LocalCores.quasisimple_normal_subgroups hK hMn).resolve_left hMlt.ne
    have hle : J.subgroupOf K ≤ centralizer ((J.subgroupOf K : Subgroup ↥K) : Set ↥K) :=
      (hJM.trans hMc).trans (Subgroup.center_le_centralizer _)
    have hcomm : ⁅J.subgroupOf K, J.subgroupOf K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    have hperf : ⁅J.subgroupOf K, J.subgroupOf K⁆ = J.subgroupOf K :=
      Subgroup.isPerfect_iff.mp hJQ.1.1
    have hbot : J.subgroupOf K = ⊥ := hperf.symm.trans hcomm
    have : Nontrivial ↥(J.subgroupOf K) := CFSG.LocalCores.isQuasisimple_nontrivial hJQ.1
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this hbot

theorem comp_eq_of_le_solvable_or_quasisimple {K J J' : Subgroup X}
    (hK : Group.IsSolvable ↥K ∨ IsQuasisimple ↥K) (hJ : IsComponent J) (hJ' : IsComponent J')
    (hJK : J ≤ K) (hJ'K : J' ≤ K) : J = J' := by
  rcases hK with hs | hq
  · exfalso
    have := hs
    have : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJK)
    have : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
    have : Group.IsPerfect ↥J := hJ.1.1
    exact Group.IsPerfect.not_isSolvable ↥J inferInstance
  · exact (comp_eq_of_le_quasisimple hq hJ hJK).trans (comp_eq_of_le_quasisimple hq hJ' hJ'K).symm

theorem le_normalizer_of_commute {A B : Subgroup X} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ normalizer (A : Set X) := fun b hb =>
  (Subgroup.centralizer_le_normalizer (A : Set X))
    (Subgroup.mem_centralizer_iff.mpr fun a ha => h a ha b hb)

variable [Finite X]

theorem comp_le_or_le_of_commute {K₁ K₂ J : Subgroup X} (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hJ : IsComponent J) (hJK : J ≤ K₁ ⊔ K₂) : J ≤ K₁ ∨ J ≤ K₂ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hJM : IsComponent (J.subgroupOf (K₁ ⊔ K₂)) := CFSG.LocalCores.component_overgroup hJ hJK
  have hN₁ : (K₁.subgroupOf (K₁ ⊔ K₂)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer (le_normalizer_of_commute hcomm)
  have hN₂ : (K₂.subgroupOf (K₁ ⊔ K₂)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
    exact sup_le (le_normalizer_of_commute fun a ha b hb => (hcomm b hb a ha).symm)
      Subgroup.le_normalizer
  have hc₁ : ⁅J, K₁⁆ = ⊥ := by
    rcases CFSG.LocalCores.component_normal_subgroup hJM hN₁ with h | h
    · exact absurd (CFSG.LocalCores.le_of_subgroupOf_le hJK h) h1
    · have := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hJK h
      rwa [inf_eq_left.mpr le_sup_left] at this
  have hc₂ : ⁅J, K₂⁆ = ⊥ := by
    rcases CFSG.LocalCores.component_normal_subgroup hJM hN₂ with h | h
    · exact absurd (CFSG.LocalCores.le_of_subgroupOf_le hJK h) h2
    · have := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hJK h
      rwa [inf_eq_left.mpr le_sup_right] at this
  have hK₁ : K₁ ≤ centralizer (J : Set X) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hc₁
  have hK₂ : K₂ ≤ centralizer (J : Set X) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hc₂
  have hJc : ⁅J, J⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hJK.trans (sup_le hK₁ hK₂))
  have hbot : J = ⊥ := (Subgroup.isPerfect_iff.mp hJ.1.1).symm.trans hJc
  have : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this hbot

theorem three_comps_false {K₁ K₂ : Subgroup X} (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (h₁ : Group.IsSolvable ↥K₁ ∨ IsQuasisimple ↥K₁) (h₂ : Group.IsSolvable ↥K₂ ∨ IsQuasisimple ↥K₂)
    {J₁ J₂ J₃ : Subgroup X} (hJ₁ : IsComponent J₁) (hJ₂ : IsComponent J₂) (hJ₃ : IsComponent J₃)
    (hle₁ : J₁ ≤ K₁ ⊔ K₂) (hle₂ : J₂ ≤ K₁ ⊔ K₂) (hle₃ : J₃ ≤ K₁ ⊔ K₂)
    (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃) : False := by
  rcases comp_le_or_le_of_commute hcomm hJ₁ hle₁ with a | a <;>
  rcases comp_le_or_le_of_commute hcomm hJ₂ hle₂ with b | b <;>
  rcases comp_le_or_le_of_commute hcomm hJ₃ hle₃ with c | c
  · exact h12 (comp_eq_of_le_solvable_or_quasisimple h₁ hJ₁ hJ₂ a b)
  · exact h12 (comp_eq_of_le_solvable_or_quasisimple h₁ hJ₁ hJ₂ a b)
  · exact h13 (comp_eq_of_le_solvable_or_quasisimple h₁ hJ₁ hJ₃ a c)
  · exact h23 (comp_eq_of_le_solvable_or_quasisimple h₂ hJ₂ hJ₃ b c)
  · exact h23 (comp_eq_of_le_solvable_or_quasisimple h₁ hJ₂ hJ₃ b c)
  · exact h13 (comp_eq_of_le_solvable_or_quasisimple h₂ hJ₁ hJ₃ a c)
  · exact h12 (comp_eq_of_le_solvable_or_quasisimple h₂ hJ₁ hJ₂ a b)
  · exact h12 (comp_eq_of_le_solvable_or_quasisimple h₂ hJ₁ hJ₂ a b)

end Components

section Involutions

theorem exists_orderOf_eq_two_of_isQuasisimple {J : Type} [Group J] [Finite J] (hJ : IsQuasisimple J) :
    ∃ u : J, orderOf u = 2 := by
  have : Nontrivial J := CFSG.LocalCores.isQuasisimple_nontrivial hJ
  have : Group.IsPerfect J := hJ.1
  have heven : Even (Nat.card J) := by
    by_contra hne
    exact Group.IsPerfect.not_isSolvable J
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hne))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)

end Involutions

section SL2Facts

theorem isQuasisimple_special_linear_two {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    IsQuasisimple SL(2, F) := by
  have h4' : ∃ s : Finset F, s.card = 4 := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by simpa [Finset.card_univ, Nat.card_eq_fintype_card] using h4)
    exact ⟨s, hs⟩
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl (Or.inr h4')
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr h4')
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator SL(2, F) ≤ Subgroup.center SL(2, F) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center SL(2, F))) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hab (QuotientGroup.mk' _ x),
      mul_inv_cancel_right, mul_inv_cancel]
  rw [Group.isPerfect_def.mp hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne (SL(2, F) ⧸ Subgroup.center SL(2, F))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

theorem isSolvable_statedSL_of_card_three {F : Type} [Field F] [Finite F] (h : Nat.card F = 3) :
    Group.IsSolvable ↥(StatedSL 2 F) := by
  have hcard : Nat.card ↥(StatedSL 2 F) = 2 ^ 3 * 3 := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h]
    norm_num
  have : (Nat.card ↥(StatedSL 2 F)).primeFactors.card ≤ 2 := by
    rw [hcard, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
    decide
  exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two this

theorem four_le_card_of_odd {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : Nat.card F ≠ 3) : 4 ≤ Nat.card F := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨m, hm⟩ := hodd
  omega

theorem solvable_or_quasisimple_of_hasSL2Model {K : Type} [Group K] (h : HasSL2Model K Odd) :
    Group.IsSolvable K ∨ IsQuasisimple K := by
  obtain ⟨F, _, _, hodd, ⟨e⟩⟩ := h
  by_cases h3 : Nat.card F = 3
  · left
    have := isSolvable_statedSL_of_card_three h3
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  · right
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (specialLinearGroupEquivStatedSL 2 F)
        (isQuasisimple_special_linear_two (four_le_card_of_odd hodd h3)))

end SL2Facts

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
