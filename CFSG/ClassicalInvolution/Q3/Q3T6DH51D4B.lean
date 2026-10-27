module

public import CFSG.ClassicalInvolution.Q3.Q3T6DH51D4A
public import CFSG.ClassicalInvolution.Q3.Q3CHHyp51

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

theorem oddCoreIn_inf_inf_eq_bot {G : Type} [Group G] [Finite G] (C I : Subgroup G)
    (h1 : oddCoreIn (C ⊓ I) = ⊥) : oddCoreIn C ⊓ (C ⊓ I) = ⊥ := by
  refine le_bot_iff.mp ?_
  have hnormS : ∀ y ∈ C ⊓ I, ∀ w, w ∈ oddCoreIn C ⊓ (C ⊓ I) →
      y * w * y⁻¹ ∈ oddCoreIn C ⊓ (C ⊓ I) := by
    intro y hy w hw
    exact ⟨conj_mem_oddCoreIn hy.1 hw.1,
      (C ⊓ I).mul_mem ((C ⊓ I).mul_mem hy hw.2) ((C ⊓ I).inv_mem hy)⟩
  have hle : oddCoreIn C ⊓ (C ⊓ I) ≤ oddCoreIn (C ⊓ I) := by
    refine le_oddCoreIn_of_normalizes inf_le_right (fun y hy => ?_)
      ((odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hnormS y hy w, fun h => ?_⟩
    have := hnormS y⁻¹ ((C ⊓ I).inv_mem hy) _ h
    simpa [mul_assoc] using this
  rwa [h1] at hle

theorem mul_comm_of_mem_of_forall_mul_self_eq_one {G : Type} [Group G] {A : Subgroup G}
    (hA2 : ∀ x ∈ A, x * x = 1) {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x := by
  have h1 := inv_eq_of_mul_eq_one_right (hA2 (x * y) (A.mul_mem hx hy))
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hA2 x hx),
    inv_eq_of_mul_eq_one_right (hA2 y hy)] at h1
  exact h1.symm

theorem commutator_oddCoreIn_eq_bot_of_inf {G : Type} [Group G] [Finite G] {I : Subgroup G}
    [I.Normal] {A : Subgroup G} (hAI : A ≤ I) (hA2 : ∀ x ∈ A, x * x = 1) {a : G} (haA : a ∈ A)
    (h : oddCoreIn (Subgroup.centralizer ({a} : Set G) ⊓ I) = ⊥) :
    ⁅oddCoreIn (Subgroup.centralizer ({a} : Set G)), A⁆ = ⊥ := by
  have hM := oddCoreIn_inf_inf_eq_bot (Subgroup.centralizer ({a} : Set G)) I h
  refine le_bot_iff.mp (Subgroup.commutator_le.mpr fun n hn x hx => ?_)
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_comm_of_mem_of_forall_mul_self_eq_one hA2 hx haA
  have hnC : n ∈ Subgroup.centralizer ({a} : Set G) := oddCoreIn_le _ hn
  have hxI : x ∈ I := hAI hx
  have hcomm : ⁅n, x⁆ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) ⊓
      (Subgroup.centralizer ({a} : Set G) ⊓ I) := by
    refine ⟨?_, ?_, ?_⟩
    · have h3 : x * n⁻¹ * x⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) :=
        conj_mem_oddCoreIn hxC ((oddCoreIn _).inv_mem hn)
      have : ⁅n, x⁆ = n * (x * n⁻¹ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact (oddCoreIn _).mul_mem hn h3
    · have : ⁅n, x⁆ = n * x * n⁻¹ * x⁻¹ := commutatorElement_def n x
      rw [this]
      exact (Subgroup.centralizer ({a} : Set G)).mul_mem
        ((Subgroup.centralizer ({a} : Set G)).mul_mem
          ((Subgroup.centralizer ({a} : Set G)).mul_mem hnC hxC)
          ((Subgroup.centralizer ({a} : Set G)).inv_mem hnC))
        ((Subgroup.centralizer ({a} : Set G)).inv_mem hxC)
    · have h4 : n * x * n⁻¹ ∈ I := Subgroup.Normal.conj_mem inferInstance x hxI n
      have : ⁅n, x⁆ = n * x * n⁻¹ * x⁻¹ := commutatorElement_def n x
      rw [this]
      exact I.mul_mem h4 (I.inv_mem hxI)
  rw [hM] at hcomm
  exact hcomm

theorem alphaOf_eq_bot_of_commutator_of_exists {G : Type} [Group G] {A : Subgroup G}
    (h1 : ∀ a ∈ A, a ≠ 1 → ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆ = ⊥)
    (h2 : ∃ a ∈ A, a ≠ 1 ∧ oddCoreOf (Subgroup.centralizer ({a} : Set G)) = ⊥) :
    alphaOf A = ⊥ := by
  unfold alphaOf
  have h1' : (⨆ a ∈ A, ⨆ (_ : a ≠ 1), ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆) =
      ⊥ := by
    simp only [iSup_eq_bot]
    exact h1
  have h2' : (⨅ a ∈ A, ⨅ (_ : a ≠ 1), oddCoreOf (Subgroup.centralizer ({a} : Set G))) = ⊥ := by
    obtain ⟨a, ha, ha1, hO⟩ := h2
    exact le_bot_iff.mp (((iInf₂_le a ha).trans (iInf_le _ ha1)).trans hO.le)
  rw [h1', h2', sup_bot_eq]

section D4


theorem autOddFreeOn_classicalInner_D4 {X : Type} [Group X] [Finite X]
    (ψ : (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →* X)
    (hker : ψ.ker ≤ Subgroup.center _) :
    AutOddFreeOn ↥ψ.range (Q3CH.ClassicalInner ↥ψ.range) := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaPlus 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hker' : ψ.rangeRestrict.ker ≤ Subgroup.center _ := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  obtain ⟨hXq, hψ', hker'', hSq, hZS⟩ := centralQuotientData (t := .POmegaPlus) (n := 4)
    Nat.prime_three trivial hadm ↥ψ.range ψ.rangeRestrict ψ.rangeRestrict_surjective hker'
  have : Group.IsPerfect ↥ψ.range := ⟨hXq.1⟩
  exact Q3CH.autOddFreeOn_classicalInner_of_innerOn (Q3CH.autOddFreeInnerOn_of_centralQuotient
    (autOddFreeInnerOn_D4 hSq hZS _ hψ' hker''))

theorem alphaOf_eq_bot_of_inner_one_classical (H : Type) [Group H] [Finite H] (L : Subgroup H)
    (ψ : (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →* H) (hψ : ψ.range = L)
    (hker : ψ.ker ≤ Subgroup.center _) (A : Subgroup ↥(inducedAutOn L))
    (h2 : ∀ x ∈ A, x * x = 1)
    (hinn : ∀ x ∈ A, ((x : ↥(inducedAutOn L)) : MulAut ↥L) ∈ innSubgroup ↥L)
    (hcl : ∃ x ∈ A, x ≠ 1 ∧ Q3CH.ClassicalInner ↥L ((x : ↥(inducedAutOn L)) : MulAut ↥L)) :
    alphaOf A = ⊥ := by
  subst hψ
  have hker' : ψ.rangeRestrict.ker ≤ Subgroup.center _ := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hInn : InnPartOddFree ↥ψ.range :=
    innPartOddFree_of_D4 ↥ψ.range ψ.rangeRestrict ψ.rangeRestrict_surjective hker'
  have hrow := autOddFreeOn_classicalInner_D4 ψ hker
  obtain ⟨a₀, ha₀A, ha₀1, ha₀cl⟩ := hcl
  have hord : ∀ a ∈ A, a ≠ 1 → orderOf a = 2 := fun a ha ha1 =>
    orderOf_eq_prime (by rw [sq]; exact h2 a ha) ha1
  have hO₀ : oddCoreIn (Subgroup.centralizer ({a₀} : Set ↥(inducedAutOn ψ.range))) = ⊥ :=
    hrow (inducedAutOn ψ.range) (innSubgroup_le_inducedAutOn ψ.range) a₀ ha₀cl
      (hord a₀ ha₀A ha₀1)
  refine alphaOf_eq_bot_of_commutator_of_exists (fun a ha ha1 => ?_) ⟨a₀, ha₀A, ha₀1, hO₀⟩
  have hcomm := commutator_oddCoreIn_eq_bot_of_inf
    (I := (innSubgroup ↥ψ.range).subgroupOf (inducedAutOn ψ.range)) (A := A)
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hinn x hx)) h2 ha
    (hInn (inducedAutOn ψ.range) (innSubgroup_le_inducedAutOn ψ.range) a (hinn a ha)
      (hord a ha ha1))
  exact hcomm

end D4

end CFSG.ClassicalInvolution.Q3.Q3T6D
