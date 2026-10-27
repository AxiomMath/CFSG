module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYLevi
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

@[expose] def yPerfTable : List ((Fin Tag.E6.rank → ℤ) × (Fin Tag.E6.rank → ℤ)) :=
  [(![0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, -1, 0]),
    (![1, 0, 1, 1, 1, 0], ![0, 0, -1, -1, -1, 0]),
    (![0, 1, 0, 1, 1, 0], ![0, -1, 0, 0, 0, 0]),
    (![0, 1, 0, 1, 1, 0], ![0, 0, 0, 0, -1, 0]),
    (![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 0]),
    (![1, 1, 2, 2, 1, 0], ![0, -1, -1, -1, -1, 0]),
    (![1, 1, 2, 2, 1, 0], ![0, -1, -1, -1, 0, 0]),
    (![1, 1, 2, 2, 1, 0], ![0, 0, -1, -1, -1, 0]),
    (![0, 0, 0, 0, 0, 1], ![1, 0, 1, 1, 1, 0]),
    (![0, 1, 0, 1, 1, 0], ![1, 0, 1, 1, 0, 0]),
    (![0, 0, 0, 0, 0, 1], ![1, 1, 1, 2, 1, 0]),
    (![0, 1, 0, 1, 1, 0], ![1, 0, 1, 1, 1, 1]),
    (![1, 1, 2, 2, 1, 0], ![0, 0, 0, 1, 1, 1]),
    (![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, -1, -1]),
    (![0, 1, 0, 1, 1, 0], ![0, -1, -1, -1, -1, 0]),
    (![0, -1, 0, -1, -1, 0], ![0, 0, 0, 1, 1, 0]),
    (![1, 1, 2, 2, 1, 0], ![-1, -1, -2, -2, -2, -1]),
    (![0, 0, 0, 0, 0, 1], ![0, 0, -1, -1, -1, -1]),
    (![-1, -1, -2, -2, -1, 0], ![1, 0, 1, 1, 1, 0]),
    (![0, 1, 0, 1, 1, 0], ![0, -1, -1, -2, -2, -1]),
    (![0, 0, 0, 0, 0, 1], ![0, -1, -1, -1, -1, -1]),
    (![0, 0, 0, 0, 0, -1], ![0, -1, -1, -1, -1, 0]),
    (![0, -1, 0, -1, -1, 0], ![0, 0, -1, -1, -1, -1]),
    (![-1, -1, -2, -2, -1, 0], ![0, 0, 0, 0, -1, -1])]

theorem yPerfTable_check :
    ∀ γ ∈ rootFinset .E6, 0 < iform γ yLam → ∃ p ∈ yPerfTable, p.1 + p.2 = γ ∧
      p.1 ∈ rootFinset .E6 ∧ p.2 ∈ rootFinset .E6 ∧ 0 < iform p.2 yLam ∧
      ((iform p.1 yA1 = 0 ∧ iform p.1 yA4 = 0) ∨ 0 < iform p.1 yLam) ∧ p.1 ≠ p.2 := by
  decide +kernel

section Perfect

variable {K : Type} [Field K]

theorem commutator_pinnedX_charTwo [CharP K 2] {δ ε : Fin Tag.E6.rank → ℤ} (hδ : IsRoot .E6 δ)
    (hε : IsRoot .E6 ε) (hne : δ ≠ ε) (hr : IsRoot .E6 (δ + ε)) (c d : K) :
    ⁅pinnedX .E6 K δ c, pinnedX .E6 K ε d⁆ = pinnedX .E6 K (δ + ε) (c * d) := by
  have hne' : δ ≠ -ε := fun e => hr.ne_zero (by rw [e, neg_add_cancel])
  obtain ⟨hs, hcomm⟩ := (simply_laced_root_commutator_unit.{0} Tag.E6 (Or.inr (Or.inl rfl)) hδ
    hε hne hne').1 hr
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs1 : (commConst Tag.E6 δ ε (1, 1) : K) = 1 := by
    rcases hs with h | h
    · rw [h, Int.cast_one]
    · rw [h, Int.cast_neg, Int.cast_one]
      linear_combination -h2
  rw [hcomm K c d, hs1, one_mul]

theorem pinnedX_mem_yRadical_sup_yLevi {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    (h : (iform γ yA1 = 0 ∧ iform γ yA4 = 0) ∨ 0 < iform γ yLam) (c : K) :
    (⟨pinnedX .E6 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .E6 K) ∈
      yRadical K ⊔ yLevi K := by
  rcases h with h | h
  · exact mem_sup_right (mem_yLevi_iff.2 (rootSubgroup_le_yLeviGL ⟨hγ, h⟩
      (mem_rootSubgroup.2 ⟨c, rfl⟩)))
  · exact mem_sup_left (mem_yRadical_iff.2 (pinnedX_mem_rootSpan (S := yRadicalRoots) ⟨hγ, h⟩ c))

theorem yRadical_le_commutator [CharP K 2] :
    yRadical K ≤ ⁅yRadical K ⊔ yLevi K, yRadical K ⊔ yLevi K⁆ := by
  have hQ : yRadical K = closure {g : adjointGroup .E6 K |
      ∃ α ∈ yRadicalRoots, ∃ c : K, pinnedX .E6 K α c = g} :=
    F4Pilot.rootSpan_subgroupOf_eq_closure .E6 K yRadicalRoots
  rw [hQ, closure_le]
  rintro g ⟨γ, hγ, c, hg⟩
  have hg' : g = ⟨pinnedX .E6 K γ c, pinnedX_mem_adjointGroup γ c⟩ := Subtype.ext hg.symm
  subst hg'
  rw [← hQ]
  obtain ⟨p, -, hsum, h1, h2, h2rad, h1cases, hne⟩ :=
    yPerfTable_check γ (mem_rootFinset.2 hγ.1) hγ.2
  have hr : IsRoot .E6 (p.1 + p.2) := by rw [hsum]; exact hγ.1
  have e : (⟨pinnedX .E6 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .E6 K) =
      ⁅(⟨pinnedX .E6 K p.1 c, pinnedX_mem_adjointGroup _ c⟩ : adjointGroup .E6 K),
        ⟨pinnedX .E6 K p.2 1, pinnedX_mem_adjointGroup _ 1⟩⁆ := by
    apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← commutatorElement_def, commutator_pinnedX_charTwo (mem_rootFinset.1 h1) (mem_rootFinset.1 h2) hne hr, hsum,
      mul_one]
  rw [SetLike.mem_coe, e]
  exact commutator_mem_commutator
    (pinnedX_mem_yRadical_sup_yLevi (mem_rootFinset.1 h1) h1cases c)
    (pinnedX_mem_yRadical_sup_yLevi (mem_rootFinset.1 h2) (Or.inr h2rad) 1)

theorem commutator_yRadical_sup_yLevi [Finite K] [CharP K 2] :
    ⁅yRadical K ⊔ yLevi K, yRadical K ⊔ yLevi K⁆ = yRadical K ⊔ yLevi K := by
  refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le yRadical_le_commutator ?_)
  calc yLevi K = ⁅yLevi K, yLevi K⁆ := commutator_yLevi_eq.symm
    _ ≤ ⁅yRadical K ⊔ yLevi K, yRadical K ⊔ yLevi K⁆ := commutator_mono le_sup_right le_sup_right

end Perfect

end CFSG.SeitzReduction.E6Pilot
