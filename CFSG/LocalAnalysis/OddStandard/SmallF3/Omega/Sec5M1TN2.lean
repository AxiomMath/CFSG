module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5M1THom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN2Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec5m1t_N2 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {p : OGroup Q} (hp : p * p = piOrth Q) :
    ∃ N : Subgroup (OGroup Q),
      N ≤ omegaGroup hQ ⊓ centralizer ({p} : Set (OGroup Q)) ∧
      (N.subgroupOf (omegaGroup hQ ⊓ centralizer ({p} : Set (OGroup Q)))).Normal ∧
      (N.subgroupOf (omegaGroup hQ ⊓ centralizer ({p} : Set (OGroup Q)))).index = 2 ∧
      CFSG.IsQuasisimple ↥N ∧ LieModel ↥N .PSU 3 3 1 ∧
      piOrth Q ∈ omegaGroup hQ ⊓ centralizer ({p} : Set (OGroup Q)) ∧ piOrth Q ∉ N ∧
      ∀ g ∈ omegaGroup hQ ⊓ centralizer ({p} : Set (OGroup Q)),
        g ∈ N ∨ piOrth Q * g ∈ N := by
  obtain ⟨hLie, hG1Ω, hπ, hcov⟩ := ff6m_N2_core hQ hdim hsgn hp
  have hG1C : ⁅centralizer ({p} : Set (OGroup Q)), centralizer ({p} : Set (OGroup Q))⁆ ≤
      centralizer ({p} : Set (OGroup Q)) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hπΩ : piOrth Q ∈ omegaGroup hQ :=
    (piOrth_mem_omegaGroup_iff hQ).mpr ⟨by rw [hdim]; decide, by rw [hsgn, hdim]; decide⟩
  have hπC : piOrth Q ∈ centralizer ({p} : Set (OGroup Q)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_piOrth_comm p).symm
  have hπY : piOrth Q ∈ omegaGroup hQ ⊓ centralizer ({p} : Set (OGroup Q)) := ⟨hπΩ, hπC⟩
  have hidx := sec5m1t_index_two (fun g => (mul_piOrth_comm g).symm) hπY hπ hcov
  exact ⟨_, fun x hx => ⟨hG1Ω hx, hG1C hx⟩, Subgroup.normal_of_index_eq_two hidx, hidx,
    l515S_isQuasisimple_of_u33 hLie, hLie, hπY, hπ, hcov⟩

end CFSG.OddStandard.SmallF3.Omega
