module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGLayer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_comm_le_self {G : Type*} [Group G] (C : Subgroup G) : ⁅C, C⁆ ≤ C := by
  rw [Subgroup.commutator_le]
  intro p hp q hq
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq)

theorem fg_mem_ffFix_of_fixed (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (ρ : ↥(simGroup Q)) {g : OGroup Q}
    (hg : g ∈ omegaGroup hQ) (hfix : simAct Q ρ g = g) :
    (⟨toProj Q g, (mem_omegaProj_iff hQ).mpr ⟨g, hg, rfl⟩⟩ : ↥(omegaProj hQ)) ∈
      ffFix hQ h2 (QuotientGroup.mk ρ : ProjSim Q) := by
  apply mem_fixSub_iff.mpr
  apply Subtype.ext
  rw [coe_ffSimOmegaAct, projSimAct_mk, projActAux_toProj, hfix]

theorem fg_ha_of_component (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    {ρ : ↥(simGroup Q)} {t : CFSG.Open.StatedLieTag} {n k : ℕ}
    (hsh : ∀ (E : Type) [Group E], LieModel E t n 3 k →
      IsSimpleGroup E ∧ ∃ a b : E, a * b ≠ b * a)
    (hLM : LayerModel ↥(ffFix hQ h2 (QuotientGroup.mk ρ : ProjSim Q)) t n k)
    {J : Subgroup ↥(omegaProj hQ)}
    (hJ : IsComponentIn J (ffFix hQ h2 (QuotientGroup.mk ρ : ProjSim Q)))
    {P : Subgroup (OGroup Q)} (hPΩ : P ≤ omegaGroup hQ) (hPfix : P ≤ fixSub (simAct Q ρ))
    (hperf : Group.IsPerfect ↥P) {A : Subgroup (ProjSim Q)}
    (hAJ : ∀ a ∈ A, ∀ j ∈ J, projSimAct Q a (j : ProjOrth Q) = (j : ProjOrth Q)) :
    ∀ a ∈ A, ∀ j ∈ P, toProj Q (projSimActO Q a j) = toProj Q j := by
  intro a ha j hj
  let f1 : ↥P →* ↥(omegaProj hQ) :=
    ((toProj Q).comp P.subtype).codRestrict (omegaProj hQ) (fun c =>
      (mem_omegaProj_iff hQ).mpr ⟨c, hPΩ c.2, rfl⟩)
  let ψ : ↥P →* ↥(ffFix hQ h2 (QuotientGroup.mk ρ : ProjSim Q)) :=
    f1.codRestrict _ (fun c =>
      fg_mem_ffFix_of_fixed hQ h2 ρ (hPΩ c.2) (mem_fixSub_iff.mp (hPfix c.2)))
  have hmem := fg_mem_component_of_perfect hsh hLM hJ hperf ψ ⟨j, hj⟩
  rw [toProj_projSimActO]
  exact hAJ a ha _ hmem

end CFSG.OddStandard.SmallF3.Omega
