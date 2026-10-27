module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qMAComb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qMACent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qMACls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CNModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5c3qma_coset_mem {G : Type} [Group G] {t : G} {L : Subgroup G} {z r : G}
    {A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} (hm : Sec5Model58 t L z r A φ)
    {ζ : Fin 6 → ZMod 2} (hζz : φ ζ = z) {P : Subgroup G} {w u : Fin 6 → ZMod 2}
    (hw : φ w ∈ P) (hz : z ∈ P) (ht : t ∈ P) (hu : u ∈ [w, w + ζ, w + 1, w + 1 + ζ]) :
    φ u ∈ P := by
  have h1 : φ (1 : Fin 6 → ZMod 2) = t := by
    rw [Pi.one_def]
    exact hm.map_one
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact hw
  · rw [hm.perm.map_add, hζz]
    exact P.mul_mem hw hz
  · rw [hm.perm.map_add, h1]
    exact P.mul_mem hw ht
  · rw [hm.perm.map_add, hm.perm.map_add, hζz, h1]
    exact P.mul_mem (P.mul_mem hw ht) hz

theorem asc82Fact513AModel_of (hS : Asc82SchurU43) (hy : Sec5B59Hyp) : Asc82Fact513AModel := by
  intro G _ _ t L S z r B A K₁ K₂ h c
  obtain ⟨φ, ζ, hm, hζz, hζ4, hcent⟩ := sec5c3qma_cent_of_const hS c.toSec5KCtx
  intro a ha
  obtain ⟨haA, haK⟩ := Subgroup.mem_inf.mp ha
  obtain ⟨w, rfl⟩ := (hm.perm.mem_iff a).mp haA
  refine hcent w ?_
  by_contra hcon
  obtain ⟨u, hu, huζ, hwt⟩ := sec5c3qma_exists_heavy hζ4 hcon
  have hz : z ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h := Subgroup.mem_sup_left c.z_mem_K₃
  have hP := sec5c3qma_coset_mem hm hζz haK hz c.t_mem_sup₃₄ hu
  have hu1 : φ u ≠ 1 := by
    intro h1
    have h0 : u = 0 := hm.perm.injective (h1.trans hm.perm.map_zero.symm)
    subst h0
    revert hwt
    decide
  have huz : φ u ≠ z := fun h1 => huζ (hm.perm.injective (h1.trans hζz.symm))
  obtain ⟨h3, h4⟩ := sec5c3qma_wt_ne hS hy c hm hP hu1 huz
  rcases hwt with h | h
  · exact h3 h
  · exact h4 h

end CFSG.OddStandard.SmallF3.Omega
