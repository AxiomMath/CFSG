module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L77H
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma77b_of (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (hP : Asc82Tab6P)
    (h77a : Asc82Lemma77a) : Asc82Lemma77b := by
  intro G _ _ t L S z g B hc
  by_contra hcon
  push_neg at hcon
  have hle : CFSG.conjugate L g ⊓ MSub S B ≤
      MSub S B ⊓ centralizer ({t} : Set G) ⊓ centralizer ({g⁻¹ * t * g} : Set G) := by
    intro n hn
    have hnL : g * n * g⁻¹ ∈ L := (mem_conjugate_iff L g n).mp hn.1
    have hcomm : (g * n * g⁻¹) * t = t * (g * n * g⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hc.ctx.le_centralizer hnL)
    have hns : n * (g⁻¹ * t * g) = (g⁻¹ * t * g) * n := by
      calc n * (g⁻¹ * t * g) = g⁻¹ * ((g * n * g⁻¹) * t) * g := by group
        _ = g⁻¹ * (t * (g * n * g⁻¹)) * g := by rw [hcomm]
        _ = (g⁻¹ * t * g) * n := by group
    exact ⟨⟨hn.2, Subgroup.mem_centralizer_singleton_iff.mpr (hcon n hn).symm⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr hns⟩
  have hsolH := sec7l77_H_solvable h36 h72 hP hc
  have hsolR : Group.IsSolvable ↥(CFSG.conjugate L g ⊓ MSub S B) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hle)
  obtain ⟨-, ρ, hρ, -⟩ := h77a G t L S z g B hc
  haveI : Group.IsSolvable (Equiv.Perm (Fin 5)) := solvable_of_surjective hρ
  exact Equiv.Perm.fin_5_not_solvable this

end CFSG.OddStandard.SmallF3.Omega
