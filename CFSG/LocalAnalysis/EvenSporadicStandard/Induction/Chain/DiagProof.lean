module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.DiagSetup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.DiagT
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.DiagDef

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem diagData_all (H : Type) [Group H] [Finite H] : DiagData H := by
  intro R T₀ K' A N₀ t hKq hT₀R hK'T₀ hA hK'P hcov hN₀N hN₀K' htR htN htt
  obtain ⟨hS, hAiso⟩ := diag_setup hKq hT₀R hK'T₀ hA hK'P hcov hN₀K'
  have hAq : CFSG.IsQuasisimple ↥A := hA.isQuasisimple
  have : Group.IsPerfect ↥A := hAq.1
  set ν := orbitNorm hA hN₀N with hν
  have hDE : ν.range ≤ orbitSup N₀ A := by
    rintro _ ⟨x, rfl⟩
    exact orbitNorm_mem hA hN₀N x
  have hDN : ν.range ≤ centralizer (N₀ : Set H) := fun d hd =>
    Subgroup.mem_centralizer_iff.2 fun n hn => (orbitNorm_commute hA hN₀N hS hn d hd).symm
  have hker : ν.rangeRestrict.ker ≤ center ↥A := by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
    let B₀ : ↥(orbitSet N₀ A) := ⟨A, self_mem_orbitSet N₀ A⟩
    obtain ⟨c, hc, -, hxc⟩ := orbitNorm_factor hA hN₀N B₀ x
    have hmap : ((orbitMap N₀ A B₀ x : ↥(B₀ : Subgroup H)) : H) = x := by
      rw [orbitMap_coe]
      exact hS _ (orbitRep_mem _ _ _) (map_orbitRep N₀ A B₀) x x.2
    rw [hmap, hx] at hxc
    have hxinv : (x : H) = c⁻¹ := eq_inv_of_mul_eq_one_right hxc.symm
    have hxC : (x : H) ∈ centralizer (A : Set H) := by
      rw [hxinv]
      exact (centralizer (A : Set H)).inv_mem hc
    refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
    exact Subgroup.mem_centralizer_iff.1 hxC g g.2
  refine ⟨ν.range, Group.IsPerfect.range ν, hDN, ?_, ?_⟩
  · obtain ⟨e₁⟩ := cqEquiv_of_central_cover ν.rangeRestrict ν.rangeRestrict_surjective hker
    obtain ⟨e₂⟩ := hAiso
    exact ⟨e₁.symm.trans e₂⟩
  · by_cases hAt : A.map (MulAut.conj t).toMonoidHom ∈ orbitSet N₀ A
    · exact Or.inl (orbit_stable_case hA hN₀N hS htN hAt)
    · exact Or.inr (orbit_swap_case hA hN₀N htR htN hAt hDE)

end CFSG.EvenSporadicStandard.Induction
