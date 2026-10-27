module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts
public import CFSG.Dihedral.BlueprintDefs
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenDistinctInvertedConjugate
import all CFSG.Dihedral.BlueprintDefs

public noncomputable section

namespace CFSG.GorensteinWalter

open DihedralBlueprint

theorem a7U_fourgroup_cycles (V : Subgroup ASevenCertificateGroup)
    (hV : IsKleinFour V) (hcent : V ≤ Subgroup.centralizer (a7U : Set ASevenCertificateGroup)) :
    Cycles (Subgroup.normalizer (a7U : Set ASevenCertificateGroup)) V := by
  letI a7VDecidablePred : DecidablePred (fun x : ASevenCertificateGroup => x ∈ a7V) := fun x => by
    change Decidable (x = 1 ∨ x = a7t ∨ x = a7u ∨ x = a7t * a7u)
    infer_instance
  letI a7VFintype : Fintype a7V := Subtype.fintype _
  letI a7VPermFintype : Fintype (Equiv.Perm a7V) := inferInstance
  rw [kleinFour_eq_a7V_of_centralizes_a7U V hV hcent]
  let x : ASevenCertificateGroup :=
    ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2, by simp [Equiv.Perm.sign_mul]⟩
  have hxU : x ∈ Subgroup.normalizer (a7U : Set ASevenCertificateGroup) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    change y = 1 ∨ y = a7a ∨ y = a7a ^ 2 at hy
    rcases hy with rfl | rfl | rfl <;> decide
  have hxV : x ∈ Subgroup.normalizer (a7V : Set ASevenCertificateGroup) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro y ⟨v, hv, rfl⟩
      change v = 1 ∨ v = a7t ∨ v = a7u ∨ v = a7t * a7u at hv
      rcases hv with rfl | rfl | rfl | rfl <;> decide
    · intro y hy
      apply Subgroup.mem_map.mpr
      refine ⟨x⁻¹ * y * x, ?_, ?_⟩
      · change y = 1 ∨ y = a7t ∨ y = a7u ∨ y = a7t * a7u at hy
        rcases hy with rfl | rfl | rfl | rfl <;> decide
      · change x * (x⁻¹ * y * x) * x⁻¹ = y
        group
  refine ⟨x, hxU, hxV, ?_⟩
  intro v hv hvne
  change v = 1 ∨ v = a7t ∨ v = a7u ∨ v = a7t * a7u at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact (hvne rfl).elim
  all_goals decide

end CFSG.GorensteinWalter
