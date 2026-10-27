module


import CFSG.GroupTheory.ThreeTranspositions.FischerResidualAction
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

namespace CFSG.GroupTheory.ThreeTranspositions

theorem map_perfectResidual_centralizer_eq_of_odd_ker {W K : Type*} [Group W] [Group K]
    [Finite W] [Finite K] (π : W →* K) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center W) (hodd : Odd (Nat.card π.ker)) {d : W} (hd : d ^ 2 = 1) :
    ((CFSG.perfectResidual ↥(Subgroup.centralizer ({d} : Set W))).map
        (Subgroup.centralizer ({d} : Set W)).subtype).map π =
      (CFSG.perfectResidual ↥(Subgroup.centralizer ({π d} : Set K))).map
        (Subgroup.centralizer ({π d} : Set K)).subtype := by
  have hcent : (Subgroup.centralizer ({d} : Set W)).map π =
      Subgroup.centralizer ({π d} : Set K) :=
    map_centralizer_eq_of_odd_ker π hπ hker hodd hd
  let π' : ↥(Subgroup.centralizer ({d} : Set W)) →*
      ↥(Subgroup.centralizer ({π d} : Set K)) :=
    (π.comp (Subgroup.centralizer ({d} : Set W)).subtype).codRestrict
      (Subgroup.centralizer ({π d} : Set K)) fun x => by
        rw [← hcent]
        exact Subgroup.mem_map_of_mem π x.2
  have hπ' : Function.Surjective π' := by
    intro k
    have hk : (k : K) ∈ (Subgroup.centralizer ({d} : Set W)).map π := by
      rw [hcent]
      exact k.2
    obtain ⟨w, hw, hwk⟩ := Subgroup.mem_map.mp hk
    exact ⟨⟨w, hw⟩, Subtype.ext hwk⟩
  have hres : ((CFSG.perfectResidual ↥(Subgroup.centralizer ({d} : Set W))).map π') =
      CFSG.perfectResidual ↥(Subgroup.centralizer ({π d} : Set K)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq π' hπ'
  have hcomp : π.comp (Subgroup.centralizer ({d} : Set W)).subtype =
      (Subgroup.centralizer ({π d} : Set K)).subtype.comp π' :=
    MonoidHom.ext fun _ => rfl
  calc ((CFSG.perfectResidual ↥(Subgroup.centralizer ({d} : Set W))).map
        (Subgroup.centralizer ({d} : Set W)).subtype).map π
      = (CFSG.perfectResidual ↥(Subgroup.centralizer ({d} : Set W))).map
          (π.comp (Subgroup.centralizer ({d} : Set W)).subtype) := by
            rw [Subgroup.map_map]
    _ = (CFSG.perfectResidual ↥(Subgroup.centralizer ({d} : Set W))).map
          ((Subgroup.centralizer ({π d} : Set K)).subtype.comp π') := by rw [hcomp]
    _ = ((CFSG.perfectResidual ↥(Subgroup.centralizer ({d} : Set W))).map π').map
          (Subgroup.centralizer ({π d} : Set K)).subtype := by
            rw [Subgroup.map_map]
    _ = (CFSG.perfectResidual ↥(Subgroup.centralizer ({π d} : Set K))).map
          (Subgroup.centralizer ({π d} : Set K)).subtype := by rw [hres]

end CFSG.GroupTheory.ThreeTranspositions
