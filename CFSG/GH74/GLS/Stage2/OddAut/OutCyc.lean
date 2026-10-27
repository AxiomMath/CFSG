module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Subgroup

theorem exists_mem_ker_of_isCyclic {G H : Type*} [Group G] [Group H] [IsCyclic H] {r : ℕ}
    [Fact r.Prime] (Θ : G →* H) {V : Subgroup G} [IsElementaryAbelian r V]
    (hVc : Nat.card V = r ^ 2) : ∃ v ∈ V, v ≠ 1 ∧ Θ v = 1 := by
  have hr : r.Prime := Fact.out
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (Θ.comp V.subtype) := by
    rw [injective_iff_map_eq_one]
    intro v hv
    by_contra hv1
    exact hcon v v.2 (fun h => hv1 (Subtype.ext h)) hv
  have hcyc : IsCyclic V := isCyclic_of_injective _ hinj
  have h1 : Monoid.exponent V = Nat.card V := IsCyclic.exponent_eq_card
  have h2 : Monoid.exponent V ∣ r := IsElementaryAbelian.exponent_dvd_p r V
  rw [h1, hVc] at h2
  have h3 := Nat.le_of_dvd hr.pos h2
  have h4 := hr.two_le
  nlinarith

end CFSG.GH74.GLS.Stage2.OddAut
