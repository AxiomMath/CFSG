module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.GroupTheory.Commutator.JoinNormalizer

public section

namespace CFSG

open scoped commutatorElement

theorem le_centralizer_of_le_sup_pPrimeCore {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {C P : Subgroup G} {z : G}
    (hzP : z ∈ P) (hPC : P ≤ C) (hP : IsPGroup p P)
    (hle : C ≤ (Subgroup.centralizer ({z} : Set G) ⊓ C) ⊔ inSubgroup (pPrimeCore p) C) :
    P ≤ Subgroup.centralizer ({z} : Set G) := by
  classical
  let O : Subgroup G := inSubgroup (pPrimeCore p) C
  let D : Subgroup G := Subgroup.centralizer ({z} : Set G) ⊓ C
  have hzC : z ∈ C := hPC hzP
  have hOC : C ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le (pPrimeCore p ↥C))).mp
      (gLAPPrimeCoreOf_normal p C)
  have hOZ : ⁅O, Subgroup.zpowers z⁆ ≤ O :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (Subgroup.zpowers_le.mpr (hOC hzC))
  have hDZ : ⁅D, Subgroup.zpowers z⁆ ≤ O :=
    CFSG.GroupTheory.commutator_zpowers_le_of_forall_mem (N := O) (A := D) (c := z)
      (hOC hzC) (fun d hd => by
        rw [Commute.commutator_eq
          (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).1)]
        exact O.one_mem)
  have hcomm : ⁅O ⊔ D, Subgroup.zpowers z⁆ ≤ O :=
    CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize O D
      (Subgroup.zpowers z) O hOZ hDZ Subgroup.le_normalizer
      (fun x hx => hOC (Subgroup.mem_inf.mp hx).2)
  have hOcop : Nat.Coprime p (Nat.card O) := by
    dsimp only [O, inSubgroup]
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective C)]
    exact pPrimeCore_coprime_card
  intro q hq
  refine Subgroup.mem_centralizer_iff_commutator_eq_one'.mpr fun w hw => ?_
  rw [Set.mem_singleton_iff] at hw
  subst w
  have hqOD : q ∈ O ⊔ D := by
    simpa [O, D, sup_comm] using hle (hPC hq)
  have hdisj : P ⊓ O = ⊥ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by
      rw [hn]
      exact hOcop.pow_left n))
  have hmem : ⁅q, z⁆ ∈ P ⊓ O :=
    ⟨Subgroup.commutator_le_self P (P.commutator_mem_commutator hq hzP),
      hcomm (Subgroup.commutator_mem_commutator hqOD (Subgroup.mem_zpowers z))⟩
  simpa [hdisj] using hmem

end CFSG
