module

public import CFSG.Holt.SmallGroups
public import CFSG.CharacterTheory.Semidihedral.FourPointPresentation

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Equiv Equiv.Perm CFSG.Holt.SmallGroups CFSG.Adapters.RankTwoModelTransports
  CFSG.Semidihedral.FourPointPresentation

@[expose] def m11a1 : Perm (Fin 11) :=
  List.formPerm [1, 2] * List.formPerm [4, 10] * List.formPerm [5, 6] * List.formPerm [7, 8]

@[expose] def m11b1 : Perm (Fin 11) :=
  List.formPerm [0, 1] * List.formPerm [3, 8] * List.formPerm [5, 6] * List.formPerm [9, 10]

@[expose] def m11c1 : Perm (Fin 11) :=
  List.formPerm [1, 2] * List.formPerm [3, 6] * List.formPerm [5, 9] * List.formPerm [8, 10]

@[expose] def m11t1 : Perm (Fin 11) :=
  List.formPerm [1, 3] * List.formPerm [2, 4] * List.formPerm [5, 7] * List.formPerm [8, 9]

theorem m11a1_eq : m11a1 = [m11CatD, m11CatC, m11CatD, m11CatD, m11CatC, m11CatC, m11CatC,
    m11CatD, m11CatD, m11CatC, m11CatC, m11CatD].prod := by
  decide +kernel

theorem m11b1_eq : m11b1 = [m11CatC, m11CatD, m11CatC, m11CatD, m11CatC, m11CatD, m11CatC,
    m11CatC, m11CatC, m11CatC].prod := by
  decide +kernel

theorem m11c1_eq : m11c1 = [m11CatD, m11CatD, m11CatD, m11CatC, m11CatD, m11CatC, m11CatD,
    m11CatC, m11CatC, m11CatC, m11CatC].prod := by
  decide +kernel

theorem m11t1_eq : m11t1 = [m11CatD, m11CatC, m11CatD, m11CatD, m11CatC, m11CatC,
    m11CatD].prod := by
  decide +kernel

theorem m11a1_mem : m11a1 ∈ CFSG.Open.M11 := by
  rw [m11a1_eq]
  exact list_prod_mem_m11 (by decide +kernel)

theorem m11b1_mem : m11b1 ∈ CFSG.Open.M11 := by
  rw [m11b1_eq]
  exact list_prod_mem_m11 (by decide +kernel)

theorem m11c1_mem : m11c1 ∈ CFSG.Open.M11 := by
  rw [m11c1_eq]
  exact list_prod_mem_m11 (by decide +kernel)

theorem m11t1_mem : m11t1 ∈ CFSG.Open.M11 := by
  rw [m11t1_eq]
  exact list_prod_mem_m11 (by decide +kernel)

theorem m11_comm_z : m11a1 * m11z = m11z * m11a1 ∧ m11b1 * m11z = m11z * m11b1 ∧
    m11c1 * m11z = m11z * m11c1 := by
  decide +kernel

theorem m11_sq_one : m11a1 * m11a1 = 1 ∧ m11b1 * m11b1 = 1 ∧ m11c1 * m11c1 = 1 ∧
    m11t1 * m11t1 = 1 ∧ m11z * m11z = 1 := by
  decide +kernel

theorem m11_relations : (m11a1 * m11b1) ^ 3 = 1 ∧ (m11b1 * m11c1) ^ 3 = 1 ∧
    (m11a1 * m11c1) ^ 2 = m11z := by
  decide +kernel

theorem m11_zt1_five : (m11z * m11t1) ^ 5 = 1 ∧ m11z * m11t1 ≠ 1 := by
  decide +kernel

theorem m11_normalWord_images_inj : ∀ i j : Fin 2 × Fin 6 × Fin 4,
    (normalWord m11a1 m11b1 m11c1 m11z i 0 = normalWord m11a1 m11b1 m11c1 m11z j 0 ∧
      normalWord m11a1 m11b1 m11c1 m11z i 1 = normalWord m11a1 m11b1 m11c1 m11z j 1 ∧
      normalWord m11a1 m11b1 m11c1 m11z i 2 = normalWord m11a1 m11b1 m11c1 m11z j 2 ∧
      normalWord m11a1 m11b1 m11c1 m11z i 3 = normalWord m11a1 m11b1 m11c1 m11z j 3) → i = j := by
  decide +kernel

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
