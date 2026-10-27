module

public import CFSG.GH74.KGroups.Sz8Tables

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

open CFSG.Blueprint

@[irreducible] private def m12a : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

@[irreducible] private def m12b : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

private def m12w : Equiv.Perm (Fin 12) :=
  m12a * m12b * m12a * m12b * m12a * m12b * m12a * m12b⁻¹ * m12a * m12b * m12a * m12b⁻¹ *
    m12a * m12b⁻¹

private lemma m12a_mem : m12a ∈ NativeSporadic.M12 := by
  unfold m12a NativeSporadic.M12
  exact Subgroup.subset_closure (by simp)

private lemma m12b_mem : m12b ∈ NativeSporadic.M12 := by
  unfold m12b NativeSporadic.M12
  exact Subgroup.subset_closure (by simp)

private lemma m12w_mem : m12w ∈ NativeSporadic.M12 := by
  have ha := m12a_mem
  have hb := m12b_mem
  have hb' : m12b⁻¹ ∈ NativeSporadic.M12 := Subgroup.inv_mem _ hb
  unfold m12w
  repeat' first
    | apply Subgroup.mul_mem
    | exact ha
    | exact hb
    | exact hb'

private lemma m12w_pow8 : m12w ^ 8 = 1 := by decide +kernel

private lemma m12w_pow4 : m12w ^ 4 ≠ 1 := by decide +kernel

private lemma orderOf_m12w : orderOf m12w = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := m12w)
    (by simpa using m12w_pow4) (by simpa using m12w_pow8)
  simpa using h

theorem not_sz8_of_noncomm
    {X : Type} [Group X] [Finite X]
    (hN : ∀ S : Sylow 2 X, ∃ a ∈ (S : Subgroup X), ∃ b ∈ (S : Subgroup X),
      a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a * b ≠ b * a) :
    ¬ LieModel X .twistedB2 0 2 3 := by
  rintro h
  let S : Sylow 2 X := default
  obtain ⟨a, ha, b, hb, ha2, hb2, hab⟩ := hN S
  have hc := (CFSG.GH74.KGroups.Sz8.bender h (S : Subgroup X) S.isPGroup' S.not_dvd_index).1
  exact hab (hc a ha ha2 b hb).symm

theorem not_M12_of_no_order_eight {X : Type} [Group X] (h8 : ∀ x : X, orderOf x ≠ 8) :
    ¬ NativeSporadic.IsSporadic X .M12 := by
  rintro ⟨e⟩
  let z : NativeSporadic.Carrier .M12 := ⟨m12w, m12w_mem⟩
  have hz : orderOf z = 8 := by
    change orderOf (⟨m12w, m12w_mem⟩ : NativeSporadic.M12) = 8
    rw [Subgroup.orderOf_mk, orderOf_m12w]
  refine h8 (e.symm z) ?_
  rw [MulEquiv.orderOf_eq]
  exact hz

end CFSG.EvenSporadicStandard.HNRecog.GH73
