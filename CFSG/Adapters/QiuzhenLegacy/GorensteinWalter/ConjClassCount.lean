module

public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.EvenSporadicStandard.SuzOuter

variable {G : Type*} [Group G]

theorem card_orbit_conj_eq_index [Finite G] (x : G) :
    Nat.card (MulAction.orbit (ConjAct G) x) = (Subgroup.centralizer ({x} : Set G)).index := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype (MulAction.orbit (ConjAct G) x) := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer (ConjAct G) x) := Fintype.ofFinite _
  have hst := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) x
  have hst' : Fintype.card (MulAction.orbit (ConjAct G) x) *
      Fintype.card (MulAction.stabilizer (ConjAct G) x) = Fintype.card G := by
    simpa using hst
  let e : MulAction.stabilizer (ConjAct G) x ≃ Subgroup.centralizer ({x} : Set G) :=
    { toFun := fun y =>
        ⟨ConjAct.ofConjAct y.1, by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          simp at hz
          rw [hz]
          have hy : y.1 • x = x := y.2
          rw [ConjAct.smul_def] at hy
          exact (mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hy)).symm⟩
      invFun := fun z =>
        ⟨ConjAct.toConjAct (z : G), by
          change ConjAct.toConjAct (z : G) • x = x
          rw [ConjAct.toConjAct_smul]
          exact mul_inv_eq_of_eq_mul
            ((Subgroup.mem_centralizer_iff.mp z.2) x (by simp)).symm⟩
      left_inv := by intro y; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; rfl }
  have hC : Fintype.card (MulAction.stabilizer (ConjAct G) x) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr e
  have hN : (Subgroup.centralizer ({x} : Set G)).index *
      Fintype.card (MulAction.stabilizer (ConjAct G) x) = Fintype.card G := by
    rw [hC, ← Nat.card_eq_fintype_card]
    exact Subgroup.index_mul_card (Subgroup.centralizer ({x} : Set G))
  rw [Nat.card_eq_fintype_card]
  exact Nat.mul_right_cancel
    (by positivity : 0 < Fintype.card (MulAction.stabilizer (ConjAct G) x)) (by
      rw [← hN] at hst'
      exact hst')

theorem card_conj_mul_card_centralizer [Finite G] (x : G) :
    Nat.card {y : G // ∃ c : G, y = c * x * c⁻¹} *
      Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card G := by
  have e : {y : G // ∃ c : G, y = c * x * c⁻¹} ≃ MulAction.orbit (ConjAct G) x :=
    Equiv.subtypeEquivRight fun y => by
      rw [MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨ConjAct.toConjAct c, ConjAct.toConjAct_smul c x⟩
      · rintro ⟨c, hc⟩
        exact ⟨ConjAct.ofConjAct c, by rw [← hc, ← ConjAct.toConjAct_smul]; rfl⟩
  rw [Nat.card_congr e, card_orbit_conj_eq_index]
  exact Subgroup.index_mul_card _

end CFSG.EvenSporadicStandard.SuzOuter
