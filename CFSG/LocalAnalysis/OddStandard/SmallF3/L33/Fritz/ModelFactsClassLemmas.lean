module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.SetTheory.Cardinal.NatCard

public section

namespace CFSG.OddStandard.SmallF3.L33

private noncomputable def comapToConjActEquiv {G : Type*} [Group G]
    (H : Subgroup (ConjAct G)) :
    ↥(H.comap (ConjAct.toConjAct (G := G)).toMonoidHom) ≃ ↥H where
  toFun x := ⟨ConjAct.toConjAct x.1, by simpa using (Subgroup.mem_comap.mp x.2)⟩
  invFun y := ⟨ConjAct.ofConjAct y.1, by
    rw [Subgroup.mem_comap]
    simpa using y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

theorem card_class_mul_card_centralizer {G : Type*} [Group G] [Finite G] (a : G) :
    Nat.card {b : G // IsConj a b} * Nat.card (Subgroup.centralizer ({a} : Set G)) =
      Nat.card G := by
  classical
  have hclass : Nat.card {b : G // IsConj a b} =
      Nat.card (MulAction.orbit (ConjAct G) a) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun b => by
      rw [ConjAct.mem_orbit_conjAct]
      exact isConj_comm))
  have hstab : Nat.card (Subgroup.centralizer ({a} : Set G)) =
      Nat.card (MulAction.stabilizer (ConjAct G) a) := by
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    exact Nat.card_congr (comapToConjActEquiv (MulAction.stabilizer (ConjAct G) a))
  calc Nat.card {b : G // IsConj a b} * Nat.card (Subgroup.centralizer ({a} : Set G))
      = Nat.card (MulAction.orbit (ConjAct G) a) *
          Nat.card (MulAction.stabilizer (ConjAct G) a) := by rw [hclass, hstab]
    _ = Nat.card (MulAction.orbit (ConjAct G) a ×
          MulAction.stabilizer (ConjAct G) a) := (Nat.card_prod _ _).symm
    _ = Nat.card G :=
        Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) a)

theorem isConj_of_card_mul_card_centralizer {G : Type*} [Group G] [Finite G] (S : Set G)
    (hS : ∀ g s, s ∈ S → g * s * g⁻¹ ∈ S) {a : G} (ha : a ∈ S)
    (hcard : Nat.card S * Nat.card (Subgroup.centralizer ({a} : Set G)) = Nat.card G)
    {b : G} (hb : b ∈ S) : IsConj a b := by
  classical
  let C : Set G := {b : G | IsConj a b}
  have hCcard : Nat.card C * Nat.card (Subgroup.centralizer ({a} : Set G)) = Nat.card G :=
    card_class_mul_card_centralizer a
  have hcne : Nat.card (Subgroup.centralizer ({a} : Set G)) ≠ 0 := by
    haveI : Nonempty ↥(Subgroup.centralizer ({a} : Set G)) := ⟨1⟩
    exact Nat.card_pos.ne'
  have hCards : Nat.card C = Nat.card S := by
    refine mul_right_cancel₀ hcne ?_
    rw [hCcard, hcard]
  have hsub : C ⊆ S := by
    intro x hx
    have hx' : IsConj a x := by simpa only [C, Set.mem_setOf_eq] using hx
    obtain ⟨g, hg⟩ := isConj_iff.mp hx'
    rw [← hg]
    exact hS g a ha
  have hCS : C = S :=
    Set.Finite.eq_of_subset_of_card_le S.toFinite hsub (le_of_eq hCards.symm)
  have hbC : b ∈ C := by rwa [hCS]
  simpa only [C, Set.mem_setOf_eq] using hbC

end CFSG.OddStandard.SmallF3.L33
