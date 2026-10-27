module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem y7a_card_lab_img {G : Type} [Group G] [Finite G] {n : ℕ} {V : Subgroup G}
    (lab : G → Fin n) {U S : Set G} (hSU : S ⊆ U)
    (hlab : ∀ u ∈ U, ∀ u' ∈ U, lab u = lab u' ↔ u⁻¹ * u' ∈ V)
    (hSV : ∀ x ∈ S, ∀ v ∈ V, x * v ∈ S) {k : ℕ}
    (hS : Nat.card ↥S = k * Nat.card ↥V) : Nat.card ↥(lab '' S) = k := by
  classical
  let jf : ↥S → ↥(lab '' S) := fun x => ⟨lab x.1, x.1, x.2, rfl⟩
  have hrep : ∀ j : ↥(lab '' S), ∃ x : ↥S, jf x = j := by
    rintro ⟨b, hb⟩
    rcases hb with ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  let rep : ↥(lab '' S) → ↥S := fun j => Classical.choose (hrep j)
  have rep_spec : ∀ j, jf (rep j) = j := fun j => Classical.choose_spec (hrep j)
  have hlab_rep : ∀ j, lab (rep j).1 = j.1 := fun j => congrArg Subtype.val (rep_spec j)
  let φ : ↥(lab '' S) × ↥V → ↥S :=
    fun p => ⟨(rep p.1).1 * p.2.1, hSV (rep p.1).1 (rep p.1).2 p.2.1 p.2.2⟩
  let ψ : ↥S → ↥(lab '' S) × ↥V :=
    fun x => (jf x, ⟨(rep (jf x)).1⁻¹ * x.1,
      (hlab (rep (jf x)).1 (hSU (rep (jf x)).2) x.1 (hSU x.2)).1 (hlab_rep (jf x))⟩)
  have hφψ : ∀ x, φ (ψ x) = x := by
    intro x
    apply Subtype.ext
    show (rep (jf x)).1 * ((rep (jf x)).1⁻¹ * x.1) = x.1
    group
  have hψφ : ∀ p, ψ (φ p) = p := by
    rintro ⟨j, v⟩
    have hfirst : jf (φ (j, v)) = j := by
      apply Subtype.ext
      show lab ((rep j).1 * v.1) = j.1
      rw [← hlab_rep j]
      exact ((hlab (rep j).1 (hSU (rep j).2) ((rep j).1 * v.1)
        (hSU (hSV (rep j).1 (rep j).2 v.1 v.2))).2 (by
          have hv : (rep j).1⁻¹ * ((rep j).1 * v.1) = v.1 := by group
          rw [hv]
          exact v.2)).symm
    apply Prod.ext
    · exact hfirst
    · apply Subtype.ext
      show (rep (jf (φ (j, v)))).1⁻¹ * ((rep j).1 * v.1) = v.1
      rw [hfirst]
      group
  have he : ↥S ≃ ↥(lab '' S) × ↥V :=
    { toFun := ψ, invFun := φ, left_inv := hφψ, right_inv := hψφ }
  have hmain : Nat.card ↥S = Nat.card ↥(lab '' S) * Nat.card ↥V := by
    rw [Nat.card_congr he, Nat.card_prod]
  have hVpos : 0 < Nat.card ↥V := by
    haveI : Nonempty ↥V := ⟨⟨1, V.one_mem⟩⟩
    exact Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_right hVpos (hS.symm.trans hmain)).symm

end CFSG.OddStandard.HigherRank.YamadaG23
