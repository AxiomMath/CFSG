module

public import CFSG.GH74.Uniqueness.SU.SU13TB0Orbit
public import CFSG.GH74.Uniqueness.SU.SU4Defs

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G]

theorem card_modEq_one_of_free {D V : Subgroup G} (hDV : D ≤ normalizer (V : Set G))
    (hfix : ∀ d ∈ D, d ≠ 1 → ∀ v ∈ V, d * v * d⁻¹ = v → v = 1) :
    Nat.card V ≡ 1 [MOD Nat.card D] := by
  classical
  let _ : MulDistribMulAction D V :=
    { smul := fun t k => ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hDV t.2) k).mp k.2⟩
      one_smul := fun k => Subtype.ext (by change (1 : G) * k * 1⁻¹ = k; group)
      mul_smul := fun s t k => Subtype.ext (by
        change (s * t : G) * k * (s * t : G)⁻¹ = s * (t * k * (t : G)⁻¹) * (s : G)⁻¹
        group)
      smul_mul := fun t k l => Subtype.ext (by
        change (t : G) * (k * l) * (t : G)⁻¹ = (t * k * (t : G)⁻¹) * (t * l * (t : G)⁻¹)
        group)
      smul_one := fun t => Subtype.ext (by change (t : G) * 1 * (t : G)⁻¹ = 1; group) }
  let _ : Fintype D := Fintype.ofFinite D
  let _ : Fintype V := Fintype.ofFinite V
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group D V
  have hcard : ∀ d : D, Fintype.card (MulAction.fixedBy V d) =
      if d = 1 then Fintype.card V else 1 := by
    intro d
    by_cases hd : d = 1
    · subst hd
      simp only [↓reduceIte]
      exact Fintype.card_congr (Equiv.subtypeUnivEquiv (fun v : V => by
        rw [MulAction.mem_fixedBy]; exact one_smul D v))
    · simp only [hd, ↓reduceIte]
      refine Fintype.card_eq_one_iff.mpr ⟨⟨1, ?_⟩, fun x => ?_⟩
      · simp [MulAction.mem_fixedBy]
      · apply Subtype.ext
        have hx := x.2
        rw [MulAction.mem_fixedBy] at hx
        have h1 : ((d : G) * (x.1 : G) * (d : G)⁻¹) = (x.1 : G) := by
          have := congrArg Subtype.val hx
          exact this
        have h2 := hfix d d.2 (fun h => hd (Subtype.ext h)) x.1 x.1.2 h1
        exact Subtype.ext h2
  simp only [hcard] at hB
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const] at hB
  have h1 : (Finset.univ.filter fun d : D => d = 1).card = 1 := by
    refine Finset.card_eq_one.mpr ⟨1, ?_⟩
    ext d
    simp
  have h2 : (Finset.univ.filter fun d : D => ¬ d = 1).card = Fintype.card D - 1 := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, h1]
  rw [h1, h2] at hB
  simp only [smul_eq_mul, mul_one, one_mul] at hB
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hpos : 0 < Fintype.card D := Fintype.card_pos
  set c := Fintype.card D
  set o := Fintype.card (Quotient (MulAction.orbitRel D V))
  have h3 : Fintype.card V + c = o * c + 1 := by omega
  have h4 : (Fintype.card V + c) % c = (o * c + 1) % c := by rw [h3]
  rw [Nat.add_mod_right, Nat.mul_comm, Nat.mul_add_mod] at h4
  exact h4

end CFSG.GH74.Uniqueness.SU.SU13
