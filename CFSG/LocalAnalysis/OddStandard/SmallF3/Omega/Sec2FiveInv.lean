module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Det

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem exists_even_lift_five (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5)
    (hσ : quadSign Q = 1) {x : ProjOrth Q} (hxx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ t : OGroup Q, t * t = 1 ∧ toProj Q t = x ∧ (invDim t = 2 ∨ invDim t = 4) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) x
  have hgg : g * g ∈ piGroup Q := by
    have h : toProj Q (g * g) = 1 := by
      rw [map_mul]
      exact hxx
    exact (QuotientGroup.eq_one_iff _).mp h
  have hgg1 : g * g = 1 := by
    rcases mem_piGroup_iff.mp hgg with h | h
    · exact h
    · exfalso
      have hd := congrArg (QuadraticMap.orthogonalDet Q) h
      rw [map_mul, orthogonalDet_piOrth, hdim] at hd
      have hsq : ∀ u : (ZMod 3)ˣ, u * u = 1 := by decide
      rw [hsq] at hd
      exact (by decide : ¬ ((1 : (ZMod 3)ˣ) = (-1) ^ 5)) hd
  have hle : invDim g ≤ 5 := hdim ▸ invDim_le g
  have h0 : invDim g ≠ 0 := fun h => hx1 (by rw [(invDim_eq_zero_iff hgg1).mp h, map_one])
  have h5 : invDim g ≠ 5 := fun h =>
    hx1 (by rw [(invDim_eq_finrank_iff hgg1).mp (by rw [h, hdim]), toProj_piOrth])
  by_cases hev : invDim g = 2 ∨ invDim g = 4
  · exact ⟨g, hgg1, rfl, hev⟩
  · refine ⟨piOrth Q * g, piOrth_mul_mul_self hgg1, ?_, ?_⟩
    · rw [map_mul, toProj_piOrth, one_mul]
    · have h1 : invDim (piOrth Q * g) = Module.finrank (ZMod 3) V - invDim g :=
        congrArg Prod.fst (invType_piOrth_mul_of_odd hQ hgg1 (by rw [hdim]; decide) hσ)
      rw [h1, hdim]
      omega

theorem hasType_of_involution_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1) {x : ProjOrth Q}
    (hxx : x * x = 1) (hx1 : x ≠ 1) :
    HasType x 4 1 ∨ HasType x 2 (-1) ∨ HasType x 4 (-1) ∨ HasType x 2 1 := by
  obtain ⟨t, htt, hxt, hr⟩ := exists_even_lift_five hQ hdim hσ hxx hx1
  have hty : HasType x (invDim t) (invSign t) := ⟨hx1, t, htt, rfl, hxt⟩
  rcases Int.units_eq_one_or (invSign t) with hs | hs <;> rcases hr with hr | hr <;>
    rw [hr, hs] at hty
  · exact Or.inr (Or.inr (Or.inr hty))
  · exact Or.inl hty
  · exact Or.inr (Or.inl hty)
  · exact Or.inr (Or.inr (Or.inl hty))

theorem hasType_mem_omegaProj_iff_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) {x : ProjOrth Q} {r : ℕ} {α : ℤˣ}
    (h : HasType x r α) (hr : r = 2 ∨ r = 4) :
    x ∈ omegaProj hQ ↔ (r = 4 ∧ α = 1) ∨ (r = 2 ∧ α = -1) := by
  obtain ⟨-, t, htt, hty, hxt⟩ := h
  have hd : invDim t = r := congrArg Prod.fst hty
  have hs : invSign t = α := congrArg Prod.snd hty
  have hcrit := involution_mem_omegaGroup_iff hQ htt
  rw [hd, hs] at hcrit
  constructor
  · intro hx
    obtain ⟨g, hg, hgx⟩ := (mem_omegaProj_iff hQ).mp hx
    have hmem : g⁻¹ * t ∈ piGroup Q := QuotientGroup.eq.mp (hgx.trans hxt.symm)
    rcases mem_piGroup_iff.mp hmem with h1 | h1
    · have h2 : t ∈ omegaGroup hQ := by
        rw [← inv_mul_eq_one.mp h1]
        exact hg
      obtain ⟨-, h3⟩ := hcrit.mp h2
      rcases hr with rfl | rfl
      · right
        exact ⟨rfl, by simpa using h3⟩
      · left
        exact ⟨rfl, by simpa using h3⟩
    · exfalso
      have h2 : g = piOrth Q * t := by
        have ht : t = g * piOrth Q := by
          rw [← h1]
          group
        calc g = g * (piOrth Q * piOrth Q) := by rw [piOrth_mul_self, mul_one]
          _ = (g * piOrth Q) * piOrth Q := by rw [mul_assoc]
          _ = t * piOrth Q := by rw [← ht]
          _ = piOrth Q * t := mul_piOrth_comm t
      have h3 := (involution_mem_omegaGroup_iff hQ (piOrth_mul_mul_self htt)).mp (h2 ▸ hg)
      have h4 : invDim (piOrth Q * t) = Module.finrank (ZMod 3) V - invDim t :=
        congrArg Prod.fst (invType_piOrth_mul hQ htt)
      have h5 := h3.1
      rw [h4, hdim, hd] at h5
      rcases hr with rfl | rfl <;> exact absurd h5 (by decide)
  · intro hx
    refine (mem_omegaProj_iff hQ).mpr ⟨t, hcrit.mpr ⟨?_, ?_⟩, hxt⟩
    · rcases hr with rfl | rfl <;> decide
    · rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem natCard_centralizer_involution_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1) {x : ProjOrth Q}
    (hxx : x * x = 1) (hx1 : x ≠ 1) :
    (HasType x 4 1 ∧ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 1152) ∨
      (HasType x 2 (-1) ∧ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 192) ∨
      (HasType x 4 (-1) ∧ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 1440) ∨
      (HasType x 2 1 ∧ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 96) := by
  rcases hasType_of_involution_five hQ hdim hσ hxx hx1 with h | h | h | h
  · exact Or.inl ⟨h, natCard_centralizer_hasType_four_plus hQ hdim h⟩
  · exact Or.inr (Or.inl ⟨h, natCard_centralizer_hasType_two_minus hQ hdim h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, natCard_centralizer_hasType_four_minus hQ hdim h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h, natCard_centralizer_hasType_two_plus hQ hdim h⟩))

theorem hasType_four_plus_iff_natCard_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1) {x : ProjOrth Q}
    (hxx : x * x = 1) (hx1 : x ≠ 1) :
    HasType x 4 1 ↔ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 1152 := by
  refine ⟨natCard_centralizer_hasType_four_plus hQ hdim, fun h => ?_⟩
  rcases natCard_centralizer_involution_five hQ hdim hσ hxx hx1 with h1 | h1 | h1 | h1
  · exact h1.1
  all_goals omega

theorem hasType_two_minus_iff_natCard_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1) {x : ProjOrth Q}
    (hxx : x * x = 1) (hx1 : x ≠ 1) :
    HasType x 2 (-1) ↔ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 192 := by
  refine ⟨natCard_centralizer_hasType_two_minus hQ hdim, fun h => ?_⟩
  rcases natCard_centralizer_involution_five hQ hdim hσ hxx hx1 with h1 | h1 | h1 | h1
  · omega
  · exact h1.1
  all_goals omega

theorem hasType_four_minus_iff_natCard_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1) {x : ProjOrth Q}
    (hxx : x * x = 1) (hx1 : x ≠ 1) :
    HasType x 4 (-1) ↔ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 1440 := by
  refine ⟨natCard_centralizer_hasType_four_minus hQ hdim, fun h => ?_⟩
  rcases natCard_centralizer_involution_five hQ hdim hσ hxx hx1 with h1 | h1 | h1 | h1
  · omega
  · omega
  · exact h1.1
  · omega

theorem hasType_two_plus_iff_natCard_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (hσ : quadSign Q = 1) {x : ProjOrth Q}
    (hxx : x * x = 1) (hx1 : x ≠ 1) :
    HasType x 2 1 ↔ Nat.card (Subgroup.centralizer ({x} : Set (ProjOrth Q))) = 96 := by
  refine ⟨natCard_centralizer_hasType_two_plus hQ hdim, fun h => ?_⟩
  rcases natCard_centralizer_involution_five hQ hdim hσ hxx hx1 with h1 | h1 | h1 | h1
  · omega
  · omega
  · omega
  · exact h1.1

end CFSG.OddStandard.SmallF3.Omega
