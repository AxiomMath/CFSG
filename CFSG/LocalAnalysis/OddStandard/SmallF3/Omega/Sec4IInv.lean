module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Det
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem exists_even_lift_seven (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    (hσ : quadSign Q = 1) {x : ProjOrth Q} (hxx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ t : OGroup Q, t * t = 1 ∧ toProj Q t = x ∧
      (invDim t = 2 ∨ invDim t = 4 ∨ invDim t = 6) := by
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
      exact (by decide : ¬ ((1 : (ZMod 3)ˣ) = (-1) ^ 7)) hd
  have hle : invDim g ≤ 7 := hdim ▸ invDim_le g
  have h0 : invDim g ≠ 0 := fun h => hx1 (by rw [(invDim_eq_zero_iff hgg1).mp h, map_one])
  have h7 : invDim g ≠ 7 := fun h =>
    hx1 (by rw [(invDim_eq_finrank_iff hgg1).mp (by rw [h, hdim]), toProj_piOrth])
  by_cases hev : invDim g = 2 ∨ invDim g = 4 ∨ invDim g = 6
  · exact ⟨g, hgg1, rfl, hev⟩
  · refine ⟨piOrth Q * g, piOrth_mul_mul_self hgg1, ?_, ?_⟩
    · rw [map_mul, toProj_piOrth, one_mul]
    · have h1 : invDim (piOrth Q * g) = Module.finrank (ZMod 3) V - invDim g :=
        congrArg Prod.fst (invType_piOrth_mul_of_odd hQ hgg1 (by rw [hdim]; decide) hσ)
      rw [h1, hdim]
      omega

theorem hasType_of_involution_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) (hσ : quadSign Q = 1) {x : ProjOrth Q}
    (hxx : x * x = 1) (hx1 : x ≠ 1) :
    HasType x 2 1 ∨ HasType x 2 (-1) ∨ HasType x 4 1 ∨ HasType x 4 (-1) ∨ HasType x 6 1 ∨
      HasType x 6 (-1) := by
  obtain ⟨t, htt, hxt, hr⟩ := exists_even_lift_seven hQ hdim hσ hxx hx1
  have hty : HasType x (invDim t) (invSign t) := ⟨hx1, t, htt, rfl, hxt⟩
  rcases Int.units_eq_one_or (invSign t) with hs | hs <;> rcases hr with hr | hr | hr <;>
    rw [hr, hs] at hty
  · exact Or.inl hty
  · exact Or.inr (Or.inr (Or.inl hty))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hty))))
  · exact Or.inr (Or.inl hty)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hty)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hty))))

theorem eq_of_hasType_seven (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    {x : ProjOrth Q} {r r' : ℕ} {α α' : ℤˣ} (h : HasType x r α) (h' : HasType x r' α')
    (hr : r = 2 ∨ r = 4 ∨ r = 6) (hr' : r' = 2 ∨ r' = 4 ∨ r' = 6) : r = r' ∧ α = α' := by
  obtain ⟨-, t, htt, hty, hxt⟩ := h
  obtain ⟨-, t', htt', hty', hxt'⟩ := h'
  have hmem : t⁻¹ * t' ∈ piGroup Q := QuotientGroup.eq.mp (hxt.trans hxt'.symm)
  rcases mem_piGroup_iff.mp hmem with h1 | h1
  · have h2 : t = t' := inv_mul_eq_one.mp h1
    rw [h2] at hty
    have h3 := hty.symm.trans hty'
    exact ⟨(Prod.ext_iff.mp h3).1, (Prod.ext_iff.mp h3).2⟩
  · exfalso
    have h2 : t' = piOrth Q * t := by
      rw [← mul_piOrth_comm t, ← h1]
      group
    have h3 := congrArg Prod.fst (hty'.symm.trans (h2 ▸ invType_piOrth_mul hQ htt))
    have h4 : invDim t = r := congrArg Prod.fst hty
    simp only [h4, hdim] at h3
    omega

theorem exists_hasType_seven (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    {r : ℕ} (hr : r = 2 ∨ r = 4 ∨ r = 6) (α : ℤˣ) : ∃ x : ProjOrth Q, HasType x r α := by
  obtain ⟨t, htt, hty⟩ := (exists_involution_of_type hQ r α).mpr
    ⟨by omega, fun h => by omega, fun h => by omega⟩
  refine ⟨toProj Q t, ?_, t, htt, hty, rfl⟩
  intro h1
  have h2 : t ∈ piGroup Q := (QuotientGroup.eq_one_iff _).mp h1
  have h3 : invDim t = r := congrArg Prod.fst hty
  rcases mem_piGroup_iff.mp h2 with h4 | h4
  · rw [(invDim_eq_zero_iff htt).mpr h4] at h3
    omega
  · rw [(invDim_eq_finrank_iff htt).mpr h4, hdim] at h3
    omega

theorem hasType_mem_omegaProj_iff_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) {x : ProjOrth Q} {r : ℕ} {α : ℤˣ}
    (h : HasType x r α) (hr : r = 2 ∨ r = 4 ∨ r = 6) :
    x ∈ omegaProj hQ ↔ (r = 2 ∧ α = -1) ∨ (r = 4 ∧ α = 1) ∨ (r = 6 ∧ α = -1) := by
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
      rcases hr with rfl | rfl | rfl
      · left
        exact ⟨rfl, by simpa using h3⟩
      · right
        left
        exact ⟨rfl, by simpa using h3⟩
      · right
        right
        exact ⟨rfl, h3.trans (by decide)⟩
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
      rcases hr with rfl | rfl | rfl <;> exact absurd h5 (by decide)
  · intro hx
    refine (mem_omegaProj_iff hQ).mpr ⟨t, hcrit.mpr ⟨?_, ?_⟩, hxt⟩
    · rcases hr with rfl | rfl | rfl <;> decide
    · rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

end CFSG.OddStandard.SmallF3.Omega
