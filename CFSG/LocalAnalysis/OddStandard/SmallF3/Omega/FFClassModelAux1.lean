module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem toProj_eq_or_eq_piOrth {a b : OGroup Q} (h : toProj Q a = toProj Q b) :
    a = b ∨ a = piOrth Q * b := by
  have hmem : a / b ∈ piGroup Q := by
    refine (QuotientGroup.eq_iff_div_mem (N := piGroup Q)).mp ?_
    change toProj Q a = toProj Q b
    exact h
  rcases mem_piGroup_iff.mp hmem with h1 | h1
  · left
    rw [div_eq_mul_inv] at h1
    exact mul_inv_eq_one.mp h1
  · right
    rw [div_eq_mul_inv] at h1
    rw [← h1]
    group

theorem not_mem_omegaProj_of_odd_invDim (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) {y : ProjOrth Q} (hy : y ∈ omegaProj hQ)
    {t : OGroup Q} (htt : t * t = 1) (hyt : toProj Q t = y) (hodd : Odd (invDim t)) : False := by
  obtain ⟨g, hg, hgy⟩ := (mem_omegaProj_iff hQ).mp hy
  have hgt : toProj Q g = toProj Q t := by rw [hgy, hyt]
  have hfin : invDim (piOrth Q * t) = 6 - invDim t := by
    have h := congrArg Prod.fst (invType_piOrth_mul hQ htt)
    simp only [invType] at h
    simpa only [hdim] using h
  rcases toProj_eq_or_eq_piOrth hgt with h1 | h1
  · have htΩ : t ∈ omegaGroup hQ := h1 ▸ hg
    exact (Nat.not_odd_iff_even.mpr ((involution_mem_omegaGroup_iff hQ htt).mp htΩ).1) hodd
  · have hptΩ : piOrth Q * t ∈ omegaGroup hQ := h1 ▸ hg
    have hptt : (piOrth Q * t) * (piOrth Q * t) = 1 := piOrth_mul_mul_self htt
    have hev : Even (invDim (piOrth Q * t)) :=
      ((involution_mem_omegaGroup_iff hQ hptt).mp hptΩ).1
    have hodd' : Odd (invDim (piOrth Q * t)) := by
      rw [hfin]
      exact Nat.Even.sub_odd (by rw [← hdim]; exact invDim_le t) (by decide) hodd
    exact (Nat.not_odd_iff_even.mpr hev) hodd'

theorem simHasType_ne_one {x : ProjSim Q} {r : ℕ} {α : ℤˣ} (h : SimHasType x r α) :
    x ≠ 1 := by
  rintro hx
  obtain ⟨y, hyx, hy1, -⟩ := h
  exact hy1 (projOrthToProjSim_injective (by rw [hyx, hx, map_one]))

theorem simHasType_sq {x : ProjSim Q} {r : ℕ} {α : ℤˣ} (h : SimHasType x r α) :
    x * x = 1 := by
  obtain ⟨y, hyx, hy1, t, htt, hty, htoy⟩ := h
  rw [← hyx, ← map_mul, ← htoy, ← map_mul, htt]
  simp

theorem km0123_of_involution (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    {y : ProjOrth Q} {t : OGroup Q} (htt : t * t = 1) (hyt : toProj Q t = y)
    (hy1 : y ≠ 1) :
    KM0 (projOrthToProjSim Q y) ∨ KM1 (projOrthToProjSim Q y) ∨
      KM2 (projOrthToProjSim Q y) ∨ KM3 (projOrthToProjSim Q y) := by
  have ht1 : t ≠ 1 := by
    intro h
    exact hy1 (by rw [← hyt, h, map_one])
  have htpi : t ≠ piOrth Q := by
    intro h
    exact hy1 (by rw [← hyt, h, toProj_piOrth])
  have hpos : 0 < invDim t := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact ht1 ((invDim_eq_zero_iff htt).mp h0)
  have hlt : invDim t < 6 := by
    have hle : invDim t ≤ 6 := by rw [← hdim]; exact invDim_le t
    refine lt_of_le_of_ne hle ?_
    intro h6
    exact htpi ((invDim_eq_finrank_iff htt).mp (by rw [hdim]; exact h6))
  have hptoy : toProj Q (piOrth Q * t) = y := by
    rw [map_mul, toProj_piOrth, one_mul, hyt]
  have hpi : invType (piOrth Q * t) =
      (6 - invDim t, (-1) ^ invDim t * invSign t) := by
    have h := invType_piOrth_mul_of_even_plus hQ htt (by rw [hdim]; decide) hsgn
    simpa only [hdim] using h
  have hcases : invDim t = 1 ∨ invDim t = 2 ∨ invDim t = 3 ∨ invDim t = 4 ∨
      invDim t = 5 := by
    interval_cases invDim t <;> decide
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · exact Or.inr (Or.inr (Or.inl
      ⟨invSign t, y, rfl, hy1, t, htt, by rw [invType, h1], hyt⟩))
  · rcases Int.units_eq_one_or (invSign t) with hs | hs
    · refine Or.inl ⟨y, rfl, hy1, piOrth Q * t, piOrth_mul_mul_self htt, ?_, hptoy⟩
      rw [hpi, h2, hs]
      decide
    · exact Or.inr (Or.inl
        ⟨y, rfl, hy1, t, htt, by rw [invType, h2, hs], hyt⟩)
  · exact Or.inr (Or.inr (Or.inr
      ⟨invSign t, y, rfl, hy1, t, htt, by rw [invType, h3], hyt⟩))
  · rcases Int.units_eq_one_or (invSign t) with hs | hs
    · exact Or.inl ⟨y, rfl, hy1, t, htt, by rw [invType, h4, hs], hyt⟩
    · refine Or.inr (Or.inl
        ⟨y, rfl, hy1, piOrth Q * t, piOrth_mul_mul_self htt, ?_, hptoy⟩)
      rw [hpi, h4, hs]
      decide
  · have hpidim : invDim (piOrth Q * t) = 1 := by
      rw [show invDim (piOrth Q * t) = 6 - invDim t from congrArg Prod.fst hpi, h5]
    exact Or.inr (Or.inr (Or.inl
      ⟨invSign (piOrth Q * t), y, rfl, hy1, piOrth Q * t, piOrth_mul_mul_self htt,
        by rw [invType, hpidim], hptoy⟩))

theorem conj_of_simHasType_even (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) {u u' : ↥(omegaProj hQ)} {r : ℕ} {α : ℤˣ}
    (hu : SimHasType (projOrthToProjSim Q (u : ProjOrth Q)) r α)
    (hu' : SimHasType (projOrthToProjSim Q (u' : ProjOrth Q)) r α)
    (hr : Even r) (hs : α = (-1) ^ (r / 2)) :
    ∃ a : ↥(omegaProj hQ), a * u * a⁻¹ = u' := by
  obtain ⟨y, hyx, hy1, t, htt, hty, htoy⟩ := hu
  obtain ⟨y', hyx', hy1', t', htt', hty', htoy'⟩ := hu'
  have hyu : y = (u : ProjOrth Q) := projOrthToProjSim_injective hyx
  have hyu' : y' = (u' : ProjOrth Q) := projOrthToProjSim_injective hyx'
  have htu : (u : ProjOrth Q) = toProj Q t := (htoy.trans hyu).symm
  have htu' : (u' : ProjOrth Q) = toProj Q t' := (htoy'.trans hyu').symm
  have hmem : t ∈ omegaGroup hQ := by
    rw [involution_mem_omegaGroup_iff hQ htt]
    exact ⟨by rw [show invDim t = r from congrArg Prod.fst hty]; exact hr,
      by rw [show invSign t = α from congrArg Prod.snd hty,
        show invDim t = r from congrArg Prod.fst hty]; exact hs⟩
  have hmem' : t' ∈ omegaGroup hQ := by
    rw [involution_mem_omegaGroup_iff hQ htt']
    exact ⟨by rw [show invDim t' = r from congrArg Prod.fst hty']; exact hr,
      by rw [show invSign t' = α from congrArg Prod.snd hty',
        show invDim t' = r from congrArg Prod.fst hty']; exact hs⟩
  obtain ⟨c, hc, hcj⟩ := exists_mem_omegaGroup_conj hQ (by rw [hdim]; norm_num) htt htt'
    (hty.trans hty'.symm)
  refine ⟨⟨toProj Q c, (mem_omegaProj_iff hQ).mpr ⟨c, hc, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  change (toProj Q c) * (u : ProjOrth Q) * (toProj Q c)⁻¹ = (u' : ProjOrth Q)
  rw [htu, htu', ← map_mul, ← map_inv, ← map_mul, hcj]

end CFSG.OddStandard.SmallF3.Omega
