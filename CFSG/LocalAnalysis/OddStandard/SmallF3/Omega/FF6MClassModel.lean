module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MKinds
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFClassModelAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6m_not_mem_omega_of_mul_self_eq_pi (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {p : OGroup Q}
    (hp : p * p = piOrth Q) : p ∉ omegaGroup hQ :=
  fun hpΩ => t5_pi_not_sq (hQ := hQ) hdim hsgn ⟨⟨p, hpΩ⟩, hp⟩

theorem ff6m_invType_piOrth_mul (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {t : OGroup Q} (htt : t * t = 1) {r : ℕ} {α : ℤˣ}
    (ht : invType t = (r, α)) :
    invType (piOrth Q * t) = (6 - r, -1 * α * (-1) ^ (r * (6 - r))) := by
  have hd : invDim t = r := congrArg Prod.fst ht
  have hs : invSign t = α := congrArg Prod.snd ht
  have h := invType_piOrth_mul hQ htt
  rw [hdim, hsgn, hd, hs] at h
  exact h

theorem ff6m_kinds_of_involution (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {y : ProjOrth Q}
    {t : OGroup Q} (htt : t * t = 1) (hyt : toProj Q t = y) (hy1 : y ≠ 1) :
    KM0 (projOrthToProjSim Q y) ∨ KN1 (projOrthToProjSim Q y) ∨ KM2 (projOrthToProjSim Q y) ∨
      KM3 (projOrthToProjSim Q y) := by
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
  have hpi := ff6m_invType_piOrth_mul hQ hdim hsgn htt (r := invDim t) (α := invSign t) rfl
  have hcases : invDim t = 1 ∨ invDim t = 2 ∨ invDim t = 3 ∨ invDim t = 4 ∨ invDim t = 5 := by
    interval_cases invDim t <;> decide
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · exact Or.inr (Or.inr (Or.inl
      ⟨invSign t, y, rfl, hy1, t, htt, by rw [invType, h1], hyt⟩))
  · rcases Int.units_eq_one_or (invSign t) with hs | hs
    · refine Or.inr (Or.inl ⟨y, rfl, hy1, piOrth Q * t, piOrth_mul_mul_self htt, ?_, hptoy⟩)
      rw [hpi, h2, hs]
      decide
    · refine Or.inl ⟨y, rfl, hy1, piOrth Q * t, piOrth_mul_mul_self htt, ?_, hptoy⟩
      rw [hpi, h2, hs]
      decide
  · exact Or.inr (Or.inr (Or.inr
      ⟨invSign t, y, rfl, hy1, t, htt, by rw [invType, h3], hyt⟩))
  · rcases Int.units_eq_one_or (invSign t) with hs | hs
    · exact Or.inl ⟨y, rfl, hy1, t, htt, by rw [invType, h4, hs], hyt⟩
    · exact Or.inr (Or.inl ⟨y, rfl, hy1, t, htt, by rw [invType, h4, hs], hyt⟩)
  · have hpidim : invDim (piOrth Q * t) = 1 := by
      rw [show invDim (piOrth Q * t) = 6 - invDim t from congrArg Prod.fst hpi, h5]
    exact Or.inr (Or.inr (Or.inl
      ⟨invSign (piOrth Q * t), y, rfl, hy1, piOrth Q * t, piOrth_mul_mul_self htt,
        by rw [invType, hpidim], hptoy⟩))

theorem ff6m_model_classify (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {x : ProjSim Q} (hx : x * x = 1) :
    x = 1 ∨ KM0 x ∨ KN1 x ∨ KM2 x ∨ KM3 x ∨ KN2 x ∨ KM4 x := by
  by_cases hG : SimInGStar x
  · obtain ⟨y, hyx⟩ := hG
    have hy2 : y * y = 1 :=
      projOrthToProjSim_injective (by rw [map_mul, hyx, hx, map_one])
    obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
    have hyt : toProj Q t = y := ht
    have hg1 : t * t ∈ piGroup Q := by
      apply (QuotientGroup.eq_one_iff (t * t)).mp
      change toProj Q (t * t) = 1
      rw [map_mul, hyt]
      exact hy2
    rcases mem_piGroup_iff.mp hg1 with htt | htt
    · by_cases hy1 : y = 1
      · left
        rw [← hyx, hy1, map_one]
      · rw [← hyx]
        rcases ff6m_kinds_of_involution hQ hdim hsgn htt hyt hy1 with h0 | h1 | h2 | h3
        · exact Or.inr (Or.inl h0)
        · exact Or.inr (Or.inr (Or.inl h1))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3))))
    · by_cases hy1 : y = 1
      · exfalso
        have hmem : t ∈ piGroup Q := (QuotientGroup.eq_one_iff t).mp (hyt.trans hy1)
        rcases mem_piGroup_iff.mp hmem with h | h
        · rw [h, one_mul] at htt
          exact piOrth_ne_one (by omega) htt.symm
        · rw [h, piOrth_mul_self] at htt
          exact piOrth_ne_one (by omega) htt.symm
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨y, hyx, hy1, hy2, t, htt, hyt⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hG)))))

theorem ff6m_KN2_ne_one {x : ProjSim Q} (h : KN2 x) : x ≠ 1 := by
  obtain ⟨y, hyx, hy1, -⟩ := h
  intro hx
  exact hy1 (projOrthToProjSim_injective (by rw [hyx, hx, map_one]))

theorem ff6m_KM0_inner (hQ : Q.Nondegenerate) {x : ProjSim Q} (h : KM0 x) :
    SimInOmegaStar hQ x := by
  obtain ⟨y, hyx, hy1, t, htt, hty, htoy⟩ := h
  refine ⟨y, ?_, hyx⟩
  rw [mem_omegaProj_iff]
  refine ⟨t, ?_, htoy⟩
  rw [involution_mem_omegaGroup_iff hQ htt]
  exact ⟨by rw [show invDim t = 4 from congrArg Prod.fst hty]; decide,
    by rw [show invSign t = 1 from congrArg Prod.snd hty,
      show invDim t = 4 from congrArg Prod.fst hty]; decide⟩

theorem ff6m_KM3_not_inner (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {x : ProjSim Q} (h : KM3 x) : ¬ SimInOmegaStar hQ x := by
  rintro ⟨y', hy'om, hy'x⟩
  obtain ⟨_, y, hyx, hy1, t, htt, hty, htoy⟩ := h
  have hyy : y' = y := projOrthToProjSim_injective (by rw [hy'x, hyx])
  have hyom : y ∈ omegaProj hQ := hyy ▸ hy'om
  have hodd : Odd (invDim t) := by
    rw [show invDim t = 3 from congrArg Prod.fst hty]
    decide
  exact not_mem_omegaProj_of_odd_invDim hQ hdim hyom htt htoy hodd

theorem ff6m_involution_kind (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {u : ↥(omegaProj hQ)} (hu : u * u = 1) (hu1 : u ≠ 1) :
    KM0 (projOrthToProjSim Q (u : ProjOrth Q)) := by
  obtain ⟨g, hg, hgu⟩ := (mem_omegaProj_iff hQ).mp u.2
  have hu1' : (u : ProjOrth Q) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hgg1 : toProj Q (g * g) = 1 := by
    rw [map_mul, hgu]
    exact congrArg Subtype.val hu
  have hgg : g * g = 1 := by
    rcases mem_piGroup_iff.mp ((QuotientGroup.eq_one_iff (g * g)).mp hgg1) with h | h
    · exact h
    · exact absurd hg (ff6m_not_mem_omega_of_mul_self_eq_pi hQ hdim hsgn h)
  rcases t5_omega_involution_type (hQ := hQ) hdim hgg hg with h0 | h2 | h4 | h6
  · exfalso
    have : g = 1 := (invDim_eq_zero_iff hgg).mp (congrArg Prod.fst h0)
    exact hu1' (by rw [← hgu, this, map_one])
  · refine simHasType_projOrthToProjSim ⟨hu1', piOrth Q * g, piOrth_mul_mul_self hgg, ?_, ?_⟩
    · rw [ff6m_invType_piOrth_mul hQ hdim hsgn hgg h2]
      decide
    · rw [map_mul, toProj_piOrth, one_mul, hgu]
  · exact simHasType_projOrthToProjSim ⟨hu1', g, hgg, h4, hgu⟩
  · exfalso
    have : g = piOrth Q :=
      (invDim_eq_finrank_iff hgg).mp (by rw [hdim]; exact congrArg Prod.fst h6)
    exact hu1' (by rw [← hgu, this, toProj_piOrth])

theorem ff6m_conj_involutions (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {u u' : ↥(omegaProj hQ)} (hu : u * u = 1) (hu' : u' * u' = 1)
    (hu1 : u ≠ 1) (hu1' : u' ≠ 1) : ∃ a : ↥(omegaProj hQ), a * u * a⁻¹ = u' :=
  conj_of_simHasType_even (r := 4) (α := 1) hQ hdim (ff6m_involution_kind hQ hdim hsgn hu hu1)
    (ff6m_involution_kind hQ hdim hsgn hu' hu1') (by decide) (by decide)

end CFSG.OddStandard.SmallF3.Omega
