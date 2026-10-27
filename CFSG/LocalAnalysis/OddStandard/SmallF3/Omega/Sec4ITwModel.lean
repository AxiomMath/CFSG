module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec4I_blockInr_piOrth_comm (hQ : Q.Nondegenerate) {x : OGroup Q} (hx : x * x = 1)
    (b : OGroup (Q.restrict (commSp (piOrth Q * x)))) :
    blockInr (piOrth_mul_mul_self hx) b * x = x * blockInr (piOrth_mul_mul_self hx) b := by
  have h1 : blockInr (piOrth_mul_mul_self hx) b * (piOrth Q * x) =
      (piOrth Q * x) * blockInr (piOrth_mul_mul_self hx) b :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (blockInr_mem_centralizer hQ (piOrth_mul_mul_self hx) b)
  have h2 : piOrth Q * (blockInr (piOrth_mul_mul_self hx) b * x) =
      piOrth Q * (x * blockInr (piOrth_mul_mul_self hx) b) := by
    calc piOrth Q * (blockInr (piOrth_mul_mul_self hx) b * x)
        = (piOrth Q * blockInr (piOrth_mul_mul_self hx) b) * x := by group
      _ = (blockInr (piOrth_mul_mul_self hx) b * piOrth Q) * x := by rw [mul_piOrth_comm]
      _ = blockInr (piOrth_mul_mul_self hx) b * (piOrth Q * x) := by group
      _ = (piOrth Q * x) * blockInr (piOrth_mul_mul_self hx) b := h1
      _ = piOrth Q * (x * blockInr (piOrth_mul_mul_self hx) b) := by group
  exact mul_left_cancel h2

theorem sec4I_twist_elt_two (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    {x : OGroup Q} (hx : x * x = 1) (hxd : invDim x = 2) :
    ∃ w : OGroup Q, w * w = 1 ∧ w * x = x * w ∧ invType w = (4, 1) ∧
      invType (w * x) = invType x := by
  have hx' : (piOrth Q * x) * (piOrth Q * x) = 1 := piOrth_mul_mul_self hx
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) x
  have hU2 : Module.finrank (ZMod 3) ↥(commSp x) = 2 := hxd
  have hF5 : Module.finrank (ZMod 3) ↥(commSp (piOrth Q * x)) = 5 := by
    rw [commSp_piOrth_mul hx]
    omega
  have hQU' := nondegenerate_restrict_commSp hQ hx'
  obtain ⟨u₂, hu₂, hu₂t⟩ := (exists_involution_of_type hQU' 2 (invSign x)).mpr
    ⟨by omega, fun h => by omega, fun h => by omega⟩
  have ht't' : blockInr hx' u₂ * blockInr hx' u₂ = 1 := by rw [← map_mul, hu₂, map_one]
  have hxt' := sec4I_blockInr_piOrth_comm hQ hx u₂
  have ht'type : invType (blockInr hx' u₂) = (2, invSign x) := by
    rw [invType_blockInr hQ hx' hu₂, hu₂t]
  have horth : ∀ v ∈ commSp x, ∀ w ∈ commSp (blockInr hx' u₂), QuadraticMap.polar Q v w = 0 := by
    intro v hv w hw
    have hw' : w ∈ fixSp x := by
      have := commSp_blockInr_le hx' u₂ hw
      rwa [commSp_piOrth_mul hx] at this
    rw [QuadraticMap.polar_comm]
    exact polar_fixSp_commSp hx hw' hv
  have hww : (x * blockInr hx' u₂) * (x * blockInr hx' u₂) = 1 :=
    mul_mul_self_of_orth hQ hx ht't' horth
  have hwx : (x * blockInr hx' u₂) * x = x * (x * blockInr hx' u₂) := by rw [mul_assoc, hxt']
  have hwx' : (x * blockInr hx' u₂) * x = blockInr hx' u₂ := by
    rw [hwx, ← mul_assoc, hx, one_mul]
  refine ⟨x * blockInr hx' u₂, hww, hwx, ?_, ?_⟩
  · have h1 : invDim (blockInr hx' u₂) = 2 := congrArg Prod.fst ht'type
    have h2 : invSign (blockInr hx' u₂) = invSign x := congrArg Prod.snd ht'type
    rw [invType_mul_of_orth hQ hx ht't' horth, h1, h2, hxd, Int.units_mul_self]
    decide
  · rw [hwx', ht'type]
    exact Prod.ext hxd.symm rfl

theorem sec4I_twist_elt_four (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    {x : OGroup Q} (hx : x * x = 1) (hxd : invDim x = 4) :
    ∃ w : OGroup Q, w * w = 1 ∧ w * x = x * w ∧ invType w = (4, 1) ∧
      invType (w * x) = invType x := by
  have hx' : (piOrth Q * x) * (piOrth Q * x) = 1 := piOrth_mul_mul_self hx
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) x
  have hU4 : Module.finrank (ZMod 3) ↥(commSp x) = 4 := hxd
  have hF3 : Module.finrank (ZMod 3) ↥(commSp (piOrth Q * x)) = 3 := by
    rw [commSp_piOrth_mul hx]
    omega
  have hQU := nondegenerate_restrict_commSp hQ hx
  have hQU' := nondegenerate_restrict_commSp hQ hx'
  obtain ⟨u₁, hu₁, hu₁t⟩ := (exists_involution_of_type hQU 2 1).mpr
    ⟨by omega, fun h => by omega, fun h => by omega⟩
  obtain ⟨u₂, hu₂, hu₂t⟩ := (exists_involution_of_type hQU' 2 1).mpr
    ⟨by omega, fun h => by omega, fun h => by omega⟩
  have hu₁d : invDim u₁ = 2 := congrArg Prod.fst hu₁t
  have hu₁s : invSign u₁ = 1 := congrArg Prod.snd hu₁t
  have h11 : blockInr hx u₁ * blockInr hx u₁ = 1 := by rw [← map_mul, hu₁, map_one]
  have h22 : blockInr hx' u₂ * blockInr hx' u₂ = 1 := by rw [← map_mul, hu₂, map_one]
  have horth := polar_blockInr_piOrth_mul hx u₁ u₂
  have hgh : (blockInr hx u₁ * blockInr hx' u₂) * (blockInr hx u₁ * blockInr hx' u₂) = 1 :=
    mul_mul_self_of_orth hQ h11 h22 horth
  have hxt₁ : blockInr hx u₁ * x = x * blockInr hx u₁ :=
    Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ hx u₁)
  have hxt₂ := sec4I_blockInr_piOrth_comm hQ hx u₂
  have ht₁type : invType (blockInr hx u₁) = (2, 1) := by
    rw [invType_blockInr hQ hx hu₁, hu₁t]
  have ht₂type : invType (blockInr hx' u₂) = (2, 1) := by
    rw [invType_blockInr hQ hx' hu₂, hu₂t]
  refine ⟨blockInr hx u₁ * blockInr hx' u₂, hgh, ?_, ?_, ?_⟩
  · calc blockInr hx u₁ * blockInr hx' u₂ * x
        = blockInr hx u₁ * (blockInr hx' u₂ * x) := mul_assoc _ _ _
      _ = blockInr hx u₁ * (x * blockInr hx' u₂) := by rw [hxt₂]
      _ = (blockInr hx u₁ * x) * blockInr hx' u₂ := (mul_assoc _ _ _).symm
      _ = (x * blockInr hx u₁) * blockInr hx' u₂ := by rw [hxt₁]
      _ = x * (blockInr hx u₁ * blockInr hx' u₂) := mul_assoc _ _ _
  · have h1 : invDim (blockInr hx u₁) = 2 := congrArg Prod.fst ht₁type
    have h2 : invSign (blockInr hx u₁) = 1 := congrArg Prod.snd ht₁type
    have h3 : invDim (blockInr hx' u₂) = 2 := congrArg Prod.fst ht₂type
    have h4 : invSign (blockInr hx' u₂) = 1 := congrArg Prod.snd ht₂type
    rw [invType_mul_of_orth hQ h11 h22 horth, h1, h2, h3, h4]
    decide
  ·
    have hxg : blockInr hx u₁ * x =
        blockInr hx (piOrth (Q.restrict (commSp x)) * u₁) := by
      rw [map_mul, blockInr_piOrth]
      exact hxt₁
    have hπu : (piOrth (Q.restrict (commSp x)) * u₁) * (piOrth (Q.restrict (commSp x)) * u₁) = 1 :=
      piOrth_mul_mul_self hu₁
    have hg'g' : blockInr hx (piOrth (Q.restrict (commSp x)) * u₁) *
        blockInr hx (piOrth (Q.restrict (commSp x)) * u₁) = 1 := by
      rw [← map_mul, hπu, map_one]
    have hg't : invType (blockInr hx (piOrth (Q.restrict (commSp x)) * u₁)) = (2, invSign x) := by
      rw [invType_blockInr hQ hx hπu, invType_piOrth_mul hQU hu₁, hu₁d, hu₁s, hU4]
      exact Prod.ext rfl (by
        change invSign x * 1 * (-1) ^ (2 * (4 - 2)) = invSign x
        rw [mul_one]
        have hp : ((-1 : ℤˣ)) ^ (2 * (4 - 2)) = 1 := by decide
        rw [hp, mul_one])
    have hwx : (blockInr hx u₁ * blockInr hx' u₂) * x =
        blockInr hx (piOrth (Q.restrict (commSp x)) * u₁) * blockInr hx' u₂ := by
      rw [mul_assoc, hxt₂, ← mul_assoc, hxg]
    rw [hwx, invType_mul_of_orth hQ hg'g' h22 (polar_blockInr_piOrth_mul hx _ u₂)]
    have h5 : invDim (blockInr hx (piOrth (Q.restrict (commSp x)) * u₁)) = 2 :=
      congrArg Prod.fst hg't
    have h6 : invSign (blockInr hx (piOrth (Q.restrict (commSp x)) * u₁)) = invSign x :=
      congrArg Prod.snd hg't
    have h3 : invDim (blockInr hx' u₂) = 2 := congrArg Prod.fst ht₂type
    have h4 : invSign (blockInr hx' u₂) = 1 := congrArg Prod.snd ht₂type
    rw [h5, h6, h3, h4]
    exact Prod.ext hxd.symm (by
      change invSign x * 1 * (-1) ^ (2 * 2) = invSign x
      have hp : ((-1 : ℤˣ)) ^ (2 * 2) = 1 := by decide
      rw [hp, mul_one, mul_one])

theorem sec4I_exists_twist_model (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    {x : OGroup Q} (hx : x * x = 1) (hr : invDim x = 2 ∨ invDim x = 4) :
    ∃ a u : ↥(omegaProj hQ), HasType (u : ProjOrth Q) 4 1 ∧ u * u = 1 ∧
      u ∈ fixSub (projAut hQ x) ∧ a⁻¹ * projAut hQ x a = u := by
  obtain ⟨w, hww, hwx, hwt, hwxt⟩ : ∃ w : OGroup Q, w * w = 1 ∧ w * x = x * w ∧
      invType w = (4, 1) ∧ invType (w * x) = invType x := by
    rcases hr with h | h
    · exact sec4I_twist_elt_two hQ hdim hx h
    · exact sec4I_twist_elt_four hQ hdim hx h
  have hwd : invDim w = 4 := congrArg Prod.fst hwt
  have hws : invSign w = 1 := congrArg Prod.snd hwt
  have hwΩ : w ∈ omegaGroup hQ := by
    refine (involution_mem_omegaGroup_iff hQ hww).mpr ⟨?_, ?_⟩
    · rw [hwd]
      decide
    · rw [hws, hwd]
      decide
  obtain ⟨a, ha⟩ := exists_conj_of_type hQ (by omega) hx ⟨w, hwΩ⟩ hwx hww (Or.inl hwxt)
  refine ⟨a, omegaToProj hQ ⟨w, hwΩ⟩, ⟨?_, w, hww, hwt, rfl⟩, ?_, ?_, ha⟩
  · intro h1
    have h2 : omegaToProj hQ ⟨w, hwΩ⟩ = 1 := Subtype.ext h1
    rcases (omegaToProj_eq_one_iff hQ ⟨w, hwΩ⟩).mp h2 with h | h
    · have h3 : invType w = (0, 1) := by
        change w = 1 at h
        rw [h, invType_one]
      exact absurd (congrArg Prod.fst (hwt.symm.trans h3)) (by decide)
    · have h3 : invType w = (Module.finrank (ZMod 3) V, quadSign Q) := by
        change w = piOrth Q at h
        rw [h, invType_piOrth hQ]
      have h4 : (4 : ℕ) = Module.finrank (ZMod 3) V := congrArg Prod.fst (hwt.symm.trans h3)
      omega
  · rw [← map_mul, show (⟨w, hwΩ⟩ : omegaGroup hQ) * ⟨w, hwΩ⟩ = 1 from Subtype.ext hww, map_one]
  · rw [mem_fixSub_projAut_iff]
    change toProj Q x * toProj Q w = toProj Q w * toProj Q x
    rw [← map_mul, ← map_mul, hwx]

end CFSG.OddStandard.SmallF3.Omega
