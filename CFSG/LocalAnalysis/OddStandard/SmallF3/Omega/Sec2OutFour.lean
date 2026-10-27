module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutOne
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutOrth
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L38Four
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrBlockType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem projAut_piOrth_mul (hQ : Q.Nondegenerate) (x : OGroup Q) :
    projAut hQ (piOrth Q * x) = projAut hQ x := by
  unfold projAut
  rw [map_mul, toProj_piOrth, one_mul]

theorem commSp_blockInr_le {s : OGroup Q} (hs : s * s = 1)
    (b : OGroup (Q.restrict (commSp s))) : commSp (blockInr hs b) ≤ commSp s := by
  rw [commSp_blockInr]
  rintro _ ⟨y, _, rfl⟩
  exact y.2

theorem polar_blockInr_piOrth_mul {x : OGroup Q} (hx : x * x = 1)
    (b : OGroup (Q.restrict (commSp x)))
    (b' : OGroup (Q.restrict (commSp (piOrth Q * x)))) :
    ∀ v ∈ commSp (blockInr hx b), ∀ w ∈ commSp (blockInr (piOrth_mul_mul_self hx) b'),
      QuadraticMap.polar Q v w = 0 := by
  intro v hv w hw
  have hw' : w ∈ fixSp x := by
    have := commSp_blockInr_le (piOrth_mul_mul_self hx) b' hw
    rwa [commSp_piOrth_mul hx] at this
  rw [QuadraticMap.polar_comm]
  exact polar_fixSp_commSp hx hw' (commSp_blockInr_le hx b hv)

theorem outerData_of_four_minus (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8)
    (hσ : quadSign Q = 1) {x : OGroup Q} (hx : x * x = 1) (hxt : invType x = (4, -1)) :
    OuterData ↥(omegaProj hQ) (projAut hQ x) := by
  have hxd : invDim x = 4 := congrArg Prod.fst hxt
  have hxs : invSign x = -1 := congrArg Prod.snd hxt
  have hx' : (piOrth Q * x) * (piOrth Q * x) = 1 := piOrth_mul_mul_self hx
  have hxt' : invType (piOrth Q * x) = (4, -1) := by
    rw [invType_piOrth_mul hQ hx, hxd, hxs, hdim, hσ]
    decide
  have hxd' : invDim (piOrth Q * x) = 4 := congrArg Prod.fst hxt'
  have hxs' : invSign (piOrth Q * x) = -1 := congrArg Prod.snd hxt'
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) x
  have hsum' := finrank_fixSp_add_finrank_commSp (Q := Q) (piOrth Q * x)
  have hrU : Module.finrank (ZMod 3) ↥(commSp x) = invDim x := rfl
  have hrU' : Module.finrank (ZMod 3) ↥(commSp (piOrth Q * x)) = invDim (piOrth Q * x) := rfl
  have hQU := nondegenerate_restrict_commSp hQ hx
  have hQU' := nondegenerate_restrict_commSp hQ hx'
  have hq : CFSG.IsQuasisimple (omegaGroup hQU) :=
    isQuasisimple_omegaGroup_four_minus hQU (by omega) hxs
  have hq' : CFSG.IsQuasisimple (omegaGroup hQU') :=
    isQuasisimple_omegaGroup_four_minus hQU' (by omega) hxs'
  have hU : 2 ≤ Module.finrank (ZMod 3) (commSp x) := by omega
  have hU' : 2 ≤ Module.finrank (ZMod 3) (commSp (piOrth Q * x)) := by omega
  have hW : 0 < Module.finrank (ZMod 3) (fixSp x) := by omega
  have hW' : 0 < Module.finrank (ZMod 3) (fixSp (piOrth Q * x)) := by omega
  obtain ⟨u₁, hu₁, hu₁t⟩ := (exists_involution_of_type hQU 2 (-1)).mpr
    ⟨by omega, fun h => by omega, fun h => by omega⟩
  obtain ⟨u₂, hu₂, hu₂t⟩ := (exists_involution_of_type hQU' 2 (-1)).mpr
    ⟨by omega, fun h => by omega, fun h => by omega⟩
  have hu₁d : invDim u₁ = 2 := congrArg Prod.fst hu₁t
  have hu₁s : invSign u₁ = -1 := congrArg Prod.snd hu₁t
  have hu₂d : invDim u₂ = 2 := congrArg Prod.fst hu₂t
  have hu₂s : invSign u₂ = -1 := congrArg Prod.snd hu₂t
  have hu₁Ω : u₁ ∈ omegaGroup hQU := by
    refine (involution_mem_omegaGroup_iff hQU hu₁).mpr ⟨?_, ?_⟩
    · rw [hu₁d]
      exact even_two
    · rw [hu₁s, hu₁d]
      decide
  have hu₂Ω : u₂ ∈ omegaGroup hQU' := by
    refine (involution_mem_omegaGroup_iff hQU' hu₂).mpr ⟨?_, ?_⟩
    · rw [hu₂d]
      exact even_two
    · rw [hu₂s, hu₂d]
      decide
  have hgg : blockInr hx u₁ * blockInr hx u₁ = 1 := by rw [← map_mul, hu₁, map_one]
  have hhh : blockInr hx' u₂ * blockInr hx' u₂ = 1 := by rw [← map_mul, hu₂, map_one]
  have horth := polar_blockInr_piOrth_mul hx u₁ u₂
  have hgh : (blockInr hx u₁ * blockInr hx' u₂) * (blockInr hx u₁ * blockInr hx' u₂) = 1 :=
    mul_mul_self_of_orth hQ hgg hhh horth
  have hgx : blockInr hx u₁ * x = x * blockInr hx u₁ :=
    Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ hx u₁)
  have hhx : blockInr hx' u₂ * x = x * blockInr hx' u₂ := by
    have h1 : blockInr hx' u₂ * (piOrth Q * x) = (piOrth Q * x) * blockInr hx' u₂ :=
      Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ hx' u₂)
    have h2 : piOrth Q * (blockInr hx' u₂ * x) = piOrth Q * (x * blockInr hx' u₂) := by
      calc piOrth Q * (blockInr hx' u₂ * x) = (piOrth Q * blockInr hx' u₂) * x := by group
        _ = (blockInr hx' u₂ * piOrth Q) * x := by rw [mul_piOrth_comm]
        _ = blockInr hx' u₂ * (piOrth Q * x) := by group
        _ = (piOrth Q * x) * blockInr hx' u₂ := h1
        _ = piOrth Q * (x * blockInr hx' u₂) := by group
    exact mul_left_cancel h2
  have hgt : invType (blockInr hx u₁) = (2, -1) := by rw [invType_blockInr hQ hx hu₁, hu₁t]
  have hht : invType (blockInr hx' u₂) = (2, -1) := by rw [invType_blockInr hQ hx' hu₂, hu₂t]
  have hut : invType (blockInr hx u₁ * blockInr hx' u₂) = (4, 1) := by
    rw [invType_mul_of_orth hQ hgg hhh horth]
    have h1 : invDim (blockInr hx u₁) = 2 := congrArg Prod.fst hgt
    have h2 : invSign (blockInr hx u₁) = -1 := congrArg Prod.snd hgt
    have h3 : invDim (blockInr hx' u₂) = 2 := congrArg Prod.fst hht
    have h4 : invSign (blockInr hx' u₂) = -1 := congrArg Prod.snd hht
    rw [h1, h2, h3, h4]
    decide
  have hxg : blockInr hx u₁ * x = blockInr hx (piOrth (Q.restrict (commSp x)) * u₁) := by
    rw [map_mul, blockInr_piOrth]
    exact hgx
  have hπu : (piOrth (Q.restrict (commSp x)) * u₁) * (piOrth (Q.restrict (commSp x)) * u₁) = 1 :=
    piOrth_mul_mul_self hu₁
  have hg'g' : blockInr hx (piOrth (Q.restrict (commSp x)) * u₁) *
      blockInr hx (piOrth (Q.restrict (commSp x)) * u₁) = 1 := by
    rw [← map_mul, hπu, map_one]
  have hg't : invType (blockInr hx (piOrth (Q.restrict (commSp x)) * u₁)) = (2, 1) := by
    rw [invType_blockInr hQ hx hπu, invType_piOrth_mul hQU hu₁, hu₁d, hu₁s]
    have h1 : Module.finrank (ZMod 3) ↥(commSp x) = 4 := by omega
    have h2 : quadSign (Q.restrict (commSp x)) = -1 := hxs
    rw [h1, h2]
    decide
  have hwx : (blockInr hx u₁ * blockInr hx' u₂) * x =
      blockInr hx (piOrth (Q.restrict (commSp x)) * u₁) * blockInr hx' u₂ := by
    rw [mul_assoc, hhx, ← mul_assoc, hxg]
  have hwxt : invType ((blockInr hx u₁ * blockInr hx' u₂) * x) = invType x := by
    rw [hwx, invType_mul_of_orth hQ hg'g' hhh (polar_blockInr_piOrth_mul hx _ u₂), hxt]
    have h3 : invDim (blockInr hx' u₂) = 2 := congrArg Prod.fst hht
    have h4 : invSign (blockInr hx' u₂) = -1 := congrArg Prod.snd hht
    have h5 : invDim (blockInr hx (piOrth (Q.restrict (commSp x)) * u₁)) = 2 :=
      congrArg Prod.fst hg't
    have h6 : invSign (blockInr hx (piOrth (Q.restrict (commSp x)) * u₁)) = 1 :=
      congrArg Prod.snd hg't
    rw [h3, h4, h5, h6]
    decide
  set w : ↥(omegaGroup hQ) := omegaInr hQ hx hU ⟨u₁, hu₁Ω⟩ * omegaInr hQ hx' hU' ⟨u₂, hu₂Ω⟩
    with hwdef
  have hwc : (w : OGroup Q) = blockInr hx u₁ * blockInr hx' u₂ := rfl
  have hwx' : (w : OGroup Q) * x = x * (w : OGroup Q) := by
    rw [hwc]
    calc blockInr hx u₁ * blockInr hx' u₂ * x = blockInr hx u₁ * (blockInr hx' u₂ * x) :=
          mul_assoc _ _ _
      _ = blockInr hx u₁ * (x * blockInr hx' u₂) := by rw [hhx]
      _ = (blockInr hx u₁ * x) * blockInr hx' u₂ := (mul_assoc _ _ _).symm
      _ = (x * blockInr hx u₁) * blockInr hx' u₂ := by rw [hgx]
      _ = x * (blockInr hx u₁ * blockInr hx' u₂) := mul_assoc _ _ _
  have hww : (w : OGroup Q) * w = 1 := by rw [hwc]; exact hgh
  obtain ⟨a, ha⟩ := exists_conj_of_type hQ (by omega) hx w hwx' hww
    (Or.inl (by rw [hwc]; exact hwxt))
  have hw1 : omegaToProj hQ w ≠ 1 := by
    intro h1
    rcases (omegaToProj_eq_one_iff hQ w).mp h1 with h | h
    · rw [hwc] at h
      have h1 : invType (blockInr hx u₁ * blockInr hx' u₂) = (0, 1) := by rw [h, invType_one]
      have h2 : (4 : ℕ) = 0 := congrArg Prod.fst (hut.symm.trans h1)
      omega
    · rw [hwc] at h
      have h1 : invType (blockInr hx u₁ * blockInr hx' u₂) =
          (Module.finrank (ZMod 3) V, quadSign Q) := by rw [h, invType_piOrth hQ]
      have h2 : (4 : ℕ) = Module.finrank (ZMod 3) V := congrArg Prod.fst (hut.symm.trans h1)
      omega
  have hL1 := omegaProjInr_mem_layer hQ hx hU hW hq ⟨u₁, hu₁Ω⟩
  have hL2 := omegaProjInr_mem_layer hQ hx' hU' hW' hq' ⟨u₂, hu₂Ω⟩
  rw [projAut_piOrth_mul] at hL2
  refine ⟨a, omegaToProj hQ w, ?_, hw1, ?_, ha⟩
  · rw [← map_mul, show w * w = 1 from Subtype.ext hww, map_one]
  · rw [hwdef, map_mul]
    exact Subgroup.mul_mem _ hL1 hL2

end CFSG.OddStandard.SmallF3.Omega
