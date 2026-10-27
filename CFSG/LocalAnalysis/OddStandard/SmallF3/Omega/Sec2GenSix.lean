module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenInr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem six_minus_component (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8)
    {y : omegaGroup hQ} (hyy : (y : OGroup Q) * y = 1) (hty : invType (y : OGroup Q) = (6, -1))
    (hU : 2 ≤ Module.finrank (ZMod 3) (commSp (y : OGroup Q))) :
    IsComponentIn (omegaProjInr hQ hyy hU).range
        (Subgroup.centralizer ({omegaToProj hQ y} : Set (omegaProj hQ))) ∧
      omegaToProj hQ y ∈ (omegaProjInr hQ hyy hU).range ∧
      IsTwoU43 ↥(omegaProjInr hQ hyy hU).range := by
  have hr : Module.finrank (ZMod 3) (commSp (y : OGroup Q)) = 6 := by
    simpa only [invType, invDim] using congrArg Prod.fst hty
  have hs : quadSign (Q.restrict (commSp (y : OGroup Q))) = -1 := by
    simpa only [invType, invSign] using congrArg Prod.snd hty
  have hW : 0 < Module.finrank (ZMod 3) (fixSp (y : OGroup Q)) := by
    have := finrank_fixSp_add_finrank_commSp (Q := Q) (y : OGroup Q)
    omega
  have hQU := nondegenerate_restrict_commSp hQ hyy
  have hinj := omegaProjInr_injective hQ hyy hU hW
  let φ : omegaGroup hQU ≃* (omegaProjInr hQ hyy hU).range := MonoidHom.ofInjective hinj
  have hquasi : CFSG.IsQuasisimple ↥(omegaProjInr hQ hyy hU).range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv φ (isQuasisimple_omegaGroup_six_minus hQU hr hs)
  have hle : (omegaProjInr hQ hyy hU).range ≤
      Subgroup.centralizer ({omegaToProj hQ y} : Set (omegaProj hQ)) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hc := Subgroup.mem_centralizer_singleton_iff.mp
      (blockInr_mem_centralizer hQ hyy (b : OGroup _))
    change toProj Q (blockInr hyy (b : OGroup _)) * toProj Q (y : OGroup Q) =
      toProj Q (y : OGroup Q) * toProj Q (blockInr hyy (b : OGroup _))
    rw [← map_mul, ← map_mul, hc]
  have hpiU : piOrth (Q.restrict (commSp (y : OGroup Q))) ∈ omegaGroup hQU := by
    refine (piOrth_mem_omegaGroup_iff hQU).mpr ⟨?_, ?_⟩
    · rw [hr]
      decide
    · rw [hs, hr]
      decide
  have hzX : omegaToProj hQ y ∈ (omegaProjInr hQ hyy hU).range := by
    refine ⟨⟨_, hpiU⟩, ?_⟩
    change omegaToProj hQ (omegaInr hQ hyy hU ⟨_, hpiU⟩) = _
    congr 1
    exact Subtype.ext (blockInr_piOrth hyy)
  exact ⟨isComponentIn_of_normal hle hquasi
    (omegaProjInr_range_normal hQ hyy hU (by omega)), hzX,
    isTwoU43_of_mulEquiv φ (isTwoU43_omegaGroup hQU hr hs)⟩

theorem notQuat_omegaToProj (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8)
    {d : omegaGroup hQ} (hdd : (d : OGroup Q) * d = 1) (htd : invType (d : OGroup Q) = (2, -1)) :
    NotQuat (omegaToProj hQ d) := by
  intro f hf hfd
  obtain ⟨y', hy'y', hty', hωy'⟩ := exists_invType_of_quaternion_omegaProj hQ hdim hf
  have hy'dim : invDim (y' : OGroup Q) = 4 := by
    simpa only [invType, invDim] using congrArg Prod.fst hty'
  have hddim : invDim (d : OGroup Q) = 2 := by
    simpa only [invType, invDim] using congrArg Prod.fst htd
  rcases omegaToProj_eq_iff hQ (hωy'.trans hfd) with h1 | h1
  · rw [h1] at hddim
    omega
  · have h2 := congrArg (fun t => (invType t).1) h1
    simp only [invType_piOrth_mul hQ hy'y', hy'dim, hdim] at h2
    simp only [invType, invDim] at h2 hddim
    omega

theorem layer_reflPair_mem (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8)
    (hσ : quadSign Q = 1) {zb : omegaProj hQ} {d : omegaGroup hQ}
    (hdd : (d : OGroup Q) * d = 1) (htd : invType (d : OGroup Q) = (2, -1))
    (hcore : omegaToProj hQ d ∈ genPocketCore zb) (u v : V) (hQu : Q u ≠ 0) (hQv : Q v ≠ 0)
    (hu : u ∈ fixSp (d : OGroup Q)) (hv : v ∈ fixSp (d : OGroup Q)) (huv : Q u = Q v)
    (g : omegaGroup hQ) (hg : (g : OGroup Q) = reflOf Q u hQu * reflOf Q v hQv) :
    omegaToProj hQ g ∈ genLayers zb := by
  have hπΩ : piOrth Q ∈ omegaGroup hQ := by
    refine (piOrth_mem_omegaGroup_iff hQ).mpr ⟨?_, ?_⟩
    · rw [hdim]
      decide
    · rw [hdim, hσ]
      decide
  let yd : omegaGroup hQ := ⟨piOrth Q * (d : OGroup Q), mul_mem hπΩ d.2⟩
  have hyy : (yd : OGroup Q) * yd = 1 := piOrth_mul_mul_self hdd
  have hdimd : invDim (d : OGroup Q) = 2 := by
    simpa only [invType, invDim] using congrArg Prod.fst htd
  have hsgnd : invSign (d : OGroup Q) = -1 := by
    simpa only [invType, invSign] using congrArg Prod.snd htd
  have hty : invType (yd : OGroup Q) = (6, -1) := by
    change invType (piOrth Q * (d : OGroup Q)) = (6, -1)
    rw [invType_piOrth_mul hQ hdd, hdim, hσ, hdimd, hsgnd]
    decide
  have hU : 2 ≤ Module.finrank (ZMod 3) (commSp (yd : OGroup Q)) := by
    have h6 : Module.finrank (ZMod 3) (commSp (yd : OGroup Q)) = 6 := by
      simpa only [invType, invDim] using congrArg Prod.fst hty
    omega
  obtain ⟨hXc, hzX, hX2⟩ := six_minus_component hQ hdim hyy hty hU
  have hωyd : omegaToProj hQ yd = omegaToProj hQ d := by
    apply Subtype.ext
    change toProj Q (piOrth Q * (d : OGroup Q)) = toProj Q (d : OGroup Q)
    rw [map_mul, toProj_piOrth, one_mul]
  have hgood : GenGood zb (omegaToProj hQ d) (omegaProjInr hQ hyy hU).range := by
    refine ⟨?_, ?_, hcore, notQuat_omegaToProj hQ hdim hdd htd, ?_, ?_, hX2⟩
    · intro h1
      rcases (omegaToProj_eq_one_iff hQ d).mp h1 with h | h
      · rw [h, invType_one] at htd
        exact absurd (congrArg Prod.fst htd) (by decide)
      · rw [h, invType_piOrth hQ, hdim] at htd
        exact absurd (congrArg Prod.fst htd) (by simp)
    · rw [← map_mul, show d * d = 1 from Subtype.ext hdd, map_one]
    · rw [← hωyd]
      exact hXc
    · rw [← hωyd]
      exact hzX
  have hmem : omegaToProj hQ g ∈ (omegaProjInr hQ hyy hU).range := by
    have hcomm : commSp (yd : OGroup Q) = fixSp (d : OGroup Q) := commSp_piOrth_mul hdd
    exact omegaToProj_reflPair_mem_range hQ hyy hU u v (hcomm ▸ hu) (hcomm ▸ hv) hQu hQv huv g hg
  unfold genLayers
  exact Subgroup.mem_iSup_of_mem (omegaToProj hQ d) (Subgroup.mem_iSup_of_mem _
    (Subgroup.mem_iSup_of_mem hgood hmem))

end CFSG.OddStandard.SmallF3.Omega
