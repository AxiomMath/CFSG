module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrSix
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenTop

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec4I_six_minus_component (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
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

theorem asc82FactK6_holds : Asc82FactK6 := by
  intro G _ _ L hL u hu hord hty
  obtain ⟨e⟩ := sec4I_exists_model hL
  have h6 : (6 : ℕ) = 2 ∨ (6 : ℕ) = 4 ∨ (6 : ℕ) = 6 := Or.inr (Or.inr rfl)
  obtain ⟨-, t, htt, htype, hρt⟩ := (sec4I_inducesTypeSome_mem_iff e hu h6).mp hty
  have hd : invDim t = 6 := congrArg Prod.fst htype
  have hs : invSign t = -1 := congrArg Prod.snd htype
  have htΩ : t ∈ omegaGroup sec4IQ_nondegenerate := by
    refine (involution_mem_omegaGroup_iff sec4IQ_nondegenerate htt).mpr ⟨?_, ?_⟩
    · rw [hd]
      decide
    · rw [hd, hs]
      decide
  have hU : 2 ≤ Module.finrank (ZMod 3) (commSp t) := by
    have : Module.finrank (ZMod 3) (commSp t) = 6 := hd
    omega
  obtain ⟨hX, hzX, h2⟩ := sec4I_six_minus_component sec4IQ_nondegenerate sec4IQ_finrank
    (y := ⟨t, htΩ⟩) htt htype hU
  have hρ : sec4ICover e ⟨u, hu⟩ = omegaToProj sec4IQ_nondegenerate ⟨t, htΩ⟩ :=
    Subtype.ext hρt.symm
  rw [← hρ] at hX hzX
  obtain ⟨K, hK, huK, hK2, -⟩ := exists_component_lift L (sec4ICover e) (sec4ICover_odd hL e) hu
    (mul_self_eq_one_of_orderOf_eq_two hord) hX hzX h2
  exact ⟨K, hK, huK, hK2⟩

end CFSG.OddStandard.SmallF3.Omega
