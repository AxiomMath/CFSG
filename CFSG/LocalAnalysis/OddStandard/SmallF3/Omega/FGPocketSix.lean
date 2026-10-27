module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FivePocket
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Pocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Equiv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_isI4PlusIn_top_of_hasType_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) {z : omegaProj hQ}
    (h : HasType (z : ProjOrth Q) 4 1) : IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) z := by
  obtain ⟨-, t, htt, hty, hzt⟩ := h
  have hd : invDim t = 4 := congrArg Prod.fst hty
  have hs' : invSign t = 1 := congrArg Prod.snd hty
  have htΩ : t ∈ omegaGroup hQ := by
    refine (involution_mem_omegaGroup_iff hQ htt).mpr ⟨?_, ?_⟩
    · rw [hd]
      decide
    · rw [hd, hs']
      decide
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hs
  have hpocket := asc82PocketCover_holds V Q hQ ⟨t, htΩ⟩ (Subtype.ext htt) hty
  have h2 := isI4PlusIn_top_map_mulEquiv (omegaProjEquiv hQ hπ) hpocket
  have hz : omegaProjEquiv hQ hπ ⟨t, htΩ⟩ = z := Subtype.ext hzt
  rwa [hz] at h2

theorem fg_hasType_of_isI4PlusIn_top_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) {z : omegaProj hQ}
    (h : IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) z) : HasType (z : ProjOrth Q) 4 1 := by
  obtain ⟨hord, K, hzK, -, -, hKsl⟩ := h
  obtain ⟨f, hf, hfz, -⟩ := exists_quaternion_of_isSL23Mod hKsl hzK hord
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hs
  let E := omegaProjEquiv hQ hπ
  let F : QuaternionGroup 2 →* OGroup Q :=
    (omegaGroup hQ).subtype.comp (E.symm.toMonoidHom.comp f)
  have hF : Function.Injective F := Subtype.val_injective.comp (E.symm.injective.comp hf)
  have ha1 : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by decide +kernel
  have hx0 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 := by decide +kernel
  have hconj : (QuaternionGroup.a 1 : QuaternionGroup 2)⁻¹ * QuaternionGroup.xa 0 =
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide +kernel
  have ha22 : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by
    decide +kernel
  have ha2ne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide +kernel
  have hqq : F (QuaternionGroup.a 1) * F (QuaternionGroup.a 1) = F (QuaternionGroup.a 2) := by
    rw [← map_mul, ha1]
  have hrr : F (QuaternionGroup.xa 0) * F (QuaternionGroup.xa 0) = F (QuaternionGroup.a 2) := by
    rw [← map_mul, hx0]
  have hyy : F (QuaternionGroup.a 2) * F (QuaternionGroup.a 2) = 1 := by
    rw [← map_mul, ha22, map_one]
  have hrq : F (QuaternionGroup.xa 0) * F (QuaternionGroup.a 1) =
      (F (QuaternionGroup.a 1))⁻¹ * F (QuaternionGroup.xa 0) := by
    rw [← map_inv, ← map_mul, ← map_mul, hconj]
  obtain ⟨h4, hsg⟩ := four_dvd_invDim_of_quaternion hQ (hqq.trans hrr.symm)
    (by rw [hqq]; exact hyy) hrq
  rw [hqq] at h4 hsg
  have hy1 : F (QuaternionGroup.a 2) ≠ 1 := fun h => ha2ne (hF (h.trans (map_one F).symm))
  have hd0 := (invDim_eq_zero_iff hyy).not.mpr hy1
  have hle := invDim_le (F (QuaternionGroup.a 2))
  rw [hdim] at hle
  have hy4 : invDim (F (QuaternionGroup.a 2)) = 4 := by omega
  have hzE : E (E.symm (f (QuaternionGroup.a 2))) = z := by
    rw [E.apply_symm_apply, hfz]
  refine ⟨?_, F (QuaternionGroup.a 2), hyy, Prod.ext hy4 hsg, ?_⟩
  · intro h1
    have h2 : z = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hord
    exact absurd hord (by decide)
  · exact congrArg Subtype.val hzE

end CFSG.OddStandard.SmallF3.Omega
