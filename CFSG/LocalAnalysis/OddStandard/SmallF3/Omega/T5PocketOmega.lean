module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Pocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem t5_isI4PlusIn_omega_iff (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1)
    {g : omegaGroup hQ} (hg : (g : OGroup Q) * g = 1) (hg1 : g ≠ 1) :
    IsI4PlusIn (⊤ : Subgroup ↥(omegaGroup hQ)) g ↔ invType (g : OGroup Q) = (4, 1) := by
  constructor
  · rintro ⟨hord, K, hgK, -, -, hKsl⟩
    obtain ⟨f, hf, hfg, -⟩ := exists_quaternion_of_isSL23Mod hKsl hgK hord
    let F : QuaternionGroup 2 →* OGroup Q := (omegaGroup hQ).subtype.comp f
    have hF : Function.Injective F := Subtype.val_injective.comp hf
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
    have hFg : F (QuaternionGroup.a 2) = (g : OGroup Q) :=
      congrArg Subtype.val hfg
    rw [hFg] at hy4 hsg
    exact Prod.ext hy4 hsg
  · intro htype
    exact asc82PocketCover_holds V Q hQ g (Subtype.ext hg) htype

end CFSG.OddStandard.SmallF3.Omega
