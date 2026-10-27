module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6Q8Lift
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Assembly.ComponentTypeDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem m6z_invType_of_q8_lift_six (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1)
    {q r : OGroup Q} (hq : q ∈ omegaGroup hQ) (hr : r ∈ omegaGroup hQ)
    (hyy : (q * q) * (q * q) = 1) (hy1 : q * q ≠ 1) (hyπ : q * q ≠ piOrth Q)
    (hb : r * r = q * q ∨ r * r = piOrth Q * (q * q))
    (hc : r * q = q⁻¹ * r ∨ r * q = piOrth Q * (q⁻¹ * r)) :
    invType (q * q) = (4, 1) ∨ invType (piOrth Q * (q * q)) = (4, 1) := by
  have hΩ : q * q ∈ omegaGroup hQ := mul_mem hq hq
  have homega := (involution_mem_omegaGroup_iff hQ hyy).mp hΩ
  have hev : Even (invDim (q * q)) := homega.1
  have hsign : invSign (q * q) = (-1) ^ (invDim (q * q) / 2) := homega.2
  have hle : invDim (q * q) ≤ 6 := by rw [← hdim]; exact invDim_le (q * q)
  have hne0 : invDim (q * q) ≠ 0 := fun h => hy1 ((invDim_eq_zero_iff hyy).mp h)
  have hne6 : invDim (q * q) ≠ 6 := by
    intro h
    exact hyπ ((invDim_eq_finrank_iff hyy).mp (by rw [h, hdim]))
  have hcases : invDim (q * q) = 2 ∨ invDim (q * q) = 4 := by
    obtain ⟨m, hm⟩ := hev
    omega
  rcases hcases with h2 | h4
  · right
    have hty := invType_piOrth_mul_of_even_minus hQ hyy (by rw [hdim]; norm_num) hs
    rw [hty]
    refine Prod.ext ?_ ?_
    · show Module.finrank (ZMod 3) V - invDim (q * q) = 4
      omega
    · show ((-1 : ℤˣ) ^ (invDim (q * q) + 1)) * invSign (q * q) = 1
      rw [h2, hsign, h2]
      decide
  · left
    have hsign4 : invSign (q * q) = 1 := by
      rw [hsign, h4]
      norm_num
    exact Prod.ext h4 hsign4

theorem m6z_exists_lift_of_pocket_omegaProj_six (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) {x : omegaProj hQ}
    (hx : IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) x) :
    ∃ y : omegaGroup hQ, (y : OGroup Q) * y = 1 ∧ invType (y : OGroup Q) = (4, 1) ∧
      omegaToProj hQ y = x := by
  unfold IsI4PlusIn Sl23PocketIn at hx
  obtain ⟨hord, K, hxK, hKle, hKsub, hKsl⟩ := hx
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite (omegaProj hQ) := inferInstance
  obtain ⟨f, hf, hfx, -⟩ := exists_quaternion_of_isSL23Mod hKsl hxK hord
  obtain ⟨q, r, hρ, hyy, hy1, hyπ, hb, hc⟩ := m6z_exists_q8_lift hQ hf
  have h12 := m6z_invType_of_q8_lift_six hQ hdim hs q.2 r.2 hyy hy1 hyπ hb hc
  have hπmem : piOrth Q ∈ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ]
    constructor
    · rw [hdim]; norm_num
    · rw [hdim, hs]; decide
  rcases h12 with htyq | htypq
  · refine ⟨q * q, ?_, ?_, ?_⟩
    · simpa using hyy
    · simpa using htyq
    · exact hρ.trans hfx
  · refine ⟨⟨piOrth Q, hπmem⟩ * (q * q), ?_, ?_, ?_⟩
    · simpa using piOrth_mul_mul_self (t := (q : OGroup Q) * (q : OGroup Q)) hyy
    · simpa using htypq
    · have hp1 : omegaToProj hQ (⟨piOrth Q, hπmem⟩ : omegaGroup hQ) = 1 :=
        (omegaToProj_eq_one_iff hQ _).mpr (Or.inr rfl)
      calc
        omegaToProj hQ (⟨piOrth Q, hπmem⟩ * (q * q))
          = omegaToProj hQ (⟨piOrth Q, hπmem⟩ : omegaGroup hQ) * omegaToProj hQ (q * q) :=
            map_mul _ _ _
        _ = omegaToProj hQ (q * q) := by rw [hp1, one_mul]
        _ = f (QuaternionGroup.a 2) := hρ
        _ = x := hfx

end CFSG.OddStandard.SmallF3.Omega
