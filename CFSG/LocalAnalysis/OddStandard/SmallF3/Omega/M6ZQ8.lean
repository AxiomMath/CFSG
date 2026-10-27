module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6Q8Lift
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Q8Plus
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem m6z_invType_of_pocket_omega (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V ≤ 8) {g : omegaGroup hQ}
    (hπ : Module.finrank (ZMod 3) V = 8 → (g : OGroup Q) ≠ piOrth Q)
    (hg : IsI4PlusIn (⊤ : Subgroup (omegaGroup hQ)) g) :
    (g : OGroup Q) * g = 1 ∧ invType (g : OGroup Q) = (4, 1) := by
  obtain ⟨hord, K, hgK, -, -, hKsl⟩ := hg
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
  have hd0 : invDim (F (QuaternionGroup.a 2)) ≠ 0 :=
    fun h => hy1 ((invDim_eq_zero_iff hyy).mp h)
  have hle : invDim (F (QuaternionGroup.a 2)) ≤ Module.finrank (ZMod 3) V :=
    invDim_le (F (QuaternionGroup.a 2))
  have hFg : F (QuaternionGroup.a 2) = (g : OGroup Q) := congrArg Subtype.val hfg
  have hne8 : invDim (F (QuaternionGroup.a 2)) ≠ 8 := by
    intro h8
    have hfin : Module.finrank (ZMod 3) V = 8 := by omega
    have hpi : F (QuaternionGroup.a 2) = piOrth Q :=
      (invDim_eq_finrank_iff hyy).mp (by rw [h8, hfin])
    rw [hFg] at hpi
    exact hπ hfin hpi
  have hy4 : invDim (F (QuaternionGroup.a 2)) = 4 := by omega
  have hyg : (g : OGroup Q) * (g : OGroup Q) = 1 := by
    rw [← hFg]
    exact hyy
  rw [hFg] at hy4 hsg
  exact ⟨hyg, Prod.ext hy4 hsg⟩

theorem m6z_isI4PlusIn_omegaProj_of_invType (hQ : Q.Nondegenerate) {y : omegaGroup hQ}
    (hyy : (y : OGroup Q) * y = 1) (hty : invType (y : OGroup Q) = (4, 1))
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) :
    IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) (omegaToProj hQ y) := by
  have hdim4 : Module.finrank (ZMod 3) (commSp (y : OGroup Q)) = 4 := by
    simpa only [invType, invDim] using congrArg Prod.fst hty
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [Subgroup.coe_one, commSp_one, finrank_bot] at hdim4
    omega
  have hfix : 0 < Module.finrank (ZMod 3) (fixSp (y : OGroup Q)) := by
    have h1 := finrank_fixSp_add_finrank_commSp (y : OGroup Q)
    omega
  obtain ⟨K, M, hzK, hKM, hMC, hKM', hMC', hKsl, hKπ⟩ :=
    exists_pocket_chain_of_invType hQ y hyy hty hfix
  have hzz : orderOf y = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hyy) hy1
  have hdis : Disjoint K (omegaToProj hQ).ker := by
    rw [Subgroup.disjoint_def]
    intro k hk hkρ
    rcases (omegaToProj_eq_one_iff hQ k).mp (MonoidHom.mem_ker.mp hkρ) with h | h
    · exact Subtype.ext h
    · exact absurd h (hKπ k hk)
  exact isI4PlusIn_map_of_chain (omegaToProj hQ) (omegaToProj_surjective hQ)
    (fun m hm g => omegaToProj_ker_central hQ (MonoidHom.mem_ker.mp hm) g) hzz hzK hKM hMC
    hKM' hMC' hKsl hdis

theorem m6z_exists_lift_of_pocket_omegaProj_eight (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) {x : omegaProj hQ}
    (hx : IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) x) :
    ∃ y : omegaGroup hQ, (y : OGroup Q) * y = 1 ∧ invType (y : OGroup Q) = (4, 1) ∧
      omegaToProj hQ y = x := by
  obtain ⟨hord, K, hxK, -, -, hKsl⟩ := hx
  obtain ⟨f, hf, hfx, -⟩ := exists_quaternion_of_isSL23Mod hKsl hxK hord
  obtain ⟨q, r, hρ, hyy, hy1, hyπ, hb, hc⟩ := m6z_exists_q8_lift hQ hf
  refine ⟨q * q, ?_, invType_eq_of_q8_lift hQ hdim q.2 r.2 hyy hy1 hyπ hb hc,
    hρ.trans hfx⟩
  simpa only [Subgroup.coe_mul] using hyy

end CFSG.OddStandard.SmallF3.Omega
