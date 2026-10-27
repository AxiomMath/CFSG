module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXQBCentE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTheta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarE16

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem fx_qb_sq_mem_centralizer {B : Subgroup G} (hBL : B ≤ L) (hB : IsElemAb2 B 5)
    (hBZ : Nat.card ↥(B ⊓ centerIn L) ≤ 2) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hLp : commutator ↥L = ⊤) {y : G} (hyN : y ∈ normalizer (L : Set G))
    (hyB : y ∈ centralizer (B : Set G)) : y * y ∈ centralizer (L : Set G) := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hh : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)) :=
    Or.inr ⟨hdim, Or.inr hsgn⟩
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  obtain ⟨U, hU, hUφ⟩ := fx_qb_exists_E16 hBL hB hBZ e
  obtain ⟨y', hy'⟩ := ff_star_E16_conj hQ hdim hsgn h2 fr hU
  let z : ProjSim Q := ffTheta hQ hh e ⟨y, hyN⟩
  have hzI : InducesViaP L (Subgroup.center ↥L) hQ e y z := ffTheta_induces hQ hh e ⟨y, hyN⟩
  have hzU : ∀ u ∈ U, ffSimOmegaAct hQ h2 z u = u := by
    intro u hu
    obtain ⟨l, hlB, rfl⟩ := hUφ u hu
    have hyl : y * (l : G) = (l : G) * y :=
      (Subgroup.mem_centralizer_iff.mp hyB (l : G) hlB).symm
    exact ff6m_phi_conj hQ h2 e hzI l l (by rw [hyl]; group)
  have hz' : ∀ b ∈ ffB1 hQ fr, ffSimOmegaAct hQ h2 (y'⁻¹ * z * y') b = b := by
    intro b hb
    have hbU : ffSimOmegaAct hQ h2 y' b ∈ U := by
      rw [hy']
      exact Subgroup.mem_map_of_mem (ffSimOmegaAct hQ h2 y').toMonoidHom hb
    apply (ffSimOmegaAct hQ h2 y').injective
    rw [← MulAut.mul_apply, ← map_mul, show y' * (y'⁻¹ * z * y') = z * y' by group, map_mul,
      MulAut.mul_apply, hzU _ hbU]
  obtain ⟨K, hK⟩ := ff_star_cent_sim hQ h2 fr hz'
  have hzz' : (y'⁻¹ * z * y') * (y'⁻¹ * z * y') = 1 := by
    rw [hK, ← map_mul, ← map_mul, fr.signChange_mul_self, map_one, map_one]
  have hzz : z * z = 1 := by
    have h : z * z = y' * ((y'⁻¹ * z * y') * (y'⁻¹ * z * y')) * y'⁻¹ := by group
    rw [h, hzz', mul_one, mul_inv_cancel]
  have hyy : (⟨y, hyN⟩ : ↥(normalizer (L : Set G))) * ⟨y, hyN⟩ = ⟨y * y, mul_mem hyN hyN⟩ :=
    rfl
  have h1 : ffTheta hQ hh e ⟨y * y, mul_mem hyN hyN⟩ = 1 := by
    rw [← hyy, map_mul]
    exact hzz
  exact (ffTheta_eq_one_iff hQ hh e hLp ⟨y * y, mul_mem hyN hyN⟩).mp h1

end CFSG.OddStandard.SmallF3.Omega
