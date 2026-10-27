module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSTypes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6p_swap (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (fr : PFrame Q (Option (Fin 5)) ffC) {y : ProjSim Q} (hyG : ¬ SimInGStar y)
    (hy : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom = ffP1p hQ fr) :
    y * ffTs fr * y⁻¹ = ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr) := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hz : ∀ p ∈ ffP1p hQ fr,
      (y * ffTs fr * y⁻¹) * ffOmegaToSim hQ p =
        ffOmegaToSim hQ p * (y * ffTs fr * y⁻¹) := by
    intro p hp
    have hp' : p ∈ (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom := by
      rw [hy]; exact hp
    obtain ⟨q, hq, hqp⟩ := Subgroup.mem_map.mp hp'
    have hqp' : ffSimOmegaAct hQ h2 y q = p := by
      simpa only [MulEquiv.coe_toMonoidHom] using hqp
    have hcomm : ffTs fr * ffOmegaToSim hQ q = ffOmegaToSim hQ q * ffTs fr :=
      ffTs_comm_normalizer hQ h2 hπ fr (ffP1p_le_normalizer hQ hπ fr hq)
    rw [← hqp', ff_omegaToSim_act hQ h2 y q]
    calc (y * ffTs fr * y⁻¹) * (y * ffOmegaToSim hQ q * y⁻¹)
        = y * (ffTs fr * ffOmegaToSim hQ q) * y⁻¹ := by group
      _ = y * (ffOmegaToSim hQ q * ffTs fr) * y⁻¹ := by rw [hcomm]
      _ = (y * ffOmegaToSim hQ q * y⁻¹) * (y * ffTs fr * y⁻¹) := by group
  have htype : SimHasType (y * ffTs fr * y⁻¹) 1 1 := by
    simpa using ff_simHasType_conj_outer hQ hyG (show Odd 1 from ⟨0, rfl⟩) (ffTs_hasType hQ fr)
  rcases ff6p_cent_P1 hQ h2 hπ fr hz with h1 | h1 | h1 | h1
  · exfalso
    exact ff_simHasType_ne_one (h1 ▸ htype) rfl
  · exfalso
    have h' : SimHasType (ffOmegaToSim hQ (ffZ0s hQ fr)) 1 1 := h1 ▸ htype
    rcases ff_simHasType_rank hQ hdim h' (ffZ0s_hasType hQ fr) with h | h
    · omega
    · omega
  · exfalso
    have h' : SimHasType (ffTs fr) 1 1 := h1 ▸ htype
    exact absurd (ff_simHasType_one_unique hQ hdim h' (ffTs_hasType hQ fr)) (by decide)
  · exact h1

theorem ff6p_tsz0_comm_normalizer_B2 (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : PFrame Q (Option (Fin 5)) ffC) {y : ProjSim Q}
    (hyG : ¬ SimInGStar y)
    (hy : (ffP1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom = ffP1p hQ fr)
    {n : ↥(omegaProj hQ)}
    (hn : n ∈ Subgroup.normalizer
      (((ffB1p hQ fr).map (ffSimOmegaAct hQ h2 y).toMonoidHom : Subgroup ↥(omegaProj hQ)) :
        Set ↥(omegaProj hQ))) :
    (ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr)) * ffOmegaToSim hQ n =
      ffOmegaToSim hQ n * (ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr)) := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  let c : MulAut ↥(omegaProj hQ) := ffSimOmegaAct hQ h2 y
  let m : ↥(omegaProj hQ) := c.symm n
  have hcm : c m = n := MulEquiv.apply_symm_apply c n
  have hn' : n ∈ Subgroup.normalizer
      (((ffB1p hQ fr).map c.toMonoidHom : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ)) := hn
  have hm : m ∈ Subgroup.normalizer
      ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hkey : m * h * m⁻¹ = c.symm (n * c h * n⁻¹) := by
      show (c.symm n) * h * (c.symm n)⁻¹ = c.symm (n * c h * n⁻¹)
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
    rw [hkey, ← Subgroup.mem_map_equiv (f := c) (K := ffB1p hQ fr) (x := n * c h * n⁻¹),
      (Subgroup.mem_normalizer_iff.mp hn' (c h)).symm,
      Subgroup.mem_map_equiv (f := c) (K := ffB1p hQ fr) (x := c h), MulEquiv.symm_apply_apply]
  have hcomm : ffTs fr * ffOmegaToSim hQ m = ffOmegaToSim hQ m * ffTs fr :=
    ffTs_comm_normalizer hQ h2 hπ fr hm
  have hιn : ffOmegaToSim hQ n = y * ffOmegaToSim hQ m * y⁻¹ := by
    rw [← hcm]
    exact ff_omegaToSim_act hQ h2 y m
  have hswap : ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr) = y * ffTs fr * y⁻¹ :=
    (ff6p_swap hQ hdim hsgn h2 fr hyG hy).symm
  rw [hswap, hιn]
  calc (y * ffTs fr * y⁻¹) * (y * ffOmegaToSim hQ m * y⁻¹)
      = y * (ffTs fr * ffOmegaToSim hQ m) * y⁻¹ := by group
    _ = y * (ffOmegaToSim hQ m * ffTs fr) * y⁻¹ := by rw [hcomm]
    _ = (y * ffOmegaToSim hQ m * y⁻¹) * (y * ffTs fr * y⁻¹) := by group

end CFSG.OddStandard.SmallF3.Omega
