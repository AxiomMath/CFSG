module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTwist
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOrth3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private noncomputable def auxProdEquiv (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    (OGroup (Q.restrict (fixSp t)) × OGroup (Q.restrict (commSp t))) ≃*
      ↥(Subgroup.centralizer ({t} : Set (OGroup Q))) := by
  classical
  let φ : (OGroup (Q.restrict (fixSp t)) × OGroup (Q.restrict (commSp t))) →*
      ↥(Subgroup.centralizer ({t} : Set (OGroup Q))) :=
    { toFun := fun p => ⟨blockHom htt p, by
        rw [← range_blockHom hQ htt]
        exact MonoidHom.mem_range.mpr ⟨p, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun p q => Subtype.ext (map_mul _ p q) }
  exact MulEquiv.ofBijective φ (by
    constructor
    · intro p q hpq
      exact blockHom_injective htt (Subtype.ext_iff.mp hpq)
    · intro y
      have hy : (y : OGroup Q) ∈ (blockHom htt).range := by
        rw [range_blockHom hQ htt]
        exact y.2
      obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hy
      exact ⟨p, Subtype.ext hp⟩)

private noncomputable def auxHom (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    ↥(omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q))) →*
      OGroup (Q.restrict (fixSp t)) × OGroup (Q.restrict (commSp t)) :=
  (auxProdEquiv hQ htt).symm.toMonoidHom.comp (Subgroup.inclusion inf_le_right)

private theorem auxHom_injective (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    Function.Injective (auxHom hQ htt) := by
  intro a b hab
  exact Subgroup.inclusion_injective inf_le_right ((auxProdEquiv hQ htt).symm.injective hab)

private theorem aux_finrank_commSp_eq (hQ : Q.Nondegenerate) {t : OGroup Q} {α : ℤˣ}
    (hty : invType t = (3, α)) : Module.finrank (ZMod 3) (commSp t) = 3 := by
  have h := congrArg Prod.fst hty
  simpa only [invType, invDim] using h

private theorem aux_finrank_fixSp_eq (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {t : OGroup Q} {α : ℤˣ} (hty : invType t = (3, α)) :
    Module.finrank (ZMod 3) (fixSp t) = 3 := by
  have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
  have h3 := aux_finrank_commSp_eq hQ hty
  omega

theorem ff6m_K3_solvable (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1)
    {x : ProjSim Q} (hx : KM3 x) : Group.IsSolvable ↥(ffFix hQ (by omega) x) := by
  obtain ⟨α, y, hyx, htype⟩ := hx
  obtain ⟨_, t, htt, hty, hto⟩ := htype
  have hyx' : projOrthToProjSim Q (toProj Q t) = x := by rw [hto]; exact hyx
  have hdimC := aux_finrank_commSp_eq hQ hty
  have hdimU := aux_finrank_fixSp_eq hQ hdim hty
  haveI hsol1 : Group.IsSolvable (OGroup (Q.restrict (fixSp t))) :=
    ff_orth3_solvable (nondegenerate_restrict_fixSp hQ htt) hdimU
  haveI hsol2 : Group.IsSolvable (OGroup (Q.restrict (commSp t))) :=
    ff_orth3_solvable (nondegenerate_restrict_commSp hQ htt) hdimC
  haveI hsolC : Group.IsSolvable ↥(Subgroup.centralizer ({t} : Set (OGroup Q))) :=
    ff_solvable_congr (auxProdEquiv hQ htt) inferInstance
  have hsolA :
      Group.IsSolvable ↥(omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q))) :=
    Group.isSolvable_of_isSolvable_injective (f := auxHom hQ htt) (auxHom_injective hQ htt)
  have hEq : omegaGroup hQ ⊓ fixSub (simAct Q (orthToSim Q t)) =
      omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q)) :=
    congrArg (fun S => omegaGroup hQ ⊓ S) (fixSub_simAct_orthToSim t)
  have hsolA' : Group.IsSolvable ↥(omegaGroup hQ ⊓ fixSub (simAct Q (orthToSim Q t))) :=
    ff_solvable_congr (MulEquiv.subgroupCongr hEq).symm hsolA
  rw [← hyx', projOrthToProjSim_toProj]
  exact ff6m_solvable_of_twist hQ hdim (orthToSim Q t) hsolA'

theorem ff6m_K3_xTwoCore (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1)
    {x : ProjSim Q} (hx : KM3 x) : XTwoCore ↥(ffFix hQ (by omega) x) := by
  obtain ⟨α, y, hyx, htype⟩ := hx
  obtain ⟨_, t, htt, hty, hto⟩ := htype
  have hyx' : projOrthToProjSim Q (toProj Q t) = x := by rw [hto]; exact hyx
  have hdimC := aux_finrank_commSp_eq hQ hty
  have hdimU := aux_finrank_fixSp_eq hQ hdim hty
  have h1 := ff_orth3_series (nondegenerate_restrict_fixSp hQ htt) hdimU
  have h2 := ff_orth3_series (nondegenerate_restrict_commSp hQ htt) hdimC
  haveI : Finite (OGroup (Q.restrict (fixSp t))) := inferInstance
  haveI : Finite (OGroup (Q.restrict (commSp t))) := inferInstance
  have hcore : XTwoCore ↥(omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q))) :=
    ff_xTwoCore_of_prod h1 h2 (auxHom hQ htt) (auxHom_injective hQ htt)
  have hEq : omegaGroup hQ ⊓ fixSub (simAct Q (orthToSim Q t)) =
      omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q)) :=
    congrArg (fun S => omegaGroup hQ ⊓ S) (fixSub_simAct_orthToSim t)
  have hcore' : XTwoCore ↥(omegaGroup hQ ⊓ fixSub (simAct Q (orthToSim Q t))) :=
    (ff_xTwoCore_congr (MulEquiv.subgroupCongr hEq)).mpr hcore
  rw [← hyx', projOrthToProjSim_toProj]
  exact ff6m_xTwoCore_of_twist hQ hdim (orthToSim Q t) hcore'

end CFSG.OddStandard.SmallF3.Omega
