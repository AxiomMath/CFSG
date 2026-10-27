module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GDefs
public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldX

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open CFSG.GH74.GLS.Th2.P412

variable {G : Type} [Group G] [Finite G] {X : Type} [Group X]

structure Sec5OPHyp (t z : G) (T : Subgroup G)
    (π : ↥(centralizer ({z} : Set G)) →* X) : Prop where
  tH : t ∈ centralizer ({z} : Set G)
  ht : orderOf t = 2
  hz : orderOf z = 2
  surj : Function.Surjective π
  ker : π.ker = (zpowers z).subgroupOf (centralizer ({z} : Set G))
  tT : t ∈ T
  zT : z ∈ T
  TH : T ≤ centralizer ({z} : Set G)
  TY : T ≤ sec5op_Y t z
  t_not_mem : t ∉ zpowers z
  nconj : ¬ ∃ g : G, g⁻¹ * t * g = t * z

@[expose] def sec5op_Tb (z : G) (T : Subgroup G) (π : ↥(centralizer ({z} : Set G)) →* X) :
    Subgroup X :=
  (T.subgroupOf (centralizer ({z} : Set G))).map π

@[expose] noncomputable def sec5op_act (A : Subgroup X) : X →* MulAut (Sec5GBar A) where
  toFun g := psiAut (normalClosure (A : Set X)) g
  map_one' := by
    ext x
    refine QuotientGroup.induction_on x fun m => ?_
    simp only [psiAut_mk, map_one, MulAut.one_apply]
  map_mul' g h := by
    ext x
    refine QuotientGroup.induction_on x fun m => ?_
    simp only [psiAut_mk, MulAut.mul_apply, map_mul]

@[expose] noncomputable def sec5op_rho (z : G) (T : Subgroup G)
    (π : ↥(centralizer ({z} : Set G)) →* X) :
    ↥(centralizer ({z} : Set G)) →* MulAut (Sec5GBar (sec5op_Tb z T π)) :=
  (sec5op_act (sec5op_Tb z T π)).comp π

omit [Finite G] in
theorem sec5op_rho_mk {z : G} {T : Subgroup G} {π : ↥(centralizer ({z} : Set G)) →* X}
    (h : ↥(centralizer ({z} : Set G)))
    (m : ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X))) :
    sec5op_rho z T π h (sec5g_pi (sec5op_Tb z T π) m) =
      sec5g_pi (sec5op_Tb z T π) (MulAut.conjNormal (π h) m) := by
  change psiAut (normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X)) (π h)
      (sec5g_pi (sec5op_Tb z T π) m) =
    sec5g_pi (sec5op_Tb z T π) (MulAut.conjNormal (π h) m)
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, psiAut_mk]

end CFSG.OddStandard.SmallF3.Omega
