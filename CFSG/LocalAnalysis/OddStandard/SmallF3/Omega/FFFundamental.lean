module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFFundamentalAux2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem ff_layerCent_eq_bot_of_solvable (L : Subgroup G) (s : G)
    (h : Group.IsSolvable ↥(L ⊓ centralizer ({s} : Set G))) : layerCent L s = ⊥ :=
  ff_layerCent_eq_bot_of_solvable_aux L s h

theorem ff_dinv_not_mem_centralizer (L : Subgroup G) (s : G) {k : ℕ} (hk : k < 5)
    (h : DInv L s k) : s ∉ centralizer (L : Set G) :=
  ff_dinv_not_mem_centralizer_aux L s hk h

theorem ff_dinv_excl (L : Subgroup G) (s : G) {i j : ℕ} (hi : i < 5) (hj : j < 5)
    (hI : DInv L s i) (hJ : DInv L s j) : i = j :=
  ff_dinv_excl_aux L s hi hj hI hJ

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {L : Subgroup G}

theorem ff_KM0_of_dinv0 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : DInv L s 0) :
    KM0 x :=
  ff_KM0_of_dinv0_aux hQ hdim hsgn hz e hs hss h

theorem ff_KM1_of_dinv1 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : DInv L s 1) :
    KM1 x :=
  ff_KM1_of_dinv1_aux hQ hdim hsgn hz e hs hss h

theorem ff_KM3_of_dinv3 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : DInv L s 3) :
    KM3 x :=
  ff_KM3_of_dinv3_aux hQ hdim hsgn hz e hs hss h

theorem ff_KM4_of_dinv4 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : DInv L s 4) :
    KM4 x :=
  ff_KM4_of_dinv4_aux hQ hdim hsgn hz e hs hss h

end Model

theorem ff_kindP_iff_dinv (hGA : CFSG.Open.GriessAllModelsStatement) [Finite G] {L : Subgroup G}
    (hL : IsOm6P L) {s : G} (hs2 : orderOf s = 2) (hsn : s ∈ normalizer (L : Set G)) {k : ℕ}
    (hk : k < 5) : KindP L s k ↔ DInv L s k :=
  ff_kindP_iff_dinv_aux hGA hL hs2 hsn hk

theorem ff_dinv_classify (hGA : CFSG.Open.GriessAllModelsStatement) [Finite G] {L : Subgroup G}
    (hL : IsOm6P L) {s : G} (hs2 : orderOf s = 2) (hsn : s ∈ normalizer (L : Set G)) :
    s ∈ centralizer (L : Set G) ∨ DInv L s 0 ∨ DInv L s 1 ∨ DInv L s 2 ∨ DInv L s 3 ∨
      DInv L s 4 :=
  ff_dinv_classify_aux hGA hL hs2 hsn

end CFSG.OddStandard.SmallF3.Omega
