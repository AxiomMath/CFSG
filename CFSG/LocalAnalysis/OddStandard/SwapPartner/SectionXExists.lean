module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.SectionX
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaG

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern CFSG.OddStandard.AltStdBal

open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

theorem map_Agrp_eq_commutator_twoSecMap (hC : CentData z ι) :
    ((Agrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G))).map
        (QuotientGroup.mk' (zpowers (selfC (z * ι τ₀)))) =
      (⁅twoSecMap (z * ι τ₀) (Siggrp ι), twoSecMap (z * ι τ₀) (Siggrp ι)⁆ :
        Subgroup (TwoSec (z * ι τ₀))) :=
  (commutator_twoSecMap_Siggrp hC).symm

theorem exists_swapShape_twoSec [Finite G] (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) :
    ∃ Sg V : Subgroup (TwoSec (z * ι τ₀)),
      SwapShape (QuotientGroup.mk ⟨z, z_mem_centralizer_x₂ hC⟩ : TwoSec (z * ι τ₀)) Sg V ∧
        ((Agrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G))).map
            (QuotientGroup.mk' (zpowers (selfC (z * ι τ₀)))) =
          (⁅Sg, Sg⁆ : Subgroup (TwoSec (z * ι τ₀))) := by
  obtain ⟨g, hg⟩ := exists_gElt hC hx hP2
  exact ⟨twoSecMap (z * ι τ₀) (Siggrp ι), twoSecMap (z * ι τ₀) (Dgrp z g),
    swapShape_twoSec hC hg (z_mem_centralizer_x₂ hC), map_Agrp_eq_commutator_twoSecMap hC⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
