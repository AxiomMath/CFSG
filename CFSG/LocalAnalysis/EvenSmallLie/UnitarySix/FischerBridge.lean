module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerMain
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntMain

public section

namespace CFSG.EvenSmallLie.UnitarySix.Fischer

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L E : Subgroup G}
  {p : L →* Equiv.Perm (Fin 693)}

theorem fischerHyp_of_hunt
    (H : Hunt.Hyp t L E p) : FischerHyp t L E p :=
  ⟨H.todd', H.centralizer_eq'.1, H.tv, H.inj, H.m22, H.ker, H.card_sylow, H.card_sylowN⟩

theorem fi22_of_huntHyp
    [IsSimpleGroup G] (H : Hunt.Hyp t L E p) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 :=
  fi22_of_hunt (fischerHyp_of_hunt H)

theorem fi22_of_davisSolomon
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (H : ToddOrbit.Hyp t L E p) (D : DavisSolomonFacts G t L E)
    (hCE : centralizer (E : Set G) ≤ E ⊔ centralizer (L : Set G))
    (hCL : centralizer (L : Set G) = zpowers t) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 :=
  fi22_of_huntHyp (Hunt.Hyp.of_simple hnonab H D hCE hCL)

end CFSG.EvenSmallLie.UnitarySix.Fischer
