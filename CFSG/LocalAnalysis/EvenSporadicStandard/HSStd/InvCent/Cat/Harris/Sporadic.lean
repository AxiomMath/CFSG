module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Setup
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentZ2A6
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicNoA6

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Subgroup CFSG CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


variable {G : Type} [Group G] [Finite G] {S : Subgroup G} [S.Normal] {t : G}

theorem sporadic_arm {s : TauCeti.SporadicName}
    (es : ↥S ≃* CFSG.Blueprint.NativeSporadic.Carrier s) (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) : s = .HS := by
  have hσ : orderOf (MulAut.conjNormal t : MulAut ↥S) = 2 := orderOf_conjNormal h.cent h.ord
  obtain ⟨e⟩ := commutator_fixed_equiv h ζ
  haveI : (commutator ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S))).Normal :=
    Subgroup.commutator_normal ⊤ ⊤
  have hD := isComponent_of_alt6 _ e
  have hcard := card_quotient_center_alt6 e
  rcases sporadic_comp_360 h.simple h.nonab es hσ hD hcard with ⟨hs, -⟩ | ⟨hs, hout⟩
  · exact hs
  · exfalso
    subst hs
    have h1 := he_outer_fixedSubgroup_card es hσ hout
    have h2 := Nat.le_of_dvd (by norm_num) (card_fixed_dvd (S := S) ζ)
    omega

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
