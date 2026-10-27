module

public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Def
import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Sections
import CFSG.GH74.Generic.BProg.B2.Prop31
import CFSG.GH74.Generic.BProg.B2.T1Comp
import CFSG.GH74.Generic.BProg.B2.T1Basic
public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.GH74.Generic.BProg.B2.Defs

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

namespace Thm2AssemblyC2

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H : Subgroup G}

theorem barIn_nonabelian_of_simple (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M)
    (hF : barIn M H = generalizedFitting (Mbar M)) (hsimple : IsSimpleGroup ↥(barIn M H)) :
    ∃ a b : ↥(barIn M H), a * b ≠ b * a := by
  by_contra hcon
  have hcomm : ∀ a b : ↥(barIn M H), a * b = b * a := fun a b => by
    by_contra h
    exact hcon ⟨a, b, h⟩
  have hsolvbar : Group.IsSolvable (Mbar M) :=
    GHTrichotomy.isSolvable_of_eq_generalizedFitting hF hsimple hcomm
  have hsolvM : Group.IsSolvable ↥M := GHTrichotomy.isSolvable_of_quotient_pPrimeCore hsolvbar
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hs.pair.1.1.1.2.2
  have hsolvK : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKM)
      (Subgroup.inclusion_injective hKM)
  exact GHTrichotomy.not_isSolvable_of_isQuasisimple (TwoThin.isQuasisimple_hat hK) inferInstance

theorem faithful_of_simple (hF : barIn M H = generalizedFitting (Mbar M))
    (hsimple : IsSimpleGroup ↥(barIn M H)) (hnonab : ∃ a b : ↥(barIn M H), a * b ≠ b * a) :
    ∀ n : Mbar M, (∀ h ∈ barIn M H, n * h = h * n) → n = 1 := by
  intro n hn
  have hcent : n ∈ Subgroup.centralizer (generalizedFitting (Mbar M) : Set (Mbar M)) := by
    rw [← hF, Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hn h hh).symm
  have hnF : n ∈ barIn M H := hF ▸ centralizer_generalizedFitting_le (Mbar M) hcent
  have hcen : (⟨n, hnF⟩ : ↥(barIn M H)) ∈ Subgroup.center ↥(barIn M H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hn g g.2).symm
  rw [GHTrichotomy.center_eq_bot_of_simple_nonab hsimple hnonab, Subgroup.mem_bot] at hcen
  exact congrArg Subtype.val hcen

theorem shapeInCent_of_simple (hB : B_B2_g4) (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1Core x K M Q H) (hF : barIn M H = generalizedFitting (Mbar M))
    (hsimple : IsSimpleGroup ↥(barIn M H)) :
    ∃ hxM : x ∈ M,
      ShapeInCent (barIn M H) (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : Mbar M) (barIn M K) := by
  have hxM : x ∈ M := h1.Q_le (x_mem_Q hs)
  have hcomp := barIn_K_isCompIn hB hs h1.K_le hxM
  have hKH : K ≤ H := h1.H_min.1
  have hbarKH : barIn M K ≤ barIn M H := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, hKH hm, rfl⟩
  have hnonab := barIn_nonabelian_of_simple hs h1.K_le hF hsimple
  refine ⟨hxM, ?_⟩
  exact
    { normal := by
        rw [hF]
        exact (CFSG.LocalCores.generalized_fitting_characteristic).2
      simple := hsimple
      faithful := faithful_of_simple hF hsimple hnonab
      inv := Prop31.orderOf_mk_involution hxM hs.pair.1.1.1.1
      comp := Prop31.isCompIn_of_le (le_inf hbarKH hcomp.1) inf_le_right hcomp
      shape := Prop31.exists_shape hs h1.K_le (Prop31.isQuasisimple_of_isCompIn hcomp) }

theorem ghList_of_simple (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1Core x K M Q H)
    (hF : barIn M H = generalizedFitting (Mbar M)) (hsimple : IsSimpleGroup ↥(barIn M H)) :
    GHList ↥(barIn M H) :=
  GLS.IVK.ghList_of_subgroup_of_quotient hs.hyp.kgh hs.maxM.1
    (QuotientGroup.mk' (pPrimeCore 2 ↥M)) (QuotientGroup.mk'_surjective _) (barIn M H)
    hsimple (barIn_nonabelian_of_simple hs h1.K_le hF hsimple)

end Thm2AssemblyC2

end CFSG.GH74.Generic.BProg.B2
