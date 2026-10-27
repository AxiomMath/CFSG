module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddFam
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1All
public import CFSG.ClassicalInvolution.Q3.TA3FrameD43
public import CFSG.LargeExtraspecial.S5Comp

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.Foote5.OddLieCore (oddFixed)

set_option linter.unusedSectionVars false

theorem hasCompOrSolv_of_oddFixed_component {Y : Type} [Group Y] (x : Y)
    (h : ∃ Xc : Subgroup Y, GorensteinWalter.IsComponentOf Xc (oddFixed (MulAut.conj x))) :
    HasCompOrSolv (centralizer ({x} : Set Y)) := by
  obtain ⟨Xc, hXc⟩ := h
  have h1 := CFSG.ClassicalInvolution.Q3.TA3.Frame.isComponentOf_of_oddFixed hXc
  have h2 := (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf h1.1).1 h1
  exact Or.inr ⟨_, (isComponent_iff_open _).2 h2⟩


theorem solvableOrComponent_of_oddFixed_component {X Y : Type} [Group X] [Group Y] (E : X ≃* Y)
    (z : X) (h : ∃ Xc : Subgroup Y, GorensteinWalter.IsComponentOf Xc (oddFixed (MulAut.conj (E z)))) :
    SolvableOrComponent X z :=
  solvableOrComponent_of_mulEquiv E z (hasCompOrSolv_of_oddFixed_component (E z) h)

theorem oddDichotomyFamily_E7 : OddDichotomyFamily .E7 := by
  intro X _ _ n p f hp hp2 hadm hX z hz
  obtain ⟨K, _, _, hK, ⟨E⟩⟩ := nonempty_mulEquiv_adjointGroup .E7
    (hX.chevalleyExceptionalModel (by decide)).2
  have hf : 1 ≤ f := hadm.2.1
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  set z' : adjointGroup .E7 K := E z with hz'def
  have hz' : orderOf z' = 2 := (orderOf_injective E.toMonoidHom E.injective z).trans hz
  have hαg : ∀ h : adjointGroup .E7 K, ((MulAut.conj z' : MulAut (adjointGroup .E7 K)) h : ModGL .E7 K) =
      (z' : ModGL .E7 K) * rootDiagUnit .E7 (1 : Fin Tag.E7.rank → Kˣ) * (h : ModGL .E7 K) *
        (rootDiagUnit .E7 (1 : Fin Tag.E7.rank → Kˣ))⁻¹ * (z' : ModGL .E7 K)⁻¹ := by
    intro h
    rw [rootDiagUnit_one, mul_one, inv_one, mul_one]
    rfl
  have hα : (MulAut.conj z' : MulAut (adjointGroup .E7 K)) ^ 2 = 1 := by
    rw [← map_pow, ← hz', pow_orderOf_eq_one, map_one]
  exact solvableOrComponent_of_oddFixed_component E z
    (HarrisLit.L33.E1.e7_innerDiag_exists_component K hKodd _ hα ⟨z', 1, hαg⟩)

theorem oddDichotomyFamily_of_twisted {t : StatedLieTag} {T : TwistTag}
    (ht : t ∈ chevalleyExceptionalTags)
    (hmodel : ∀ (J : Type) [Group J] (p f : ℕ), ChevalleyExceptionalModel J t p f →
      TwistedChevalleyModel J T (p ^ f)) : OddDichotomyFamily t := by
  intro X _ _ n p f hp hp2 hadm hX z hz
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨E⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card T hp hf
    (hmodel X p f (hX.chevalleyExceptionalModel ht))
  set x := E z with hxdef
  have hx : orderOf x = 2 := (orderOf_injective E.toMonoidHom E.injective z).trans hz
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  exact solvableOrComponent_of_oddFixed_component E z
    (HarrisLit.L33.E1.twisted_inner_exists_component T p f hp hp2 hf K hK σ hσ x hx2 hx1)

theorem oddDichotomyFamily_twistedE6 : OddDichotomyFamily .twistedE6 :=
  oddDichotomyFamily_of_twisted (T := .E6) (by decide) (fun _ _ _ _ h => h.2)

theorem oddDichotomyFamily_trialityD4 : OddDichotomyFamily .trialityD4 :=
  oddDichotomyFamily_of_twisted (T := .D4) (by decide) (fun _ _ _ _ h => h.2)

end CFSG.ComponentClassification.CatFC.DS81
