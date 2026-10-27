module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.LitX
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporNum

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.HarrisLit.T1.SporRow (not_oddLieOrder_sporOrder)
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)

theorem oddLieCompNotSporadic_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Catalog)
    (hO : LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, Nat.card (Carrier s) = sporOrder s) :
    Hyp.OddLieCompNotSporadic := by
  intro Y _ _ N' hF hodd t ht A hA s'' hs
  have : IsSimpleGroup ↥N' := hF.isSimpleGroup
  have hcat : Catalog ↥N' := by
    obtain ⟨τ, n, p, f, -, -, -, h⟩ := hodd
    exact lieModel_catalog _ τ n p f h
  have hsolv : Group.IsSolvable (Outer ↥N') := hSch ↥N' hF.nonabelian hcat
  have := hF.normal
  have hperf : Group.IsPerfect ↥A := hA.isQuasisimple.1
  have hAN : A ≤ N' := le_of_perfect_of_solvable_outer hF.centralizer_le
  obtain ⟨σ, D, hσ, hD, -, ⟨e⟩⟩ := exists_fixedComponent hF ht hA hAN
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hmod⟩ := hodd
  obtain ⟨g⟩ := hs
  have hc : Nat.card (↥D ⧸ center ↥D) = sporOrder s'' := by
    rw [Nat.card_congr ((quotientCenterEquiv e).trans g).toEquiv, hcard]
  rcases hGLS ↥N' τ n p f hp hp2 hadm hmod σ hσ D hD with
    ⟨τ', n', f', hadm', hmod'⟩ | ⟨-, -, -, hL⟩
  · obtain ⟨-, h1, h2⟩ := hO _ τ' n' p f' hadm' hmod'
    rw [hc] at h1 h2
    exact not_oddLieOrder_sporOrder s'' ⟨τ', n', p, f', hp, hp2, hadm', h1, h2⟩
  · have hadmL : StatedLieAdmissible .PSL 2 2 3 :=
      ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩
    obtain ⟨-, h1, -⟩ := hO _ .PSL 2 2 3 hadmL hL
    have h504 : Nat.card ↥D = 504 := by
      simp only [lieOrderDivisor, lieOrderNumerator] at h1
      norm_num [Finset.Icc_self] at h1
      omega
    have hle : Nat.card (↥D ⧸ center ↥D) ≤ Nat.card ↥D :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [hc, h504] at hle
    revert hle
    cases s'' <;> norm_num [sporOrder, CFSG.ComponentClassification.GSThmB.QPUSpor.sporFactors]

end CFSG.ComponentClassification.CatFC
