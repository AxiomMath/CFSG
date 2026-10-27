module

public import CFSG.LocalAnalysis.OddStandard.L2Ree.Halves
public import CFSG.LocalAnalysis.OddStandard.L2Ree.Mult
public import CFSG.LocalAnalysis.OddStandard.L2Ree.SporadicArm
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.FixedComponent
import CFSG.LocalAnalysis.OddStandard.ChildHeHeld

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.HarrisLit.T1.SporRow (SporOddCompsAny)

theorem alt_arm_outcome {G Q D : Type} [Group G] [Group Q] [Group D] (eDQ : D ≃* Q)
    (h5 : ¬ Nonempty (Q ≃* alternatingGroup (Fin 5)))
    (h6 : ¬ Nonempty (Q ≃* alternatingGroup (Fin 6))) {n k : ℕ} (hk5 : 5 ≤ k) (hkn : k + 2 ≤ n)
    (hG : Nonempty (G ≃* alternatingGroup (Fin n)))
    (hD : Nonempty (D ≃* alternatingGroup (Fin k))) : AltOutcome G := by
  by_cases hk : k < 7
  · exfalso
    obtain ⟨eD⟩ := hD
    obtain rfl | rfl : k = 5 ∨ k = 6 := by omega
    · exact h5 ⟨eDQ.symm.trans eD⟩
    · exact h6 ⟨eDQ.symm.trans eD⟩
  · exact ⟨n, by omega, hG⟩


theorem l2_half_of_arms (hGA : TBLit.GriessMultipliersOdd)
    (hGC : TBLit.GriessMultipliersCentralCovers) (hT1 : HarrisLit.TheoremOne)
    (hGLS : GLS3OddLieAutComponentsInput)
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hEO : EvenLieOuterTwoComponentsInput)
    (hAny : ∀ s : TauCeti.SporadicName,
      (s ≠ .M11 ∧ s ≠ .M12 ∧ s ≠ .J1 ∧ s ≠ .J2 ∧ s ≠ .J3 ∧ s ≠ .HS) → SporOddCompsAny s) :
    L2Half := by
  rintro G _ _ L hS hlie ⟨p, f, hm⟩ h5 h6 hM S hcyc
  have := hS.simple
  have hq : IsQuasisimple L :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).1 hS.standard.1
  have hp : p.Prime := hm.admissible.1
  have hp2 : p ≠ 2 := p_ne_two_of_l2 hlie hm h5
  have hodd : Odd (Nat.card (center L)) :=
    odd_center_of_l2 hGA hGC hq hp hp2 hm
      (hM.imp_right fun ⟨_, _, _, _, _, _, _, _, hne⟩ => hne)
  obtain ⟨t, ht, ht2⟩ := exists_involution_of_standard hS.standard
  have hev : 2 ∣ Nat.card L := even_iff_two_dvd.1 (even_card_of_standard hS.standard)
  have hcfg := config_of_standard_psl_two hS.standard ht ht2 hev hp2 hodd hm S hcyc
  have hcat : Catalog G := hT1 G hS.nonab hS.kProper t L p f hcfg
  obtain ⟨D, hD, ⟨eDQ⟩⟩ := exists_fixed_component_of_standard hS.standard ht ht2
  have hσ : orderOf (MulAut.conj t : MulAut G) = 2 := orderOf_mulAut_conj_of_simple hS.nonab ht2
  rcases catalog_fixed_component hGLS hEI hEO hS.nonab hcat hσ hD with
    ⟨n, k, -, hk5, hkn, -, hG, hDk⟩ | ⟨hOdd, -⟩ | ⟨-, hnot, -⟩ | hSpor
  · exact Or.inl (alt_arm_outcome eDQ h5 h6 hk5 hkn hG hDk)
  · exact Or.inr (Or.inl hOdd)
  · exact absurd (MonoidHom.mem_range.2 ⟨t, rfl⟩) hnot
  · exact Or.inr (Or.inr (sporadic_arm_outcome hS ht ht2 hp hp2 hm h5 hSpor hAny))

end CFSG.OddStandard.L2Ree
