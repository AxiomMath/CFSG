module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4X
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4L
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4Sec

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem isPGroup_secImg_of_linkE4 (hodd : E4CoverOddFree) (hL : TightLargeHypR r n Y R S t)
    (hcase : LinkE4 R t) :
    ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore R)) t J) := by
  intro J hJ
  have hΦ := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
  have hJ' := subgroupOf_mem_linkRestrict (t := t) hJ
  obtain ⟨z, -, hz2, hsub⟩ := hΦ.cls.subnormal _ hJ'
  have hC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set ↥(linkGrp R t))) = ⊥ :=
    hodd ↥(linkGrp R t) hcase.2.2 z hz2
  have h1 := Balance.oddCoreIn_le_of_isSubnormal hsub
  have h2 : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set ↥(linkGrp R t))) = ⊥ := by
    unfold Balance.oddCoreIn
    rw [show componentClassificationOddCore ↥(Subgroup.centralizer ({z} : Set ↥(linkGrp R t))) =
      ⊥ from hC, Subgroup.map_bot]
  rw [h2, le_bot_iff] at h1
  have hO : classicalInvolutionOddCore
      ↥((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1
  exact (isPGroup_of_quot_oddCore_eq_bot (hΦ.twoGroup _ hJ') hO).of_equiv
    (Subgroup.subgroupOfEquivOfLe (le_linkGrp hJ))

end Cit3

section Layers


variable {r n : ℕ}

theorem tightE4LayersR_of (hodd : E4CoverOddFree) : TightE4LayersR r n := by
  intro Y _ _ R S t hL hc hcase hA J K' u x y x' hF
  have h2 := isPGroup_secImg_of_linkE4 hodd hL hcase
  rcases hcase.2.2 with hcov | hcov
  · exact Or.inl (exists_three_layers3 hL h2 hcov hF)
  · exact Or.inr (exists_two_layers9 hL h2 hcov hF)


theorem tightE4VtxSR_of_cover (hodd : E4CoverOddFree) (h9 : CITBelowU 3 2 n) :
    TightE4VtxSR 3 n :=
  tightE4VtxSR_of_layers (tightE4LayersR_of hodd) h9

end Layers

end CFSG.ClassicalInvolution.Q3.TL4
