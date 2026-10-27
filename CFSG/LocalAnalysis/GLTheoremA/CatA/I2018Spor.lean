module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2018

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator.YS08 (SporL3Down IsL3Kind)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem i2018_spor_absurd {X K J : Subgroup G} {x : G} {s : TauCeti.SporadicName}
    (hK : GLAPComponent 3 X K) (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx3 : x ^ 3 = 1)
    (hJ : GLAPComponent 3 (K ⊓ cx x) J) (hU : catalogIs (PSimple 3 J) CFSG.LocalAnalysis.GLTheoremA.S9.isU3eight)
    (hCover : I2018U38Cover) (hSpor : SporL3Down s)
    (eS : PSimple 3 K ≃* (TauCeti.CFSGIndex.sporadic s).Group) : False := by
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hK
  haveI := hsimple
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx3
  have hα3 : (chevAut 3 K ⟨x, hxN⟩) ^ 3 = 1 := chevAut_pow_eq_one 3 K hxN hx3
  have hJ' := glaPComponent_chevTransfer Nat.prime_three hxN hxp hJ
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hxN hxp hJ
  have hU' : catalogIs (PSimple 3 (chevTransfer 3 K J)) CFSG.LocalAnalysis.GLTheoremA.S9.isU3eight :=
    catalogIs_congr' eJ hU
  have hq' : CFSG.Open.IsQuasisimple (PQuot 3 (chevTransfer 3 K J)) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ'
  have hL3 : IsL3Kind 2 (PQuot 3 (chevTransfer 3 K J)) := hCover _ hq' hU'
  exact hSpor (PSimple 3 K) hsimple hna ⟨eS⟩ _ hα3 _ hJ' 2 hL3

end CFSG.LocalAnalysis.GLTheoremA.I2018

end
