module

public import CFSG.GH74.Generic.BProg.Stage2QS
public import CFSG.GH74.Generic.BProg.Assembly
public import CFSG.GH74.Generic.BProg.NS.Leaf

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

@[expose] def NoJPrimeFor (P : ∀ (Kt : Type) [Group Kt], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2 x K → 1 < pRank 2 ↥(CxK x K) → P (↥K ⧸ pPrimeCore 2 ↥K) → False

theorem noJPrime_of_shapes (h1 : NoJPrimeFor QShape1) (h3 : NoJPrimeFor QShape3)
    (h4 : NoJPrimeFor QShape4) (h5 : NoJPrimeFor QShape5) : NoJPrimeFor QShapeNS := by
  intro G _ _ hyp noAlt x K hJ hr hP
  rcases hP with h | h | h | h
  · exact h1 G hyp noAlt x K hJ hr h
  · exact h3 G hyp noAlt x K hJ hr h
  · exact h4 G hyp noAlt x K hJ hr h
  · exact h5 G hyp noAlt x K hJ hr h

theorem noJPrime_all (hS : JPrimeNS) (hN : NoJPrimeFor QShapeNS) {G : Type} [Group G] [Finite G]
    (hyp : Hyp2 G) (noAlt : NoAltJ2 G) {x : G} {K : Subgroup G} (hJ : IsJ2 x K)
    (hr : 1 < pRank 2 ↥(CxK x K)) : False :=
  hN G hyp noAlt x K hJ hr (hS G hyp noAlt x K hJ hr)

theorem b_Gen4_liftJ2NS_of_noJPrime (hQ : Stage2QSNS) (hS : JPrimeNS) (hN : NoJPrimeFor QShapeNS) :
    B_Gen4_liftJ2NS := by
  intro G _ _ hs hn hrank hgen hkgh hsyl hL2 hthin x M hJ hnoalt hP
  have hyp : Hyp2 G := ⟨hs, hn, hrank, hgen, hkgh, hsyl, hL2, hthin⟩
  have hall : ∀ (x' : G) (M' : Subgroup G), IsJ2 x' M' → pRank 2 ↥(CxK x' M') ≤ 1 := by
    intro x' M' hJ'
    by_contra hgt
    exact noJPrime_all hS hN hyp hnoalt hJ' (not_le.1 hgt)
  have hcirc : IsJ2Circ x M := ⟨hJ, Or.inr hall⟩
  refine ⟨hQ G hyp hnoalt x M hcirc hP, ?_⟩
  have hge : 1 ≤ pRank 2 ↥(CxK x M) :=
    one_le_pRank_of_mem_order_two (mem_CxK_self hJ.1.1.2.2.1) hJ.1.1.1
  have := hall x M hJ
  omega

end CFSG.GH74.Generic.BProg.B1
