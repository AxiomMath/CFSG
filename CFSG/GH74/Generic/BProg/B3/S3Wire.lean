module

public import CFSG.GH74.Generic.BProg.B3.S3T2Excl
public import CFSG.GH74.Generic.BProg.B3.S3T2HKB
public import CFSG.GH74.Generic.BProg.B3.S3T4U5
public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Done
public import CFSG.GH74.Generic.BProg.B2.PumpupTableProved
public import CFSG.GH74.Generic.BProg.B2.PuL4GraphUniFinal
public import CFSG.GH74.Generic.BProg.B2.PuG2Odd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup

structure BootA7id (G : Type) [Group G] [Finite G] : Prop where
  a7id : ∀ (x : G) (K A B M : Subgroup G) (a : G) (D J : Subgroup G), Boot15B G x K A B M →
    a ∈ A → Obs32 A a D J →
    (∃ w ∈ pPrimeCoreOf 2 M, w ∈ centralizer ({a} : Set G) ∧ w ∈ normalizer (J : Set G) ∧
      w ∉ centralizerSection J (pPrimeCoreOf 2 J)) →
    Nonempty ((↥J ⧸ pPrimeCore 2 ↥J) ≃* alternatingGroup (Fin 7))
  l15A7 : ∀ (x : G) (K A : Subgroup G) (a : G) (D J : Subgroup G), Ctx21 G x K A a D J →
    QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → Hyp15A7 G

section Wire

theorem bootKG_of_a7id
    {G : Type} [Group G] [Finite G] (ha7id : BootA7id G) : BootKG G where
  a7id := ha7id.a7id
  excl := excl_of_mem
  h175 := h175_of b_B2_g4_proved B2.PumpupOutOrders.pumpupTableU_proved
    (fun _ _ _ H t L hs h4 hJ => B2.puL4m_of_gen4_proved H t L hs h4 hJ)
    (fun _ _ _ H t L hs hJ => B2.puG2Odd_of_shape H t L hs hJ) leaf514S3_proved
  loc28 := loc28_of_b2 b_B2_g4_proved
  hKB := hKB_proved
  l15A7 := ha7id.l15A7

end Wire

end CFSG.GH74.Generic.BProg.B3
