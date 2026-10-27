module

public import CFSG.GH74.Generic.BProg.B3.S3Wire
public import CFSG.GH74.Generic.BProg.B3.S3Sec29JBG
public import CFSG.GH74.Generic.BProg.B3.S3T2L291P
public import CFSG.GH74.Generic.BProg.B3.S3KG16c
public import CFSG.GH74.Generic.BProg.B3.S3KG21d
public import CFSG.GH74.Generic.BProg.B3.S3KG31e
public import CFSG.GH74.Generic.BProg.B3.S3T3Fin
public import CFSG.GH74.Generic.BProg.B3.S3T4NoL3

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup

theorem sec29Final_of_tab52w
    {G : Type} [Group G] [Finite G] (htab : Tab52w G) :
    Sec29Final G :=
  sec29Final_of_lemma2910 (lemma2910_fullB ⟨htab, noL3PumpupOfA7Step_proved⟩
    ⟨kg31e_proved G, kg21d_proved, s16cKG_proved⟩)

theorem hSD29_of_leaves₃
    (ha7id : ∀ (G : Type) [Group G] [Finite G], BootA7id G)
    (htab : ∀ (G : Type) [Group G] [Finite G], Tab52w G) :
    ∀ {G : Type} [Group G] [Finite G] {x a : G} {K A D J : Subgroup G},
      Ctx21 G x K A a D J → B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K) →
        pRank 2 ↥(GLS.CxK x K) ≤ 1 := by
  intro G _ _ x a K A D J hc hSD
  exact prop292_sd (bootKG_of_a7id (ha7id G)) b_B2_g4_proved lemma291_proved
    (sec29Final_of_tab52w (htab G)) hc hSD

end CFSG.GH74.Generic.BProg.B3
