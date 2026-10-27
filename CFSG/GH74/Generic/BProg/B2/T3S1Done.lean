module

public import CFSG.GH74.Generic.BProg.B2.T3S1
public import CFSG.GH74.Generic.BProg.B2.T3S1Uni
public import CFSG.GH74.Generic.BProg.B2.T3WireDefs

public section

namespace CFSG.GH74.Generic.BProg.B2.T3S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.Assembly.LowTwoRank Subgroup

theorem s1Facts_of_qShape1 : ∀ (Kt : Type) [Group Kt], QShape1 Kt → S1Facts Kt := by
  intro Kt _ hK
  rcases hK with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · exact (s1Facts_lin hF).of_mulEquiv e.symm
  · exact (s1Facts_uni hF hq).of_mulEquiv e.symm

variable {G : Type} [Group G] [Finite G]

theorem false_of_c1_S1 {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1 x K M Q H) (h2 : Stage2Concl2 M) (hAK : A ≤ K)
    (hsh : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) (hc1 : barIn M H = barIn M K)
    (hCx : centralizer ({x} : Set G) ≤ M) (hr : pRank 2 (CMbar M K) ≤ 1) : False :=
  false_of_c1_S1_of s1Facts_of_qShape1 hs h1 h2 hAK hsh hc1 hCx hr

theorem stage2Thm3S1_form : ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H : Subgroup G),
    Stage2Setup G x K A M P Q → Stage2Concl1 x K M Q H → Stage2Concl2 M → Stage2Cor2 x K A M H →
      A ≤ K → QShape1 (↥K ⧸ pPrimeCore 2 ↥K) → barIn M H = barIn M K →
        centralizer ({x} : Set G) ≤ M → pRank 2 (CMbar M K) ≤ 1 → False :=
  fun _ _ _ _ _ _ _ _ _ _ hs h1 h2 _ hAK hsh hc1 hCx hr =>
    false_of_c1_S1 hs h1 h2 hAK hsh hc1 hCx hr

end CFSG.GH74.Generic.BProg.B2.T3S1

namespace CFSG.GH74.Generic.BProg.B2

theorem stage2Thm3S1_proved : Stage2Thm3S1 := T3S1.stage2Thm3S1_form

end CFSG.GH74.Generic.BProg.B2
