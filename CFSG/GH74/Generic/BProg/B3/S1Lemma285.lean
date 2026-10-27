module

public import CFSG.GH74.Generic.BProg.B3.S1Lemma282Aux
public import CFSG.GH74.Generic.BProg.B3.S1Split

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

section Lemma285

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem s1_lemma285 (hc : Ctx21 G x K A a D J)
    (h1 : B1.PilotS1.QShape1Big (↥K ⧸ pPrimeCore 2 ↥K))
    {J₁ J₂ : Subgroup G} (hS : S1SplitMod K A x a J₁ J₂) (hJ₂ : J₂ ≤ J) (hJ₁ : ¬ J₁ ≤ J) :
    ∃ J' : Subgroup G, IsPCompIn 2 (centralizer ({a} : Set G)) J' ∧ J₁ ≤ J' ∧ J' ≠ J ∧
      x ∈ normalizer (J' : Set G) ∧ J' ≤ centralizerSection J (pPrimeCoreOf 2 J) := by
  classical
  have _ := h1
  have _ := hJ₂
  have hx : orderOf x = 2 := hc.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have hxa : a ∈ centralizer ({x} : Set G) := hc.src.1 hc.a_mem
  have hxL : x ∈ pLayerOf 2 (centralizer ({a} : Set G)) :=
    (Lemma212S45.pLayerOf_le_of_balance hx hK hxa) hS.x_mem_layer
  obtain ⟨hPC, hJ₁P, hxP⟩ := S1Lemma282Aux.pumpUp_isPCompIn hx hK hxa hS.comp₁ hxL
  have hne : pumpUp 2 J₁ a ≠ J := fun h => hJ₁ (h ▸ hJ₁P)
  exact ⟨pumpUp 2 J₁ a, hPC, hJ₁P, hne, hxP,
    FalseCtxS45Comp.le_cSec_of_ne hc.obs.comp hPC hne.symm⟩

end Lemma285

end CFSG.GH74.Generic.BProg.B3
