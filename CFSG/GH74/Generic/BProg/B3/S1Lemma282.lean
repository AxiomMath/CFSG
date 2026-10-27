module

public import CFSG.GH74.Generic.BProg.B3.S1Lemma282Aux
public import CFSG.GH74.Generic.BProg.B3.S1Lemma282ANeX

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

section Lemma282


variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem s1_lemma282 (hc : Ctx21 G x K A a D J)
    (h1 : B1.PilotS1.QShape1Big (↥K ⧸ pPrimeCore 2 ↥K))
    {J₁ J₂ : Subgroup G} (hS : S1SplitMod K A x a J₁ J₂) :
    x ∈ normalizer (J : Set G) ∧ x ∉ centralizerSection J (pPrimeCoreOf 2 J) ∧ J₂ ≤ J ∧
      A ≤ normalizer (J : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K) := B1.PilotS1.QShape1Big.qShape1 h1
  obtain ⟨-, -, hxA, -⟩ := s1_basic hc hQ1
  have hax : a ≠ x := s1_a_ne_x hc hQ1
  have hx : orderOf x = 2 := hc.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J := hc.obs.comp
  have hxa : a ∈ centralizer ({x} : Set G) := hc.src.1 hc.a_mem
  have hx1 : x ≠ 1 := fun h => by simp [h] at hx
  have hbal := Lemma212S45.pLayerOf_le_of_balance hx hK hxa
  have hxL : x ∈ pLayerOf 2 (centralizer ({a} : Set G)) := hbal hS.x_mem_layer
  have hxN : x ∈ normalizer (J : Set G) := S1Lemma282Aux.pLayerOf_le_normalizer hJ hxL
  have hxS : x ∉ centralizerSection J (pPrimeCoreOf 2 J) := fun hcs =>
    (hc.cA_eq x hxA hcs).elim hx1 (fun h => hax h.symm)
  have haS : a ∈ centralizerSection J (pPrimeCoreOf 2 J) := hc.obs.y_mem_centralizerSection
  have hJ₂K : IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) J₂ := hS.comp₂
  have hJ₂nS : ¬ J₂ ≤ centralizerSection J (pPrimeCoreOf 2 J) := by
    intro hle
    apply hxS
    have h2 := hle hS.xu_mem
    have : x = (x * a) * a⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ haS)
  have hJ₂Y : J₂ ≤ centralizer ({a} : Set G) := hJ₂K.1.trans inf_le_right
  have hJ₂self : pLayerOf 2 J₂ = J₂ := Lemma212S45.pLayerOf_self hJ₂K
  have hJ₂L' : J₂ ≤ pLayerOf 2 (K ⊓ centralizer ({a} : Set G)) := le_sSup hJ₂K
  have hJ₂L : J₂ ≤ pLayerOf 2 (centralizer ({a} : Set G)) := hJ₂L'.trans hbal
  have hJle : J ≤ pumpUp 2 J₂ a := by
    refine Lemma212Aux.le_pumpUp_of_not_le_cSec hJ ?_ ?_
    · rw [inf_eq_left.2 hJ₂Y, hJ₂self]
      exact hJ₂L
    · rw [inf_eq_left.2 hJ₂Y, hJ₂self]
      exact hJ₂nS
  obtain ⟨hPC, hJ₂P, -⟩ := S1Lemma282Aux.pumpUp_isPCompIn hx hK hxa hJ₂K hxL
  have hJeq : J = pumpUp 2 J₂ a := FalseCtxS45Comp.eq_of_le hJ hPC hJle
  refine ⟨hxN, hxS, hJeq ▸ hJ₂P, fun c hcA => ?_⟩
  have hcY : c ∈ centralizer ({a} : Set G) := by
    obtain ⟨hAc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hc.src.2.1
    exact mem_centralizer_singleton_iff.mpr (hAc c hcA a hc.a_mem)
  have := S1Lemma282Aux.mem_normalizer_pumpUp hJ₂Y hJ₂self hcY (hS.A_norm hcA).2
  rwa [← hJeq] at this

end Lemma282

end CFSG.GH74.Generic.BProg.B3
