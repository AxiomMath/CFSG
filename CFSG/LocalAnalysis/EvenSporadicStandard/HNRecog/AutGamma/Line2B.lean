module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.LineGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.A8Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open Equiv Equiv.Perm CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem config_2B : ∃ t : alternatingGroup (Fin 8), FF t :=
  ⟨ffElem (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7) (by decide) (by decide), by decide⟩

theorem hasLine_2B (hF : IsF5Type a z) (hL : F5Local G a z) : HasLine a z .k2B .k2A .k2A := by
  obtain ⟨E⟩ := A8Emb.nonempty hL
  obtain ⟨t, ht⟩ := config_2B
  have haa : a * a = 1 := mul_self_of_isConj hF (IsConj.refl a)
  have hc : E.φ t * E.b = E.b * E.φ t := (E.comm_b t).symm
  refine ⟨a, IsConj.refl a, a * E.φ t, ⟨E.isConj_a_mul ht, ?_⟩, E.b, E.hb, ⟨?_, ?_⟩⟩
  · rw [← mul_assoc, haa, one_mul]
    exact E.isConj_z ht
  · have : a * E.φ t * E.b = a * E.b * E.φ t := by rw [mul_assoc, hc, ← mul_assoc]
    rw [this]
    exact E.fig8b_ab t ht.cycleType
  · have : a * (a * E.φ t * E.b) = E.b * E.φ t := by
      rw [← mul_assoc, ← mul_assoc, haa, one_mul, hc]
    rw [this]
    exact E.fig8b_b t ht.cycleType

theorem line_2B (hF : IsF5Type a z) (hL : F5Local G a z) :
    ∀ x ∈ orb2B a z a, ∃ y ∈ orb2A a a, x * y ∈ orb2A a a :=
  line_of_hasLine (k₁ := .k2B) (k₂ := .k2A) (k₃ := .k2A) (isConjOrbit_orb2B hL)
    (hasLine_2B hF hL)

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
