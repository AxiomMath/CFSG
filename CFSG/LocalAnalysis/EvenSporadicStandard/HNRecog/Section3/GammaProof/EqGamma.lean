module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Conn
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Mem

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog CFSG.Monster.GMS

variable {G : Type} [Group G] [Finite G] {a z : G}

theorem gamma_eq_gamma (H : GammaHyps a z) {y : G} (hy : IsConj a y) : y ∈ gammaSet a z a := by
  have key : ∀ u v : ConjVert a, (Gamma a).Walk u v → (u : G) ∈ gammaSet a z a →
      (v : G) ∈ gammaSet a z a := by
    intro u v p
    induction p with
    | nil => exact id
    | cons hadj _ ih =>
      exact fun hu => ih (gamma_mem_gamma H hu ⟨Subtype.prop _, (gamma_adj_iff.1 hadj).2⟩)
  obtain ⟨p⟩ := (gamma_connected H).preconnected ⟨a, IsConj.refl a⟩ ⟨y, hy⟩
  exact key _ _ p (gamma_mem_gammaSet_iff.2 (Or.inl rfl))

end CFSG.EvenSporadicStandard.HNRecog.Section3
