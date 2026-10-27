module

public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LieType.Steinberg.TwistedD4.Quasisimple

public section

namespace CFSG.LieType.Simplicity

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg.TwistedD4

theorem fam_3d4_simplicity
    (G : Type) [Group G] (p f : ℕ)
    (h : ChevalleyExceptionalModel G .trialityD4 p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  have hq : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have := isSimpleGroup_of_mulEquiv (isQuasisimple_derived_twistedFixedGroup_D4 σ hq hK3 hσ) e
  exact ⟨inferInstance, this⟩

end CFSG.LieType.Simplicity
