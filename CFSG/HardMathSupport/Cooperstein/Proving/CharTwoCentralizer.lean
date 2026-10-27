module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

variable {G : Type} [Group G]

theorem le_pCoreOf_two_of_centralizes {X B : Subgroup G}
    (hX : CFSG.QuasithinUnique.CharTwo X) (hBX : B ≤ X)
    (hC : ∀ b ∈ B, ∀ x ∈ CFSG.Open.pCoreOf 2 X, b * x = x * b) :
    B ≤ CFSG.Open.pCoreOf 2 X := by
  intro b hb
  have hcent : b ∈ Subgroup.centralizer ((CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => (hC b hb x hx).symm
  exact hX ⟨hBX hb, hcent⟩

end CFSG.HardMathSupport.Cooperstein.Proving

end
