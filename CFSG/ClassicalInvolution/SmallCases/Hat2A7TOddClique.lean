module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TKey
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TSylow

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

section Final

variable {F : Type} [Group F] [Finite F] [IsSimpleGroup F]

theorem false_of_odd_clique (hnab : ∃ a b : F, a * b ≠ b * a)
    (GS : GoldschmidtStronglyClosedExponent) (IH : ClassicalCommuteBelow F)
    (P1 : ClassicalQuasisimple F) {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hodd : Odd (Nat.card (cliqueSet K))) : False := by
  have hZ : CenterTrivial F := fun x hx => center_trivial_of_simple hnab x hx
  exact false_of_key hnab GS IH hK fun a ha ha1 g hb =>
    mem_normalizer_of_conj_mem hZ IH P1 hK hodd ha ha1 hb

end Final

end CFSG.ClassicalInvolution.Hat2A7T
