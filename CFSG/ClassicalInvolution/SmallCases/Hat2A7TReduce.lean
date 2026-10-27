module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TNoBad
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TOddClique

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

@[expose] def TwinNoBadPairEven : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ClassicalCommuteBelow F → ClassicalQuasisimple F →
    ∀ (K : Subgroup F) (z : F), IsClassical2A7 ⊤ K z →
      ¬ (Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F)) →
      ¬ Odd (Nat.card (cliqueSet K)) →
      ¬ Odd ((Subgroup.centralizer ({z} : Set F) ⊓ Subgroup.normalizer (K : Set F)).relIndex
        (Subgroup.centralizer ({z} : Set F))) →
      ∀ g : F, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) →
        CommOrEq K (K.map (MulAut.conj g).toMonoidHom)

theorem twinExclusion_of_inputs (GS : GoldschmidtStronglyClosedExponent)
    (hB : TwinNoBadPairEven) : TwinExclusion := by
  intro F _ _ _ hnab IH P1 K z hK ht
  by_cases hm : Odd (Nat.card (cliqueSet K))
  · exact false_of_odd_clique hnab GS IH P1 hK hm
  by_cases hodd : Odd ((Subgroup.centralizer ({z} : Set F) ⊓
      Subgroup.normalizer (K : Set F)).relIndex (Subgroup.centralizer ({z} : Set F)))
  · exact false_of_odd_twins hnab GS IH P1 hK hodd
  exact false_of_noBadPair hnab GS IH hK fun g hg => hB F hnab IH P1 K z hK ht hm hodd g hg

end CFSG.ClassicalInvolution.Hat2A7T
