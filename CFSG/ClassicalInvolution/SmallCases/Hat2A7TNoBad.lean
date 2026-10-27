module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TKey2
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TSylow
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TOdd

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

section NoBad

variable {F : Type} [Group F] [Finite F] [IsSimpleGroup F]

theorem false_of_noBadPair (hnab : ∃ a b : F, a * b ≠ b * a)
    (GS : GoldschmidtStronglyClosedExponent) (IH : ClassicalCommuteBelow F)
    {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hnb : ∀ g : F, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) →
      CommOrEq K (K.map (MulAut.conj g).toMonoidHom)) : False := by
  have hZ : CenterTrivial F := fun x hx => center_trivial_of_simple hnab x hx
  exact false_of_key hnab GS IH hK fun a ha ha1 g hb =>
    mem_normalizer_of_conj_mem_of_noBadPair hZ IH hK hnb ha ha1 hb

theorem false_of_odd_twins (hnab : ∃ a b : F, a * b ≠ b * a)
    (GS : GoldschmidtStronglyClosedExponent) (IH : ClassicalCommuteBelow F)
    (P1 : ClassicalQuasisimple F) {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hodd : Odd ((Subgroup.centralizer ({z} : Set F) ⊓ Subgroup.normalizer (K : Set F)).relIndex
      (Subgroup.centralizer ({z} : Set F)))) : False :=
  false_of_noBadPair hnab GS IH hK fun _ hg =>
    commOrEq_of_odd_relIndex (fun x hx => center_trivial_of_simple hnab x hx) IH P1 hK hodd hg

end NoBad

end CFSG.ClassicalInvolution.Hat2A7T
