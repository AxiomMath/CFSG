module

public import Certificates.Certificate2037

public section

namespace CFSG.ComponentClassification.WittDesign

open Equiv

theorem molsLevel2 : MolsLevel2 :=
  Certificates.certificate2037

theorem mols_classification (r₂ r₃ r₄ : Fin 3 → Perm (Fin 4)) (h₂ : ∀ x : Fin 3, r₂ x 0 = x.succ)
    (hc₂ : ColumnsInj (latinSq r₂)) (hc₃ : ColumnsInj (latinSq r₃))
    (hc₄ : ColumnsInj (latinSq r₄)) (h₂₃ : Orth (latinSq r₂) (latinSq r₃))
    (h₂₄ : Orth (latinSq r₂) (latinSq r₄)) (h₃₄ : Orth (latinSq r₃) (latinSq r₄)) :
    (r₂ = rA ∧ r₃ = rB ∧ r₄ = rC) ∨ (r₂ = rA ∧ r₃ = rC ∧ r₄ = rB) :=
  molsLevel2 r₂ h₂ hc₂ r₃ hc₃ h₂₃ r₄ hc₄ h₂₄ h₃₄

end CFSG.ComponentClassification.WittDesign
