module

public import CFSG.GH74.QTGen4.DSGen4.OpenLeavesAmal
public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem l34_dc [DSLeaf LeafL34DC] (Mdl : L34Model) (hMdl : L34ModelFacts Mdl) :
    ∀ (σ : MulAut ↥(Mdl.M1 ⊓ Mdl.M2)), (∀ b : ↥(Mdl.M1 ⊓ Mdl.M2), (b : Mdl.Y) ∈ pCoreOf 2 Mdl.M1 ↔
        ((σ b : ↥(Mdl.M1 ⊓ Mdl.M2)) : Mdl.Y) ∈ pCoreOf 2 Mdl.M1) →
      ∃ (a₁ : MulAut ↥Mdl.M1) (a₂ : MulAut ↥Mdl.M2),
        (∀ m : ↥Mdl.M1, (m : Mdl.Y) ∈ Mdl.M2 ↔ ((a₁ m : ↥Mdl.M1) : Mdl.Y) ∈ Mdl.M2) ∧
        (∀ m : ↥Mdl.M2, (m : Mdl.Y) ∈ Mdl.M1 ↔ ((a₂ m : ↥Mdl.M2) : Mdl.Y) ∈ Mdl.M1) ∧
        ∀ (b : ↥(Mdl.M1 ⊓ Mdl.M2)) (m₁ : ↥Mdl.M1) (m₂ : ↥Mdl.M2), (m₁ : Mdl.Y) = b →
          ((a₁ m₁ : ↥Mdl.M1) : Mdl.Y) = (m₂ : Mdl.Y) →
            ((a₂ m₂ : ↥Mdl.M2) : Mdl.Y) = ((σ b : ↥(Mdl.M1 ⊓ Mdl.M2)) : Mdl.Y) :=
  DSLeaf.holds (L := LeafL34DC) Mdl hMdl

end CFSG.GH74.QTGen4.DSGen4
