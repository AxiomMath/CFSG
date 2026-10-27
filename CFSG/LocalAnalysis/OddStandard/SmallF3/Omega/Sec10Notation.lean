module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Ctx

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def hatCent (t z : G) : Subgroup G :=
  centralizer ({z} : Set G) ⊓ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G)

@[expose] def IsStrClosedModZ (t z : G) (X : Subgroup G) : Prop :=
  ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * t * h ∈ X ⊔ zpowers z →
    h⁻¹ * t * h = t ∨ h⁻¹ * t * h = t * z

@[expose] def secA2 (t r : G) (K1 K2 : Subgroup G) : Subgroup G :=
  (secQ K1 K2 ⊓ centralizer ({r} : Set G)) ⊔ zpowers r ⊔ zpowers t

@[expose] def secCMB (t : G) (S L : Subgroup G) : Subgroup G :=
  secM t S L ⊓ centralizer ((secB S L : Subgroup G) : Set G)

@[expose] def secCMt (t : G) (S L : Subgroup G) : Subgroup G :=
  secM t S L ⊓ centralizer ({t} : Set G)

@[expose] def secMstar (t : G) (S L : Subgroup G) : Subgroup (MulAut ↥(secA t S L)) :=
  autIn (secM t S L) (secA t S L)

@[expose] def secTB (t : G) (S L : Subgroup G) : Set G :=
  cosetSet t (secB S L)

@[expose] def IsPermMod6 (A H : Subgroup G) (Alt : Subgroup (Equiv.Perm (Fin 6))) : Prop :=
  ∃ φ : (Fin 6 → ZMod 2) → G,
    IsPermModuleMod (n := 6) (fun _ => True) ({0, fun _ => 1} : Set (Fin 6 → ZMod 2)) φ A ⊥ H Alt

@[expose] def Hyp111 (t : G) (S L : Subgroup G) : Prop :=
  Nonempty (↥(secMstar t S L) ≃* ↥(alternatingGroup (Fin 6))) ∨
    Nonempty (↥(secMstar t S L) ≃* Equiv.Perm (Fin 6))

end CFSG.OddStandard.SmallF3.Omega
