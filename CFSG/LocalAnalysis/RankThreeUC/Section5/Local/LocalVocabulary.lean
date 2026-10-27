module

public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.FixedSpace
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ActionVocabulary
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Quotient.QuotientAction
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.Local

open CFSG.LocalAnalysis.RankThreeUC.Section5.Quotient

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness

open scoped commutatorElement

variable {G : Type} [Group G]

abbrev W (P : Subgroup G) : Type := Additive (Pbar P)

variable (p : ℕ) [Fact p.Prime] (P : Subgroup G) [Fact (⁅⁅P, P⁆, P⁆ = ⊥)]
  [Fact (Monoid.exponent ↥P = p)]

@[expose] noncomputable def sigma : Representation (ZMod p) (MulAut ↥P) (W P) where
  toFun g := (linearOfMulAut (p := p) (quotientHom ↥P g)).toLinearMap
  map_one' := by
    ext x
    simp [map_one]
    rfl
  map_mul' g h := by
    ext x
    simp [map_mul]
    rfl

theorem sigma_apply (g : MulAut ↥P) (x : W P) :
    sigma p P g x = Additive.ofMul (quotientHom ↥P g (Additive.toMul x)) := rfl

theorem sigma_apply_mk (g : MulAut ↥P) (x : ↥P) :
    sigma p P g (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk (g x)) := rfl

variable {P} in
@[expose] def Z [Finite G] (P T B : Subgroup G) : Subgroup (MulAut ↥P) :=
  (Subgroup.center ↥(Sstar P T B)).map (Sstar P T B).subtype

@[expose] def K [Finite G] (P T B : Subgroup G) : Subgroup (MulAut ↥P) :=
  Sstar P T B ⊔ Bstar P B

@[expose] def R [Finite G] (P T B A : Subgroup G) : Subgroup (MulAut ↥P) :=
  ⁅Sstar P T B, Bstar P A⁆

variable [Finite G]

@[expose] noncomputable def Q (T B : Subgroup G) (H : Subgroup (MulAut ↥P)) : Submodule (ZMod p) (W P) :=
  BinaryRepresentations.commSpace (sigma p P) (Z P T B) ⊓ BinaryRepresentations.fixedSpace (sigma p P) H

theorem mem_Q (T B : Subgroup G) (H : Subgroup (MulAut ↥P)) (v : W P) :
    v ∈ Q p P T B H ↔
      v ∈ BinaryRepresentations.commSpace (sigma p P) (Z P T B) ∧ v ∈ BinaryRepresentations.fixedSpace (sigma p P) H :=
  Iff.rfl

@[expose] noncomputable def betaRep (T B : Subgroup G) (H : Subgroup (MulAut ↥P))
    (hinv : ∀ k ∈ K P T B, ∀ v ∈ Q p P T B H, sigma p P k v ∈ Q p P T B H) :
    Representation (ZMod p) (K P T B) (Q p P T B H) :=
  Representation.subrepresentation ((sigma p P).comp (K P T B).subtype) (Q p P T B H)
    (fun k v hv => hinv k k.2 v hv)

@[expose] noncomputable def beta (T B : Subgroup G) (H : Subgroup (MulAut ↥P))
    (hinv : ∀ k ∈ K P T B, ∀ v ∈ Q p P T B H, sigma p P k v ∈ Q p P T B H) :
    K P T B →* (Q p P T B H ≃ₗ[ZMod p] Q p P T B H) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Q p P T B H) : _ ≃* _).toMonoidHom.comp
    (Representation.asGroupHom (betaRep p P T B H hinv))

theorem beta_apply_coe (T B : Subgroup G) (H : Subgroup (MulAut ↥P))
    (hinv : ∀ k ∈ K P T B, ∀ v ∈ Q p P T B H, sigma p P k v ∈ Q p P T B H)
    (k : K P T B) (v : Q p P T B H) :
    ((beta p P T B H hinv k v : Q p P T B H) : W P) = sigma p P k v := rfl

@[expose] noncomputable def Ralpha (T B A : Subgroup G) (H : Subgroup (MulAut ↥P))
    (hinv : ∀ k ∈ K P T B, ∀ v ∈ Q p P T B H, sigma p P k v ∈ Q p P T B H) :
    Subgroup (Q p P T B H ≃ₗ[ZMod p] Q p P T B H) :=
  ((R P T B A).subgroupOf (K P T B)).map (beta p P T B H hinv)

@[expose] noncomputable def Aalpha (T B A : Subgroup G) (H : Subgroup (MulAut ↥P))
    (hinv : ∀ k ∈ K P T B, ∀ v ∈ Q p P T B H, sigma p P k v ∈ Q p P T B H) :
    Subgroup (Q p P T B H ≃ₗ[ZMod p] Q p P T B H) :=
  ((Bstar P A).subgroupOf (K P T B)).map (beta p P T B H hinv)

end CFSG.LocalAnalysis.RankThreeUC.Section5.Local
