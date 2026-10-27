module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterSylowInvariant
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterLocalMinus

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem EqualParameterData.card_sylow_of_mod_four_eq_three
    {G : Type} [Group G] [Finite G]
    {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ} {F : Type} [Field F] [Finite F]
    {κ : C t →* Equiv.Perm (Omega F)} {F' : Type} [Field F'] [Finite F']
    {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 3) (T : Sylow p G) :
    Nat.card T = p ^ f :=
  h.card_sylow_of_mod_four_eq_three_of_invariant he (h.exists_invariant_sylow_C he) T

end CFSG.Semidihedral.FixedCoreNontrivial
