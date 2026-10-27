module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch4Sec3L43Steps

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open scoped MatrixGroups

@[expose] def Step4314_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G)
    (m : ℕ) (F : Type) [Field F] [Fintype F] (α : ↥K →* ↥(StatedSL 3 F))
    (β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)) (W' : Submodule F (Fin 3 → F))
    (ZS K₂ R₂ : Subgroup G) (μ : Fˣ) (y : G) (KZ : Subgroup G),
    Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y →
    KZ ∈ cComp (Subgroup.normalizer (ZS : Set G)) →
    Subgroup.normalizer (ZS : Set G) ≤ Subgroup.normalizer (KZ : Set G) → K₂ ≤ KZ →
    KZ ≤ Subgroup.centralizer (ZS : Set G) →
      Subgroup.normalizer (R₂ : Set G) ≤ H ⊓ Subgroup.normalizer (K₂ : Set G) ∧
      R₂ = pCoreOf 2 ((KZ ⊔ T) ⊓ Subgroup.normalizer (R₂ : Set G)) ∧
      pCoreOf 2 (KZ ⊔ T) ≤ R₂ ∧
      R₂ = ((radE0 F).comap α).map K.subtype

end CFSG.Quasithin.H13.Ch4
