module

public import CFSG.Quasithin.Background.D2Fitting
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Open.SQTKSimpleListTauCeti

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

namespace Bridge

@[expose] def IsSQTKQuotient (KP : ∀ (Y : Type) [Group Y], Prop) (G : Type) [Group G] : Prop :=
  ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ : Y →* G), Function.Surjective φ ∧
    CFSG.Open.SQTKTauCeti.StronglyQuasithin Y ∧ KP Y

@[expose] def B113Concl {V : Type} [CommGroup V] (G K : Subgroup (MulAut V)) : Prop :=
  (Nat.card ↥K = 3 ∧ K ≤ fittingOf G ⊓ Subgroup.centralizer (fittingOf G : Set (MulAut V))) ∨
  IsComponentOf K G ∨
  ∃ L : Subgroup (MulAut V), IsComponentOf L G ∧ K ≤ L ∧ ∃ m : ℕ,
    Nonempty (↥L ≃* alternatingGroup (Fin m)) ∧
    ((∃ n : ℕ, n ≤ m ∧ Nonempty (↥K ≃* alternatingGroup (Fin n))) ∨
      (Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧ m = 7))

@[expose] def AsB113With (KP : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G T K : Subgroup (MulAut V)) (Pst : Set (Subgroup (MulAut V))),
      IsSQTKQuotient KP ↥G → pCoreOf 2 G = ⊥ → IsSylowTwoOf T G → IsStableFF G Pst → K ≤ G →
      (CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) → IsSubnormal K (K ⊔ T) →
      ⁅K, ffJP Pst T⁆ = K → B113Concl G K

end Bridge

@[expose] def AltEvenExcluded : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (L K T : Subgroup Γ) (m n : ℕ), (m = 6 ∨ m = 8) → (n = 3 ∨ n = 5) →
    Nonempty (↥L ≃* alternatingGroup (Fin m)) → K ≤ L →
    Nonempty (↥K ≃* alternatingGroup (Fin n)) → IsSylowTwoOf T L → IsSubnormal K (K ⊔ T) → False

end CFSG.QuasithinUnique
