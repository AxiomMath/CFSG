module

public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.EmptyFaithful.S14111

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B2F CFSG.Quasithin.E2

@[expose] def SymCoreWith {W : Type*} [CommGroup W] (L : Subgroup (MulAut W)) (N : ℕ)
    (θ : ↥L ≃* Equiv.Perm (Fin N)) (β : ↥(commV L) ≃* Multiplicative (evenWeight N)) : Prop :=
  ∀ (h : ↥L) (u : ↥(commV L)) (hu : (h : MulAut W) (u : W) ∈ commV L) (i : Fin N),
    ((Multiplicative.toAdd (β ⟨(h : MulAut W) u, hu⟩) : evenWeight N) : Fin N → ZMod 2) i =
      ((Multiplicative.toAdd (β u) : evenWeight N) : Fin N → ZMod 2) ((θ h)⁻¹ i)

@[expose] def IsSymCoreModule {W : Type*} [CommGroup W] (L : Subgroup (MulAut W)) (N : ℕ) : Prop :=
  ∃ (θ : ↥L ≃* Equiv.Perm (Fin N)) (β : ↥(commV L) ≃* Multiplicative (evenWeight N)),
    SymCoreWith L N θ β

variable {G : Type} [Group G] [Finite G]

@[expose] def E23FamGen (H T V : Subgroup G) (hV : IsElemAbelian 2 V)
    (I : Finset (Subgroup (MulAut (IntMod V hV)))) : Prop :=
  I.Nonempty ∧
  autI hV (thompsonJ H) = ⨆ L ∈ I, L ∧
  (∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
  (∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ autI hV T, B1.conjAut t L = L') ∧
  (∀ L ∈ I, (∃ n : ℕ, IsL2Natural L (fixV (autI hV (twoResidual H))) n) ∨
    ∃ m : ℕ, 2 ≤ m ∧ IsSymCoreModule L (2 ^ m + 1)) ∧
  ((∀ L ∈ I, ∃ n : ℕ, IsL2Natural L (fixV (autI hV (twoResidual H))) n) →
    autI hV (baum T) = autI hV (thompsonJ T) ∧
    IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H)) ∧
    IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T)) ∧
  (∀ m : ℕ, 2 ≤ m → (∀ L ∈ I, IsSymCoreModule L (2 ^ m + 1)) →
    autI hV (baum T) = autI hV (thompsonJ T) ∧
    autI hV (thompsonJ T) = ⨆ L ∈ I, (L ⊓ autI hV (thompsonJ T)) ∧
    ∀ L ∈ I, ∃ (θ : ↥L ≃* Equiv.Perm (Fin (2 ^ m + 1)))
      (β : ↥(commV L) ≃* Multiplicative (evenWeight (2 ^ m + 1))),
      SymCoreWith L (2 ^ m + 1) θ β ∧
      L ⊓ autI hV (thompsonJ T) =
        Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap})

@[expose] def E23ConclGen (H T V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  twoResidual H ≤ thompsonJ H ∧ ∃ I, E23FamGen H T V hV I

@[expose] def NatCaseGen (H T V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  twoResidual H ≤ thompsonJ H ∧ ∃ I, E23FamGen H T V hV I ∧
    ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual H))) n

@[expose] def SymCaseGen (H T V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  twoResidual H ≤ thompsonJ H ∧ ∃ I, E23FamGen H T V hV I ∧
    ∃ m : ℕ, 2 ≤ m ∧ ∀ L ∈ I, IsSymCoreModule L (2 ^ m + 1)

@[expose] def E23NonsolvGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M : Subgroup G) (hV : IsElemAbelian 2 (VZ T H)),
    MinParabolic H T M → CharTwo H → IsTwoReducedIn H (VZ T H) →
    ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G) → ¬ Group.IsSolvable H →
    ∃ I, E23FamGen H T (VZ T H) hV I

@[expose] def OneBlockGen (H T : Subgroup G) : Prop :=
  ∃ K : Subgroup G, IsChiBlock H K ∧ ⁅K, thompsonJ T⁆ = K ∧ H = T ⊔ conjClosure K T

@[expose] def Concl1Gen (C₁ C₂ H T : Subgroup G) : Prop :=
  C₁ ≤ centerOf H ∨ H ≤ Subgroup.normalizer (C₂ : Set G) ∨ OneBlockGen H T

end CFSG.AGLEmbeddingD2.GN
