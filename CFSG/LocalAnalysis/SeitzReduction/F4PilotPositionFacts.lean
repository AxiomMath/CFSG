module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def root0122 : Fin (Tag.rank .F4) → ℤ := ![0, 1, 2, 2]

@[expose] def root0121 : Fin (Tag.rank .F4) → ℤ := ![0, 1, 2, 1]

@[expose] def root0110 : Fin (Tag.rank .F4) → ℤ := ![0, 1, 1, 0]

inductive TwoCentral
  | t
  | u
  | tu
  deriving DecidableEq

namespace TwoCentral

@[expose] def support : TwoCentral → List (Fin (Tag.rank .F4) → ℤ)
  | t => [root0122]
  | u => [root0121]
  | tu => [root0122, root0121]

end TwoCentral

@[expose] def phi0 (κ : TwoCentral) : Set (Fin (Tag.rank .F4) → ℤ) :=
  {γ | IsRoot .F4 γ ∧ ∀ δ ∈ κ.support, iform γ δ = 0}

section Vocabulary


variable (K : Type) [Field K]

@[expose] noncomputable def xC (γ : Fin (Tag.rank .F4) → ℤ) (c : K) : adjointGroup .F4 K :=
  ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩

@[expose] noncomputable def yRep : TwoCentral → adjointGroup .F4 K
  | .t => xC K root0122 1
  | .u => xC K root0121 1
  | .tu => xC K root0122 1 * xC K root0121 1

@[expose] noncomputable def yV : adjointGroup .F4 K :=
  xC K root0110 1 * xC K root0122 1

@[expose] noncomputable def levi (κ : TwoCentral) : Subgroup (adjointGroup .F4 K) :=
  (rootSpan .F4 K (phi0 κ)).subgroupOf (adjointGroup .F4 K)

@[expose] noncomputable def rootSL2 (γ : Fin (Tag.rank .F4) → ℤ) : Subgroup (adjointGroup .F4 K) :=
  (rootSubgroup .F4 K γ ⊔ rootSubgroup .F4 K (-γ)).subgroupOf (adjointGroup .F4 K)

@[expose] def leviRootSL2s (κ : TwoCentral) : Set (Subgroup (adjointGroup .F4 K)) :=
  {J | ∃ γ ∈ phi0 κ, ∃ m ∈ levi K κ, J = (rootSL2 K γ).map (MulAut.conj m).toMonoidHom}

@[expose] def FactF1 : Prop :=
  ∀ y : adjointGroup .F4 K, orderOf y = 2 → ∃ c : adjointGroup .F4 K,
    c * y * c⁻¹ = yRep K .t ∨ c * y * c⁻¹ = yRep K .u ∨ c * y * c⁻¹ = yRep K .tu ∨
      c * y * c⁻¹ = yV K

@[expose] def FactF2 : Prop :=
  ∀ (U : Sylow 2 (adjointGroup .F4 K)) (z : adjointGroup .F4 K),
    z ∈ centralizer ((U : Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) → z ≠ 1 →
      ∃ (κ : TwoCentral) (c : adjointGroup .F4 K), c * z * c⁻¹ = yRep K κ

@[expose] def FactF3 : Prop :=
  ∀ κ : TwoCentral, ∃ Q : Subgroup (adjointGroup .F4 K), IsPGroup 2 Q ∧
    Q ⊔ levi K κ = centralizer ({yRep K κ} : Set (adjointGroup .F4 K)) ∧
    Q ⊓ levi K κ = ⊥ ∧ levi K κ ≤ normalizer (Q : Set (adjointGroup .F4 K))

@[expose] def FactF3Perfect : Prop :=
  ∀ κ : TwoCentral, ⁅centralizer ({yRep K κ} : Set (adjointGroup .F4 K)),
    centralizer ({yRep K κ} : Set (adjointGroup .F4 K))⁆ =
      centralizer ({yRep K κ} : Set (adjointGroup .F4 K))

@[expose] def FactLeviSimple : Prop :=
  ∀ κ : TwoCentral, IsSimpleGroup (levi K κ)

@[expose] def FactF4b : Prop :=
  ∃ P : Subgroup (adjointGroup .F4 K), ⁅P, P⁆ = P ∧ yV K ∈ P ∧
    P ≤ centralizer ({yV K} : Set (adjointGroup .F4 K))

@[expose] def FactF5 : Prop :=
  ∀ (κ κ' : TwoCentral) (ι : levi K κ ≃* levi K κ') (J : Subgroup (adjointGroup .F4 K)),
    J ∈ leviRootSL2s K κ →
      ((J.subgroupOf (levi K κ)).map ι.toMonoidHom).map (levi K κ').subtype ∈ leviRootSL2s K κ'

@[expose] def FactF6 : Prop :=
  ∀ γ : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 γ →
    Nonempty (centralizer (rootSL2 K γ : Set (adjointGroup .F4 K)) ≃* C3Levi K)

@[expose] def FactF7 : Prop :=
  ∃ φ : MulAut (adjointGroup .F4 K),
    (∀ β : MulAut (adjointGroup .F4 K), ∃ (c : adjointGroup .F4 K) (k : ℕ),
      β = MulAut.conj c * φ ^ k) ∧
    ∀ n : ℕ, φ ^ n ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range →
      φ ^ n = 1

end Vocabulary

end CFSG.SeitzReduction.F4Pilot
