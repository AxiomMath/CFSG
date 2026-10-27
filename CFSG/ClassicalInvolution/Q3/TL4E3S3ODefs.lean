module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwinDefs
public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.Blueprint

noncomputable abbrev sigmaFixGen {W : Type} [Group W] (K : Subgroup W) (σ : MulAut W) :
    Subgroup W :=
  ⨆ M ∈ {M : Subgroup W | M ∈ CoreAssembly.conjClass K ∧ ∀ x ∈ M, σ x = x}, M

structure TwinBase3 {W : Type} [Group W] (Φ : Set (Subgroup W)) (K K' : Subgroup W) (k k' : W) :
    Prop where
  fam : TypeRFam 3 Φ
  odd : classicalInvolutionOddCore W = ⊥
  memK : K ∈ Φ
  memK' : K' ∈ CoreAssembly.conjClass K
  invK : IsUniqueInvolution K k
  invK' : IsUniqueInvolution K' k'
  ne : k ≠ k'
  center : k * k' ∈ Subgroup.center W
  gen : (⨆ g : W, conjSub g K) = ⊤
  notO2 : ¬ ∃ P : Subgroup W, P.Normal ∧ IsPGroup 2 ↥P ∧ k ∈ P

structure TwinSigma3 {W : Type} [Group W] (Φ : Set (Subgroup W)) (K K' : Subgroup W) (k k' : W)
    (σ : MulAut W) : Prop extends TwinBase3 Φ K K' k k' where
  perm : ∀ M ∈ Φ, M.map σ.toMonoidHom ∈ Φ
  sq : σ * σ = 1
  fixK : ∀ x ∈ K, σ x = x
  onK' : ∃ Q : Subgroup W, IsSylow2In Q K' ∧ ∃ w ∈ Q, orderOf w = 4 ∧ ∀ x ∈ Q, σ x = w * x * w⁻¹
  noNbr : ∀ M ∈ CoreAssembly.conjClass K, (∀ x ∈ M, σ x = x) → M ∉ omegaNbr Φ K

@[expose] def Model1524Twin3Om : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (Φ : Set (Subgroup W)) (K K' : Subgroup W) (k k' : W)
    (σ : MulAut W), TwinSigma3 Φ K K' k k' σ →
      (∃ (N : Subgroup W) (_ : N.Normal), N = Subgroup.zpowers (k * k') ∧ CentOmega3 (W ⧸ N)) →
        LieModel ↥(sigmaFixGen K σ) .PSU 3 3 1 ∨ LieModel ↥(sigmaFixGen K σ) .PSL 3 3 1

@[expose] def Model1524Twin3E4 : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (Φ : Set (Subgroup W)) (K K' : Subgroup W) (k k' : W)
    (σ : MulAut W), TwinSigma3 Φ K K' k k' σ → TwinE4 W →
      LieModel ↥(sigmaFixGen K σ) .PSU 3 3 1 ∨ LieModel ↥(sigmaFixGen K σ) .PSL 3 3 1

end CFSG.ClassicalInvolution.Q3.TL4
