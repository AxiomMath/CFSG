module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3ODefs
public import CFSG.ClassicalInvolution.Q3.TL4Conn26X
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame (CentOmega3)
open CFSG.Blueprint

section Defs

variable {W : Type} [Group W]

@[expose] def NoThreeOver2 (Φ : Set (Subgroup W)) : Prop :=
  ∀ M₁ ∈ Φ, ∀ M₂ ∈ Φ, ∀ M₃ ∈ Φ, M₁ ≠ M₂ → M₁ ≠ M₃ → M₂ ≠ M₃ → ∀ P : Subgroup W,
    IsPGroup 2 ↥P → 2 < Nat.card ↥(M₁ ⊓ P) → 2 < Nat.card ↥(M₂ ⊓ P) → Nat.card ↥(M₃ ⊓ P) ≤ 2

structure TwinSigmaOut3 (Φ : Set (Subgroup W)) (K K' : Subgroup W) (k k' : W)
    (σ : MulAut W) : Prop extends TwinBase3 Φ K K' k k' where
  perm : ∀ M ∈ Φ, M.map σ.toMonoidHom ∈ Φ
  sq : σ * σ = 1
  fixK : ∃ Q : Subgroup W, IsSylow2In Q K ∧ ∀ x ∈ Q, σ x = x
  normK' : K'.map σ.toMonoidHom = K'
  movK' : ∃ x ∈ K', σ x ≠ x

end Defs

@[expose] def Model264Rank3 : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (Φ : Set (Subgroup W)) (K K' : Subgroup W) (k k' : W),
    TwinBase3 Φ K K' k k' → NoThreeOver2 Φ → ∀ (N : Subgroup W) [N.Normal],
      N = Subgroup.zpowers (k * k') → CentOmega3 (W ⧸ N) →
        LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) .PSp 2 3 1 ∨
          LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) .PSL 4 3 1

@[expose] def Model1521Twin3 : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (Φ : Set (Subgroup W)) (K K' : Subgroup W) (k k' : W)
    (σ : MulAut W), TwinSigmaOut3 Φ K K' k k' σ → ∀ (N : Subgroup W) [N.Normal],
      N = Subgroup.zpowers (k * k') →
      (LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) .PSp 2 3 1 ∨
        LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) .PSL 4 3 1) →
        LieModel ((W ⧸ N) ⧸ Subgroup.center (W ⧸ N)) .PSL 4 3 1 ∧
          LieModel ↥((sigmaFixGen K σ).map ((QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp
            (QuotientGroup.mk' N))) .PSL 3 3 1 ∧
          ¬ ∃ w : W, ∀ x : W, σ x = w * x * w⁻¹

section Cit3


@[expose] def TightC263E4 (n : ℕ) : Prop :=
  TightBelowRPlus 3 n → ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd)
    (z : Y) (J : Subgroup Y) (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y),
    TightStd8R 3 n Rd Sd z J S R T W t →
      tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤ →
        MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W →
          LieModel (XQuot (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) .PSL 3 3 1 ∨
            NativeSporadic.IsSporadic
              (XQuot (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) .M11 ∨
            (IsSimpleGroup ↥(genFittingFStar
                (XQuot (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))) ∧
              (genFittingFStar
                (XQuot (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))).index ≤ 2 ∧
              ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧
                LieModel (FStarQuot
                  (XQuot (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))) .PSL 2 p f)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
