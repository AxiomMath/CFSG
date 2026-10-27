module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm7RCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinDisc

structure Setting (n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y) : Prop where
  core : TwinCoreHyp n Y R S t₀
  disc : ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))
  data : Data (CoreAssembly.conjClass (tightCore R)) K K' z u J t W

@[expose] def Disc12 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      dComp (CoreAssembly.conjClass (tightCore R)) K =
          dstarComp (CoreAssembly.conjClass (tightCore R)) K ∨
        MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W

@[expose] def Disc13N (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      Subgroup.centralizer ({t * z} : Set Y) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y)

@[expose] def Disc13Wyl (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
            sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
          MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W

@[expose] def Disc14N (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      Subgroup.centralizer ({u} : Set Y) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y)

@[expose] def Disc14Alt (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        rLayer (CoreAssembly.conjClass (tightCore R)) u ≤
            sigmaGen (CoreAssembly.conjClass (tightCore R)) K ∨
          Subgroup.centralizer ({u} : Set Y) ≤ Subgroup.centralizer ({t * z} : Set Y)

@[expose] def Disc15 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
            sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
          ∀ M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K,
            M ≤ Subgroup.centralizer ({t * z} : Set Y)

@[expose] def DiscYSigma (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        rLayer (CoreAssembly.conjClass (tightCore R)) u ≤
            sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
          Subgroup.centralizer ({t * z} : Set Y) ≤
              sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K →
            Subgroup.centralizer ({u} : Set Y) ≤
              sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K

@[expose] def Disc17tz (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
            sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
          dComp (CoreAssembly.conjClass (tightCore R)) K =
              dstarComp (CoreAssembly.conjClass (tightCore R)) K →
            Subgroup.centralizer ({t * z} : Set Y) ≤
              sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K

@[expose] def DiscCentInStar (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
            sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
          (∀ M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K,
              M ≤ Subgroup.centralizer ({t * z} : Set Y)) →
            MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W →
              ∀ M ∈ CoreAssembly.conjClass (tightCore R),
                M ≤ Subgroup.centralizer ({t * z} : Set Y) →
                  M ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
