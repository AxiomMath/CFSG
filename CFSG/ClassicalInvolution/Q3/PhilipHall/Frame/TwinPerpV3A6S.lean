module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22YN
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6aMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6iTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf93Steps
public import CFSG.YGroups.Y443.Native.Hom
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Census.SiftSound
public import CFSG.ClassicalInvolution.Asc77.AscC22P14
public import CFSG.ClassicalInvolution.Asc77.AscC22P16
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4CheckD
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}

local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

@[expose] def NoExitAll (n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) :
    Prop :=
  ∀ (L L' L'' : Subgroup Y) (a a' a'' : Y),
    V3Std n Y R S t L L' L'' a a' a'' →
    ∀ W' ∈ WSet Ω[R], L ∈ DSet Ω[R] W' → L' ∈ DSet Ω[R] W' → L'' ∈ DSet Ω[R] W' → a ∈ W' → a' ∈ W' →
      ¬ SecNoExitAt Ω[R] (a * a')

structure AE6Hyp (n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) : Prop where
  no : NoExitAll n R S t
  ex : V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄
  hW : W ∈ WSet Ω[R]
  hK : K ∈ DSet Ω[R] W
  hK' : K' ∈ DSet Ω[R] W
  hK₃ : K₃ ∈ DSet Ω[R] W
  hu₁ : u₁ ∈ W
  hu₂ : u₂ ∈ W
  ae6 : Nonempty (AEIdent (TwinDisc.secFam Ω[R] (u₁ * u₂)) 6)
  oddC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥

structure AE6Frame {Y : Type} [Group Y] (K K' K₃ K₄ W : Subgroup Y) (t u₁ u₂ a₁ a₂ a₃ a₄ y : Y) : Prop where
  h₁ : a₁ ∈ K ⊓ W
  h₂ : a₂ ∈ K' ⊓ W
  h₃ : a₃ ∈ K₃ ⊓ W
  h₄ : a₄ ∈ K₄ ⊓ W
  o₁ : orderOf a₁ = 4
  o₂ : orderOf a₂ = 4
  o₃ : orderOf a₃ = 4
  o₄ : orderOf a₄ = 4
  hu : a₁ * a₂ = u₁ * u₂
  hy : y * t * y⁻¹ = a₁ * a₂ * a₃ * a₄
  hc : y ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y)

@[expose] def ae6E {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (u : Y) : Subgroup Y :=
  pCoreOf 2 (rLayer Ω u)

@[expose] def ae6D {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (W : Subgroup Y) (u : Y) : Subgroup Y :=
  ⨆ m : MGrp Ω W, conjSub (m : Y) (ae6E Ω u)

@[expose] def ae6I {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (W : Subgroup Y) (u : Y) : Subgroup Y :=
  MGrp Ω W ⊔ rLayer Ω u

@[expose] def ae6ConjIn {Y : Type} [Group Y] (X K : Subgroup Y) : Set (Subgroup Y) :=
  {J | ∃ g ∈ X, conjSub g K = J}

@[expose] def ae6Vc {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (c : Y) : Set (Subgroup Y) :=
  {J | J ∈ Ω ∧ IsUniqueInvolution J c}

@[expose] def ae6P {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (c : Y) : Subgroup Y :=
  ⨆ J ∈ ae6Vc Ω c, J

@[expose] def ae6L {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (t τ x : Y) : Subgroup Y :=
  ⨆ J ∈ ae6Vc Ω t ∪ ae6Vc Ω τ ∪ ae6Vc Ω x, J

@[expose] def AE6Hx {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (W : Subgroup Y) (u t τ h : Y) : Prop :=
  h ∈ Subgroup.centralizer ({t} : Set Y) ∧ h * τ * h⁻¹ ∉ ae6D Ω W u ∧
    ⁅ae6D Ω W u, Subgroup.zpowers (h * τ * h⁻¹)⁆ = Subgroup.closure ({t, τ} : Set Y)

@[expose] def AE6IConc {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (K W : Subgroup Y) (u : Y) : Prop :=
  ae6I Ω W u < ⊤ ∧
    ∃ A : AEIdent (ae6ConjIn (ae6I Ω W u) K) 8,
      pSpan (ae6ConjIn (ae6I Ω W u) K) = ae6I Ω W u ∧ A.φ.ker = ⊥ ∧ pCoreOf 2 (ae6I Ω W u) = ae6D Ω W u

@[expose] def AE6I23D {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (K W : Subgroup Y) (u t τ x : Y)
    (L₂ L₃ A₂ A₃ : Subgroup Y) : Prop :=
  MGrp Ω W ≤ L₂ ∧ MGrp Ω W ≤ L₃ ∧ L₂ ≤ ae6I Ω W u ∧ L₃ ≤ ae6I Ω W u ∧ L₂ ≠ L₃ ∧
    x ∈ A₂ ∧ x ∈ A₃ ∧ IsElemAbelian2 A₂ 6 ∧ IsElemAbelian2 A₃ 6 ∧
    A₂ ≤ pCoreOf 2 L₃ ∧ A₃ ≤ pCoreOf 2 L₂ ∧
    ae6L Ω t τ x ≤ Subgroup.normalizer (A₂ : Set Y) ∧ ae6L Ω t τ x ≤ Subgroup.normalizer (A₃ : Set Y) ∧
    L₃ ≤ Subgroup.normalizer (A₂ : Set Y) ∧ L₂ ≤ Subgroup.normalizer (A₃ : Set Y) ∧
    (∃ B : AEIdent (ae6ConjIn (ae6L Ω t τ x ⊔ L₃) K) 8,
      pSpan (ae6ConjIn (ae6L Ω t τ x ⊔ L₃) K) = ae6L Ω t τ x ⊔ L₃ ∧ B.φ.ker = ⊥ ∧
        pCoreOf 2 (ae6L Ω t τ x ⊔ L₃) = A₂) ∧
    (∃ B : AEIdent (ae6ConjIn (ae6L Ω t τ x ⊔ L₂) K) 8,
      pSpan (ae6ConjIn (ae6L Ω t τ x ⊔ L₂) K) = ae6L Ω t τ x ⊔ L₂ ∧ B.φ.ker = ⊥ ∧
        pCoreOf 2 (ae6L Ω t τ x ⊔ L₂) = A₃)

@[expose] def ae6Tri {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (W : Subgroup Y) (u t τ x : Y)
    (L₂ L₃ : Subgroup Y) : Fin 3 → Subgroup Y :=
  ![ae6I Ω W u, ae6L Ω t τ x ⊔ L₃, ae6L Ω t τ x ⊔ L₂]

@[expose] def AE6Shape {Y : Type} [Group Y] (K M L L₂ L₃ : Subgroup Y) (V : Fin 3 → Subgroup Y) : Prop :=
  M ≤ L ∧ V 0 ⊓ V 1 = L₃ ∧ V 0 ⊓ V 2 = L₂ ∧ V 1 ⊓ V 2 = L ∧ L₂ ⊓ L₃ = M ∧ Nat.card M = 12288 ∧
    (∀ k l, k ≠ l → pCoreOf 2 (V k) ≤ V k ⊓ V l ∧ Nat.card ↥(V k ⊓ V l) = 86016) ∧
    ∀ k l, k ≠ l → {J | J ∈ ae6ConjIn (V k) K ∧ J ≤ V k ⊓ V l} = ae6ConjIn (V k ⊓ V l) K

@[expose] def ae6Omit : Fin 3 → Fin 8 := ![1, 7, 5]

@[expose] noncomputable def ae6ModelV (k : Fin 3) : Subgroup ↥CFSG.EvenSmallLie.OmegaEight.omegaT :=
  Subgroup.closure (A6.curtisGen '' {i | i ≠ ae6Omit k})

@[expose] def AE6Glue {Y : Type} [Group Y] (V : Fin 3 → Subgroup Y) : Prop :=
  ∃ ψ : ∀ k, ↥(V k) ≃* ↥(ae6ModelV k),
    (∀ k l (g : ↥(V k)), ((g : Y) ∈ V l ↔
      ((ψ k g : ↥CFSG.EvenSmallLie.OmegaEight.omegaT) ∈ ae6ModelV l))) ∧
    ∀ k l (g : ↥(V k)) (hg : (g : Y) ∈ V l),
      (ψ k g : ↥CFSG.EvenSmallLie.OmegaEight.omegaT) = ψ l ⟨g, hg⟩

@[expose] def V3OddCent (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
    V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥

@[expose] def V3AE6Frame (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W →
      ∃ a₁ a₂ a₃ a₄ y : Y, AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y

@[expose] def V3AE6D (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      IsElemAbelian2 (ae6E Ω[R] (u₁ * u₂)) 5 ∧ u₁ * u₂ ∈ ae6E Ω[R] (u₁ * u₂) ∧
        t ∈ ae6E Ω[R] (u₁ * u₂) ∧ y * t * y⁻¹ ∈ ae6E Ω[R] (u₁ * u₂) ∧
        ∀ m ∈ MGrp Ω[R] W, ∀ e ∈ ae6E Ω[R] (u₁ * u₂), ∀ e' ∈ ae6E Ω[R] (u₁ * u₂),
          Commute e (m * e' * m⁻¹)

@[expose] def V3AE6E (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      IsElemAbelian2 (ae6E Ω[R] (u₁ * u₂)) 5 ∧ u₁ * u₂ ∈ ae6E Ω[R] (u₁ * u₂) ∧
        t ∈ ae6E Ω[R] (u₁ * u₂) ∧ y * t * y⁻¹ ∈ ae6E Ω[R] (u₁ * u₂)

@[expose] def V3AE6EComm (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      ∀ m ∈ MGrp Ω[R] W, ∀ e ∈ ae6E Ω[R] (u₁ * u₂), ∀ e' ∈ ae6E Ω[R] (u₁ * u₂),
        Commute e (m * e' * m⁻¹)

@[expose] def V3AE6DNorm (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      (∀ d ∈ ae6D Ω[R] W (u₁ * u₂), d * d = 1) ∧
        rLayer Ω[R] (u₁ * u₂) ≤ Subgroup.normalizer (ae6D Ω[R] W (u₁ * u₂) : Set Y)

@[expose] def V3AE6I (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      AE6IConc Ω[R] K W (u₁ * u₂)

@[expose] def V3AE6H (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      ∃ h ∈ Subgroup.centralizer ({t} : Set Y),
        h * (y * t * y⁻¹) * h⁻¹ ∉ ae6D Ω[R] W (u₁ * u₂) ∧
        h * (y * t * y⁻¹) * h⁻¹ ∈ ae6P Ω[R] t ∧
        ⁅ae6D Ω[R] W (u₁ * u₂), Subgroup.zpowers (h * (y * t * y⁻¹) * h⁻¹)⁆ =
          Subgroup.closure ({t, y * t * y⁻¹} : Set Y)

@[expose] def V3AE6E3 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y h : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h →
        IsElemAbelian2 (Subgroup.closure ({t, y * t * y⁻¹, h * (y * t * y⁻¹) * h⁻¹} : Set Y)) 3 ∧
        Subgroup.closure ({t, y * t * y⁻¹, h * (y * t * y⁻¹) * h⁻¹} : Set Y) ≤ ae6P Ω[R] t ∧
        Subgroup.closure ({t, y * t * y⁻¹, h * (y * t * y⁻¹) * h⁻¹} : Set Y) ≤ ae6P Ω[R] (y * t * y⁻¹) ∧
        Subgroup.closure ({t, y * t * y⁻¹, h * (y * t * y⁻¹) * h⁻¹} : Set Y) ≤
          ae6P Ω[R] (h * (y * t * y⁻¹) * h⁻¹)

@[expose] def V3AE6L (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y h : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h →
        ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) ≤ Subgroup.normalizer
          (Subgroup.closure ({t, y * t * y⁻¹, h * (y * t * y⁻¹) * h⁻¹} : Set Y) : Set Y) ∧
        ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) < ⊤ ∧
        pSpan (ae6ConjIn (ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹)) K) =
          ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) ∧
        ∃ B : AEIdentOn (ae6ConjIn (ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹)) K) 8
            AE.e29Sets AE.e29Sub, B.φ.ker = ⊥

@[expose] def V3AE6I23 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y h : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h →
        ∃ L₂ L₃ A₂ A₃ : Subgroup Y,
          AE6I23D Ω[R] K W (u₁ * u₂) t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) L₂ L₃ A₂ A₃

@[expose] def V3AE6Shape (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y h : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h →
        ∀ L₂ L₃ A₂ A₃ : Subgroup Y,
          AE6I23D Ω[R] K W (u₁ * u₂) t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) L₂ L₃ A₂ A₃ →
            AE6Shape K (MGrp Ω[R] W) (ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹)) L₂ L₃
              (ae6Tri Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) L₂ L₃)

@[expose] def V3AE6Glue (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y h : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h →
        ∀ L₂ L₃ A₂ A₃ : Subgroup Y,
          AE6I23D Ω[R] K W (u₁ * u₂) t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) L₂ L₃ A₂ A₃ →
          AE6Shape K (MGrp Ω[R] W) (ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹)) L₂ L₃
              (ae6Tri Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) L₂ L₃) →
            AE6Glue (ae6Tri Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) L₂ L₃)

@[expose] def V3AE6Curtis (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y h : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h →
        ∃ ε : Fin 8 → Y, (∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn ε) r = 1) ∧
          ae6I Ω[R] W (u₁ * u₂) ≤ Subgroup.closure (Set.range ε) ∧
          ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) ≤ Subgroup.closure (Set.range ε)

@[expose] def V3AE6OmegaH (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y h : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h →
        ∀ ε : Fin 8 → Y, (∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn ε) r = 1) →
          ae6I Ω[R] W (u₁ * u₂) ≤ Subgroup.closure (Set.range ε) →
          ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) ≤ Subgroup.closure (Set.range ε) →
            ∀ J ∈ Ω[R], J ≤ Subgroup.closure (Set.range ε) →
              ∀ J', dstarAdj Ω[R] J J' → J' ≤ Subgroup.closure (Set.range ε)

@[expose] def V3AE6OmegaHB (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y h : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h →
        ∀ ε : Fin 8 → Y, (∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn ε) r = 1) →
          ae6I Ω[R] W (u₁ * u₂) ≤ Subgroup.closure (Set.range ε) →
          ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) ≤ Subgroup.closure (Set.range ε) →
            ∀ J ∈ Ω[R], J ≤ Subgroup.closure (Set.range ε) →
              J ∈ ae6ConjIn (Subgroup.closure (Set.range ε)) K

@[expose] def V3AE6OmegaHA (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y h : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h →
        ∀ ε : Fin 8 → Y, (∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn ε) r = 1) →
          ae6I Ω[R] W (u₁ * u₂) ≤ Subgroup.closure (Set.range ε) →
          ae6L Ω[R] t (y * t * y⁻¹) (h * (y * t * y⁻¹) * h⁻¹) ≤ Subgroup.closure (Set.range ε) →
            ∀ J', dstarAdj Ω[R] K J' → J' ≤ Subgroup.closure (Set.range ε)

@[expose] def AE6SmallQ8 {X : Type} [Group X] (a : X) (J : Subgroup X) : Prop :=
  Nonempty (↥J ≃* QuaternionGroup 2) ∧ IsUniqueInvolution J a ∧
    J ≤ pCoreOf 2 (Subgroup.centralizer ({a} : Set X)) ∧
    Set.ncard {J' | ∃ c ∈ Subgroup.centralizer ({a} : Set X), conjSub c J = J'} ≤ 4

@[expose] def AE6ModelQ8 : Prop :=
  ∀ (a b : ↥CFSG.EvenSmallLie.OmegaEight.omegaT) (J J' : Subgroup ↥CFSG.EvenSmallLie.OmegaEight.omegaT),
    AE6SmallQ8 a J → AE6SmallQ8 b J' → ∃ g, g * a * g⁻¹ = b

abbrev AE6Om : Type := ↥CFSG.EvenSmallLie.OmegaEight.omegaT

@[expose] noncomputable def ae6Word (w : List (Fin 8)) : AE6Om := (w.map A6.curtisGen).prod

@[expose] noncomputable def ae6ModelZ : AE6Om := ae6Word [0, 4, 2, 4, 0, 6, 2, 6, 4, 0, 2, 0, 4, 6, 2, 6]

@[expose] noncomputable def ae6ModelK : Subgroup AE6Om :=
  Subgroup.closure {ae6Word [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6], ae6Word [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6]}

@[expose] def ae6ModelTwins : Set (Subgroup AE6Om) :=
  ae6ConjIn (Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) ae6ModelK

@[expose] noncomputable def ae6ModelP : Subgroup AE6Om := sSup ae6ModelTwins

@[expose] noncomputable def ae6ModelW : Subgroup AE6Om :=
  Subgroup.closure {ae6Word [4, 2, 4, 2, 6, 2, 4, 2, 0], ae6Word [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6],
    ae6Word [0, 2, 4, 2, 6, 2, 0, 2, 4, 2, 6, 2], ae6Word [0, 2, 0, 2, 4, 2, 6, 2, 0, 2, 4, 2, 0, 6],
    ae6Word [0, 4, 2, 4, 2, 6, 2, 0, 2, 4, 2, 6, 2, 4]}

@[expose] noncomputable def ae6ModelE (k l : Fin 3) : Subgroup AE6Om := ae6ModelV k ⊓ ae6ModelV l

@[expose] noncomputable def ae6ModelM : Subgroup AE6Om := ae6ModelV 0 ⊓ ae6ModelV 1 ⊓ ae6ModelV 2

@[expose] def AE6ModelAE8 : Prop :=
  ∀ k : Fin 3, ∃ ρ : ↥((AE.aeSub 8).map (AE.mkQ 8)) ≃* ↥(ae6ModelV k),
    (∀ (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool), ∃ J ∈ ae6ConjIn (ae6ModelV k) ae6ModelK,
      ∀ x : ↥((AE.aeSub 8).map (AE.mkQ 8)), (x : AE.AEQ 8) ∈ AE.memBar α h b ↔
        ((ρ x : ↥(ae6ModelV k)) : AE6Om) ∈ J) ∧
    ∀ J ∈ ae6ConjIn (ae6ModelV k) ae6ModelK, ∃ (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool),
      ∀ x : ↥((AE.aeSub 8).map (AE.mkQ 8)), (x : AE.AEQ 8) ∈ AE.memBar α h b ↔
        ((ρ x : ↥(ae6ModelV k)) : AE6Om) ∈ J

@[expose] def AE6ModelEdgePairs : Prop :=
  ∀ k l m : Fin 3, k ≠ l → k ≠ m → l ≠ m → ∀ E E' : Subgroup AE6Om, E ≤ ae6ModelV k → E' ≤ ae6ModelV k →
    pCoreOf 2 (ae6ModelV k) ≤ E → pCoreOf 2 (ae6ModelV k) ≤ E' → Nat.card E = 86016 → Nat.card E' = 86016 →
    Nat.card ↥(E ⊓ E') = 12288 →
    ∃ β : MulAut ↥(ae6ModelV k),
      ((ae6ModelE k l).subgroupOf (ae6ModelV k)).map β.toMonoidHom = E.subgroupOf (ae6ModelV k) ∧
        ((ae6ModelE k m).subgroupOf (ae6ModelV k)).map β.toMonoidHom = E'.subgroupOf (ae6ModelV k)

@[expose] def AE6EdgeAut (k l : Fin 3) (θ : MulAut ↥(ae6ModelE k l)) : Prop :=
  (∀ g : ↥(ae6ModelE k l), (g : AE6Om) ∈ ae6ModelM ↔ (θ g : AE6Om) ∈ ae6ModelM) ∧
    ∀ J ∈ ae6ConjIn (ae6ModelE k l) ae6ModelK, ∃ J' ∈ ae6ConjIn (ae6ModelE k l) ae6ModelK,
      ∀ g : ↥(ae6ModelE k l), (g : AE6Om) ∈ J ↔ (θ g : AE6Om) ∈ J'

@[expose] def AE6EdgeCompat (β : ∀ k, MulAut ↥(ae6ModelV k)) (k l : Fin 3) (θ : MulAut ↥(ae6ModelE k l)) :
    Prop :=
  ∀ (g : ↥(ae6ModelE k l)) (x : ↥(ae6ModelV k)) (y : ↥(ae6ModelV l)),
    (x : AE6Om) = g → (y : AE6Om) = θ g → (β l y : AE6Om) = β k x

@[expose] def AE6ModelTri : Prop :=
  ∀ (θ₀₁ : MulAut ↥(ae6ModelE 0 1)) (θ₀₂ : MulAut ↥(ae6ModelE 0 2)) (θ₁₂ : MulAut ↥(ae6ModelE 1 2)),
    AE6EdgeAut 0 1 θ₀₁ → AE6EdgeAut 0 2 θ₀₂ → AE6EdgeAut 1 2 θ₁₂ →
    (∀ (g₁ : ↥(ae6ModelE 0 1)) (g₂ : ↥(ae6ModelE 0 2)) (g₃ : ↥(ae6ModelE 1 2)),
      (g₁ : AE6Om) ∈ ae6ModelM → (g₂ : AE6Om) = g₁ → (g₃ : AE6Om) = θ₀₁ g₁ → (θ₀₂ g₂ : AE6Om) = θ₁₂ g₃) →
    ∃ β : ∀ k, MulAut ↥(ae6ModelV k),
      (∀ k l (g : ↥(ae6ModelV k)), ((g : AE6Om) ∈ ae6ModelV l ↔ (β k g : AE6Om) ∈ ae6ModelV l)) ∧
        AE6EdgeCompat β 0 1 θ₀₁ ∧ AE6EdgeCompat β 0 2 θ₀₂ ∧ AE6EdgeCompat β 1 2 θ₁₂

@[expose] def AE6ModelSmall : Prop :=
  AE6SmallQ8 ae6ModelZ ae6ModelK ∧ ∀ J : Subgroup AE6Om, AE6SmallQ8 ae6ModelZ J → J ∈ ae6ModelTwins

@[expose] def AE6Admissible (W₁ : Subgroup AE6Om) : Prop :=
  (∀ x ∈ W₁, ∀ y ∈ W₁, x * y = y * x) ∧ Nat.card W₁ = 64 ∧
    ∀ J ∈ ae6ModelTwins, J ≤ Subgroup.normalizer (W₁ : Set AE6Om) ∧ Nat.card ↥(J ⊓ W₁) = 4

@[expose] def AE6ModelFW : Prop :=
  AE6Admissible ae6ModelW ∧ ∀ W₁ : Subgroup AE6Om, AE6Admissible W₁ →
    ∃ c ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om), conjSub c ae6ModelW = W₁

@[expose] def ae6ConjAut (X : Subgroup AE6Om) : Set (MulAut ↥ae6ModelP) :=
  {α | ∃ c ∈ X, ∀ p : ↥ae6ModelP, (α p : AE6Om) = c * p * c⁻¹}

@[expose] def AE6ModelF : Prop :=
  ∀ X : Subgroup (MulAut ↥ae6ModelP), ae6ConjAut (Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) ⊆ (X : Set _) →
    (∀ x ∈ X, ∀ J ∈ ae6ModelTwins, ∃ J' ∈ ae6ModelTwins,
      ∀ p : ↥ae6ModelP, (p : AE6Om) ∈ J ↔ (x p : AE6Om) ∈ J') →
    (∀ x ∈ X, orderOf x = 3 → (∀ J ∈ ae6ModelTwins, ∀ p : ↥ae6ModelP, (p : AE6Om) ∈ J ↔ (x p : AE6Om) ∈ J) →
      Set.ncard {J | J ∈ ae6ModelTwins ∧ ∃ p : ↥ae6ModelP, (p : AE6Om) ∈ J ∧ x p ≠ p} ≠ 1) →
    ∀ x ∈ X, ∃ β ∈ ae6ConjAut (Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)),
      (fun α => x * α * x⁻¹) '' ae6ConjAut ae6ModelW = (fun α => β * α * β⁻¹) '' ae6ConjAut ae6ModelW

@[expose] def AE6ModelC2 : Prop :=
  ∀ φ : MulAut AE6Om, (∀ p ∈ ae6ModelP, φ p = p) → φ = 1 ∨ φ = MulAut.conj ae6ModelZ

@[expose] def AE6ModelC3 : Prop :=
  ∀ y ∈ ae6ModelW, y ∉ ae6ModelP → ∃ h : AE6Om, y ^ 2 = h⁻¹ * ae6ModelZ * h

@[expose] def ae6PWords : List (List (Fin 8)) :=
  [[2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6], [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6],
    [0, 2, 4, 2, 6, 2, 0, 2, 4, 2, 6, 2], [0, 6, 2, 0, 4, 2, 6, 0, 2, 0, 2, 4, 2],
    [6, 2, 0, 4, 2, 6, 0, 2, 0, 2, 4, 2, 0], [2, 4, 0, 2, 0, 6, 2, 4, 2, 0, 2, 0, 6],
    [2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 0, 6], [0, 2, 0, 2, 4, 2, 0, 6, 2, 4, 0, 2, 6]]

@[expose] def AE6C2Search : Prop :=
  (∀ w ∈ ae6PWords, ae6Word w ∈ ae6ModelP) ∧
    ∀ c : Fin 8 → AE6Om,
      (∀ i, ∀ q ∈ ae6ModelP, A6.curtisGen i * q * (A6.curtisGen i)⁻¹ ∈ ae6ModelP → c i * q = q * c i) →
      (∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn fun i => A6.curtisGen i * c i) r = 1) →
      (∀ w ∈ ae6PWords, (w.map fun i => A6.curtisGen i * c i).prod = ae6Word w) →
      c = 1 ∨ c = fun i => (A6.curtisGen i)⁻¹ * ae6ModelZ * A6.curtisGen i * ae6ModelZ⁻¹

theorem coreAt_eq_self_of_le {Y : Type} [Group Y] [Finite Y] {c : Y} {J : Subgroup Y}
    (hc : J ≤ Subgroup.centralizer ({c} : Set Y)) (h2 : IsPGroup 2 J) : TwinADescent.coreAt c J = J := by
  refine le_antisymm (TwinADescent.coreAt_le_left c J) ?_
  unfold TwinADescent.coreAt
  rw [inf_eq_left.mpr hc]
  exact CFSG.ClassicalInvolution.Q3.le_tightCore_of_isPGroup le_rfl h2

theorem v3OddCent_of_thmE (hE : TwinThmE.TwinThmEP n) (hcit : CIT3Below n)
    (hPb : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) (hSp : ModelFactSp62) (hD4 : ModelFactD42)
    (h4 : Thm4RTwinBelow 3 n) (hB : V3Hyp51B n) (h5 : V3Fourth n) (h7 : V3Alpha13 n) : V3OddCent n :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hStd => oddCent_eq_bot_of_thmE hE hcit hPb hSp hD4 h4 hB h5 h7 hStd

theorem flip_ab {Y : Type} [Group Y] {t a b : Y} (ha : a * a = t) (hb : b * b = t) (htt : t * t = 1) :
    a⁻¹ * b⁻¹ = a * b := by
  have hinv : ∀ x : Y, x * x = t → x⁻¹ = x * t := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hx, htt])
  have htb : t * b = b * t := by rw [← hb, mul_assoc]
  rw [hinv a ha, hinv b hb]
  calc a * t * (b * t) = a * (t * b) * t := by simp only [mul_assoc]
    _ = a * b * (t * t) := by rw [htb]; simp only [mul_assoc]
    _ = a * b := by rw [htt, mul_one]

theorem conj_frame {Y : Type} [Group Y] {j y t a₁ a₂ a₃ a₄ : Y} (hj1 : j * a₁ * j⁻¹ = a₁⁻¹)
    (hj2 : j * a₂ * j⁻¹ = a₂) (hj3 : j * a₃ * j⁻¹ = a₃) (hj4 : j * a₄ * j⁻¹ = a₄)
    (hjt : j * t * j⁻¹ = t) (hy : y * t * y⁻¹ = a₁ * a₂ * a₃ * a₄)
    (hyc : y ∈ Subgroup.centralizer ({a₁ * a₂} : Set Y)) :
    (j * y * j⁻¹) * t * (j * y * j⁻¹)⁻¹ = a₁⁻¹ * a₂ * a₃ * a₄ ∧
      j * y * j⁻¹ ∈ Subgroup.centralizer ({a₁⁻¹ * a₂} : Set Y) := by
  have hjt' : j⁻¹ * t * j = t := by
    calc j⁻¹ * t * j = j⁻¹ * (j * t * j⁻¹) * j := by rw [hjt]
      _ = t := by group
  have hc : a₁⁻¹ * a₂ = j * (a₁ * a₂) * j⁻¹ := by
    calc a₁⁻¹ * a₂ = (j * a₁ * j⁻¹) * (j * a₂ * j⁻¹) := by rw [hj1, hj2]
      _ = j * (a₁ * a₂) * j⁻¹ := by group
  have hyc' : y * (a₁ * a₂) = a₁ * a₂ * y := Subgroup.mem_centralizer_singleton_iff.mp hyc
  refine ⟨?_, ?_⟩
  · calc (j * y * j⁻¹) * t * (j * y * j⁻¹)⁻¹ = j * (y * (j⁻¹ * t * j) * y⁻¹) * j⁻¹ := by group
      _ = j * (a₁ * a₂ * a₃ * a₄) * j⁻¹ := by rw [hjt', hy]
      _ = (j * a₁ * j⁻¹) * (j * a₂ * j⁻¹) * (j * a₃ * j⁻¹) * (j * a₄ * j⁻¹) := by group
      _ = a₁⁻¹ * a₂ * a₃ * a₄ := by rw [hj1, hj2, hj3, hj4]
  · rw [Subgroup.mem_centralizer_singleton_iff, hc]
    calc j * y * j⁻¹ * (j * (a₁ * a₂) * j⁻¹) = j * (y * (a₁ * a₂)) * j⁻¹ := by group
      _ = j * (a₁ * a₂ * y) * j⁻¹ := by rw [hyc']
      _ = j * (a₁ * a₂) * j⁻¹ * (j * y * j⁻¹) := by group

theorem v3AE6Frame : V3AE6Frame n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W H
  have hStd := H.ex.1
  have hF := H.ex.2.1
  have hd := hStd.datum
  have hP' := (CoreData.of_S hStd.perp.core).partIHypG
  have hperp := kPerp_datum hStd.perp hd.mem hd.hz
  have hzW : t ∈ W := hd.sq₁ ▸ W.mul_mem H.hu₁ H.hu₁
  obtain ⟨a₁, a₂, a₃, a₄, y, h1, o1, h2, o2, h3, o3, h4, o4, -, -, -, -, -, -, hy, -,
    ha₁W, ha₂W, ha₃W, ha₄W, hyc, j, hj1, hj2, hj3, hj4⟩ :=
    exists_fuse_cent2W hP' hd hperp hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1 hStd.wyl H.hW hzW
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := H.ex.2.2.2.1
  have hcyc : ∀ {J : Subgroup Y}, J ∈ DSet Ω[R] W → J ∈ Ω[R] → IsCyclic ↥(J ⊓ W) := fun hJD hJ =>
    (Q3CL.Thompson.inf_W_of_mem_D hd.hyp H.hW hJD hJ
      ⟨le_rfl, h2g _ hJ, fun _ hV' _ h => le_antisymm hV' h⟩).2.2.1
  have s₁ := Asc77.eq_or_eq_inv_of_orderOf_four_of_cyclic (hcyc H.hK hd.mem)
    (show u₁ ∈ K ⊓ W from ⟨hd.hu₁.1, H.hu₁⟩) (show a₁ ∈ K ⊓ W from ⟨h1, ha₁W⟩) hd.hu₁.2 o1
  have s₂ := Asc77.eq_or_eq_inv_of_orderOf_four_of_cyclic (hcyc H.hK' hd.hK'.1)
    (show u₂ ∈ K' ⊓ W from ⟨hd.hu₂.1, H.hu₂⟩) (show a₂ ∈ K' ⊓ W from ⟨h2, ha₂W⟩) hd.hu₂.2 o2
  have q2 : a₂ * a₂ = t := Asc77.sq_eq_of_orderOf_four hd.hzK' h2 o2
  have htt : t * t = 1 := hd.hz.sq
  have hjt : j * t * j⁻¹ = t := by
    calc j * t * j⁻¹ = (j * a₂ * j⁻¹) * (j * a₂ * j⁻¹) := by rw [← q2]; group
      _ = t := by rw [hj2, q2]
  obtain ⟨hy', hyc'⟩ := conj_frame hj1 hj2 hj3 hj4 hjt hy hyc
  have hfr : ∀ b₁ y' : Y, b₁ ∈ K ⊓ W → orderOf b₁ = 4 → b₁ * a₂ = u₁ * u₂ →
      y' * t * y'⁻¹ = b₁ * a₂ * a₃ * a₄ → y' ∈ Subgroup.centralizer ({b₁ * a₂} : Set Y) →
      ∃ a₁ a₂ a₃ a₄ y : Y, AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y :=
    fun b₁ y' hb ob hu hy hc => ⟨b₁, a₂, a₃, a₄, y', hb, ⟨h2, ha₂W⟩, ⟨h3, ha₃W⟩, ⟨h4, ha₄W⟩, ob, o2,
      o3, o4, hu, hy, hu ▸ hc⟩
  have hb₁ : a₁⁻¹ ∈ K ⊓ W := ⟨K.inv_mem h1, W.inv_mem ha₁W⟩
  have ob₁ : orderOf a₁⁻¹ = 4 := by rw [orderOf_inv]; exact o1
  rcases s₁ with e1 | e1 <;> rcases s₂ with e2 | e2
  · exact hfr a₁ y ⟨h1, ha₁W⟩ o1 (by rw [e1, e2]) hy hyc
  · exact hfr a₁⁻¹ _ hb₁ ob₁ (by rw [e1, e2]; exact flip_ab hd.sq₁ hd.sq₂ htt) hy' hyc'
  · exact hfr a₁⁻¹ _ hb₁ ob₁ (by rw [e1, e2, inv_inv]) hy' hyc'
  · exact hfr a₁ y ⟨h1, ha₁W⟩ o1 (by rw [e1, e2]; exact flip_ab hd.sq₁ hd.sq₂ htt) hy hyc

theorem v3ExitAE6WfN_of (hEW : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n)
    (h5 : V3Fourth n) (h7 : V3Alpha13 n) (hOpen : V3SecOpenW n) (hOdd : V3OddCent n)
    (hFr : V3AE6Frame n) (hE : V3AE6H n) (hH : V3AE6Curtis n) (hJ : V3AE6OmegaH n) :
    V3ExitAE6WfN n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hNo hin W hW hKD hK'D hK₃D hu₁ hu₂ hI
  have H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W :=
    ⟨hNo, hin, hW, hKD, hK'D, hK₃D, hu₁, hu₂, hI, hOdd Y R S t K K' K₃ u₁ u₂ u₃ hin.1⟩
  obtain ⟨a₁, a₂, a₃, a₄, y, fr⟩ := hFr Y R S t K K' K₃ u₁ u₂ u₃ K₄ W H
  obtain ⟨h, hh, hxD, -, hcomm⟩ := hE Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  have hx : AE6Hx Ω[R] W (u₁ * u₂) t (y * t * y⁻¹) h := ⟨hh, hxD, hcomm⟩
  obtain ⟨ε, hrel, hIε, hLε⟩ := hH Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx
  have hKM : K ≤ MGrp Ω[R] W := by
    unfold MGrp
    exact le_iSup₂_of_le K hKD le_rfl
  have hMI : MGrp Ω[R] W ≤ ae6I Ω[R] W (u₁ * u₂) := by
    unfold ae6I
    exact le_sup_left
  have hK : K ≤ Subgroup.closure (Set.range ε) := le_trans hKM (le_trans hMI hIε)
  have hconn := A6.dstarConn_of_ae6 hEW hcit hP h4 h5 h7 hOpen hNo hin hW hKD hK'D hK₃D hu₁ hu₂ hI
  have key : ∀ J, Relation.ReflTransGen (dstarAdj Ω[R]) K J →
      J ∈ Ω[R] ∧ J ≤ Subgroup.closure (Set.range ε) := by
    intro J hc
    induction hc with
    | refl => exact ⟨hin.1.datum.mem, hK⟩
    | tail _ hbc ih =>
      exact ⟨hbc.1, hJ Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx ε hrel hIε hLε _ ih.1 ih.2 _ hbc⟩
  have htop : Subgroup.closure (Set.range ε) = ⊤ := by
    rw [eq_top_iff, ← (CoreData.of_S hin.1.perp.core).gen]
    exact iSup_le fun g => (key _ (hconn _ ⟨g, rfl⟩)).2
  haveI : Nontrivial Y := ⟨⟨t, 1, hin.1.datum.hz.ne_one⟩⟩
  exact hin.1.exit (A6.curtisD42_twinE4 ε hrel htop)

theorem v3AE6D_of (hE : V3AE6E n) (hC : V3AE6EComm n) : V3AE6D n :=
  fun Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr =>
    ⟨(hE Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr).1,
      (hE Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr).2.1,
      (hE Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr).2.2.1,
      (hE Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr).2.2.2,
      hC Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr⟩

theorem v3AE6OmegaH_of (hA : V3AE6OmegaHA n) (hB : V3AE6OmegaHB n) : V3AE6OmegaH n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx ε hrel hI hL J hJ hJH J' hadj
  obtain ⟨g, hg, rfl⟩ := hB Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx ε hrel hI hL J hJ hJH
  have hadj' := dstarAdj_conj (conjInvariant_conjClass (tightCore R)) hadj g⁻¹
  rw [conjSub_inv_conjSub] at hadj'
  have hle := hA Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx ε hrel hI hL _ hadj'
  calc J' = conjSub g (conjSub g⁻¹ J') := (conjSub_conjSub_inv g J').symm
    _ ≤ conjSub g (Subgroup.closure (Set.range ε)) := conjSub_mono hle
    _ = Subgroup.closure (Set.range ε) := conjSub_eq_self_of_mem hg

theorem curtisRels_omit : ∀ r ∈ A6.curtisRels, ∃ k : Fin 3, ∀ c ∈ r, c / 2 ≠ (ae6Omit k).val := by
  decide

theorem curtisEval_congr {G : Type*} [Group G] {l l' : List G} {w : List ℕ}
    (h : ∀ c ∈ w, l.getD (c / 2) 1 = l'.getD (c / 2) 1) : A6.curtisEval l w = A6.curtisEval l' w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [A6.curtisEval_cons, A6.curtisEval_cons, h c List.mem_cons_self,
      ih fun c hc => h c (List.mem_cons_of_mem _ hc)]

theorem curtisEval_map {G H : Type*} [Group G] [Group H] (f : G →* H) (l : List G) (w : List ℕ) :
    A6.curtisEval (l.map f) w = f (A6.curtisEval l w) := by
  induction w with
  | nil => simp [A6.curtisEval_nil]
  | cons c w ih =>
    have hg : (l.map f).getD (c / 2) 1 = f (l.getD (c / 2) 1) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases l[c / 2]? <;> simp
    rw [A6.curtisEval_cons, A6.curtisEval_cons, ih, hg, map_mul]
    split_ifs <;> simp

theorem ae6ModelC2_of_search (h : AE6C2Search) : AE6ModelC2 := by
  intro φ hφ
  set c : Fin 8 → AE6Om := fun i => (A6.curtisGen i)⁻¹ * φ (A6.curtisGen i) with hc
  have hgc : ∀ i, A6.curtisGen i * c i = φ (A6.curtisGen i) := fun i => by
    simp only [hc, mul_inv_cancel_left]
  have h1 : ∀ i, ∀ q ∈ ae6ModelP, A6.curtisGen i * q * (A6.curtisGen i)⁻¹ ∈ ae6ModelP →
      c i * q = q * c i := by
    intro i q hq hgq
    have e := hφ _ hgq
    rw [map_mul, map_mul, map_inv, hφ q hq] at e
    have e' : φ (A6.curtisGen i) * q = A6.curtisGen i * q * (A6.curtisGen i)⁻¹ * φ (A6.curtisGen i) := by
      rw [← e]; group
    simp only [hc]
    calc (A6.curtisGen i)⁻¹ * φ (A6.curtisGen i) * q
        = (A6.curtisGen i)⁻¹ * (φ (A6.curtisGen i) * q) := by group
      _ = q * ((A6.curtisGen i)⁻¹ * φ (A6.curtisGen i)) := by rw [e']; group
  have hlist : (List.ofFn fun i => A6.curtisGen i * c i) = (List.ofFn A6.curtisGen).map φ.toMonoidHom := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact hgc i
  have h2 : ∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn fun i => A6.curtisGen i * c i) r = 1 := by
    intro r hr
    rw [hlist, curtisEval_map, A6.curtisGen_rels r hr, map_one]
  have h3 : ∀ w ∈ ae6PWords, (w.map fun i => A6.curtisGen i * c i).prod = ae6Word w := by
    intro w hw
    have hw' : (w.map fun i => A6.curtisGen i * c i) = (w.map A6.curtisGen).map φ.toMonoidHom := by
      rw [List.map_map]
      congr 1
      funext i
      exact hgc i
    rw [hw', ← map_list_prod]
    exact hφ _ (h.1 w hw)
  have key : ∀ ψ : MulAut AE6Om, (∀ i, φ (A6.curtisGen i) = ψ (A6.curtisGen i)) → φ = ψ := by
    intro ψ hψ
    have hm : φ.toMonoidHom = ψ.toMonoidHom :=
      MonoidHom.eq_of_eqOn_dense A6.closure_curtisGen (by rintro _ ⟨i, rfl⟩; exact hψ i)
    exact MulEquiv.ext fun x => DFunLike.congr_fun hm x
  rcases h.2 c h1 h2 h3 with hc1 | hcz
  · left
    refine key 1 fun i => ?_
    rw [← hgc i, congrFun hc1 i, Pi.one_apply, mul_one, MulAut.one_apply]
  · right
    refine key _ fun i => ?_
    rw [← hgc i, congrFun hcz i, MulAut.conj_apply]
    group

theorem getD_ofFn8 {G : Type*} [Group G] (t : Fin 8 → G) (c : ℕ) :
    (List.ofFn t).getD (c / 2) 1 = if h : c / 2 < 8 then t ⟨c / 2, h⟩ else 1 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> rfl

theorem curtis_of_glue {Y : Type} [Group Y] {V : Fin 3 → Subgroup Y} (hG : AE6Glue V) :
    ∃ ε : Fin 8 → Y, (∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn ε) r = 1) ∧
      ∀ k, V k ≤ Subgroup.closure (Set.range ε) := by
  obtain ⟨ψ, hmem, heq⟩ := hG
  let pick : Fin 8 → Fin 3 := fun i => if i = 1 then 1 else 0
  have hpick : ∀ i, i ≠ ae6Omit (pick i) := by decide
  have hgen : ∀ k i, i ≠ ae6Omit k → A6.curtisGen i ∈ ae6ModelV k :=
    fun k i hi => Subgroup.subset_closure ⟨i, hi, rfl⟩
  let ε : Fin 8 → Y := fun i =>
    (((ψ (pick i)).symm ⟨A6.curtisGen i, hgen _ i (hpick i)⟩ : ↥(V (pick i))) : Y)
  have hε : ∀ k i (hi : i ≠ ae6Omit k),
      ∃ hk : ε i ∈ V k, ψ k ⟨ε i, hk⟩ = ⟨A6.curtisGen i, hgen k i hi⟩ := by
    intro k i hi
    have hψx : ψ (pick i) ((ψ (pick i)).symm ⟨A6.curtisGen i, hgen _ i (hpick i)⟩) =
        ⟨A6.curtisGen i, hgen _ i (hpick i)⟩ := MulEquiv.apply_symm_apply _ _
    have hk : ε i ∈ V k := (hmem _ k _).2 (by rw [hψx]; exact hgen k i hi)
    refine ⟨hk, Subtype.ext ?_⟩
    rw [← heq _ k _ hk, hψx]
  have hf : ∀ k i (hi : i ≠ ae6Omit k),
      (((ψ k).symm ⟨A6.curtisGen i, hgen k i hi⟩ : ↥(V k)) : Y) = ε i := by
    intro k i hi
    obtain ⟨hk, he⟩ := hε k i hi
    rw [← he, MulEquiv.symm_apply_apply]
  refine ⟨ε, fun r hr => ?_, fun k => ?_⟩
  · obtain ⟨k, hk⟩ := curtisRels_omit r hr
    let f : ↥(ae6ModelV k) →* Y := (V k).subtype.comp (ψ k).symm.toMonoidHom
    let g : Fin 8 → ↥(ae6ModelV k) := fun i =>
      if hi : i ≠ ae6Omit k then ⟨A6.curtisGen i, hgen k i hi⟩ else 1
    have hi8 : ∀ c ∈ r, ∀ h8 : c / 2 < 8, (⟨c / 2, h8⟩ : Fin 8) ≠ ae6Omit k := by
      intro c hc h8 h
      apply hk c hc
      rw [← h]
    have h1 : A6.curtisEval (List.ofFn ε) r = A6.curtisEval ((List.ofFn g).map f) r := by
      rw [List.map_ofFn]
      refine curtisEval_congr fun c hc => ?_
      rw [getD_ofFn8, getD_ofFn8]
      split_ifs with h8
      · have hi := hi8 c hc h8
        simp only [Function.comp, g, dif_pos hi, f, MonoidHom.comp_apply, Subgroup.coe_subtype,
          MulEquiv.coe_toMonoidHom]
        exact (hf k _ hi).symm
      · rfl
    have h2 : A6.curtisEval (List.ofFn g) r = 1 := by
      apply Subtype.val_injective
      change (ae6ModelV k).subtype (A6.curtisEval (List.ofFn g) r) = (ae6ModelV k).subtype 1
      rw [map_one, ← curtisEval_map, List.map_ofFn, ← A6.curtisGen_rels r hr]
      refine curtisEval_congr fun c hc => ?_
      rw [getD_ofFn8, getD_ofFn8]
      split_ifs with h8
      · simp only [Function.comp, g, dif_pos (hi8 c hc h8), Subgroup.coe_subtype]
      · rfl
    rw [h1, curtisEval_map, h2, map_one]
  · let f : ↥(ae6ModelV k) →* Y := (V k).subtype.comp (ψ k).symm.toMonoidHom
    have hc : Subgroup.closure (((↑) : ↥(ae6ModelV k) → ↥CFSG.EvenSmallLie.OmegaEight.omegaT) ⁻¹'
        (A6.curtisGen '' {i | i ≠ ae6Omit k})) = ⊤ := Subgroup.closure_closure_coe_preimage
    have htop : (Subgroup.closure (Set.range ε)).comap f = ⊤ := by
      rw [eq_top_iff, ← hc, Subgroup.closure_le]
      rintro x ⟨i, hi, hxi⟩
      have hx : x = ⟨A6.curtisGen i, hgen k i hi⟩ := Subtype.ext hxi.symm
      show f x ∈ Subgroup.closure (Set.range ε)
      have : f x = ε i := by
        rw [hx]
        exact hf k i hi
      rw [this]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    intro y hy
    have hm : ψ k ⟨y, hy⟩ ∈ (Subgroup.closure (Set.range ε)).comap f := htop ▸ Subgroup.mem_top _
    simpa [f] using hm

theorem v3AE6Curtis_of (h23 : V3AE6I23 n) (hSh : V3AE6Shape n) (hGl : V3AE6Glue n) : V3AE6Curtis n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx
  obtain ⟨L₂, L₃, A₂, A₃, hD⟩ := h23 Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx
  have hS := hSh Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx L₂ L₃ A₂ A₃ hD
  obtain ⟨ε, hrel, hV⟩ :=
    curtis_of_glue (hGl Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h H fr hx L₂ L₃ A₂ A₃ hD hS)
  exact ⟨ε, hrel, hV 0, le_trans le_sup_left (hV 1)⟩

theorem v3ExitAE6WfN_of_parts (hEW : TwinThmEW.ThmEQ8) (hE : TwinThmE.TwinThmEP n) (hcit : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) (hSp : ModelFactSp62) (hD4 : ModelFactD42)
    (h4 : Thm4RTwinBelow 3 n) (hB : V3Hyp51B n) (h5 : V3Fourth n) (h7 : V3Alpha13 n)
    (hOpen : V3SecOpenW n) (hHx : V3AE6H n) (h23 : V3AE6I23 n) (hSh : V3AE6Shape n)
    (hGl : V3AE6Glue n) (hJA : V3AE6OmegaHA n) (hJB : V3AE6OmegaHB n) : V3ExitAE6WfN n :=
  v3ExitAE6WfN_of hEW hcit hP h4 h5 h7 hOpen (v3OddCent_of_thmE hE hcit hP hSp hD4 h4 hB h5 h7)
    v3AE6Frame hHx (v3AE6Curtis_of h23 hSh hGl) (v3AE6OmegaH_of hJA hJB)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
