module

public import CFSG.ClassicalInvolution.Q3.TL4VtxOrb
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint
open scoped commutatorElement

section Outcomes

variable {G : Type} [Group G] [Finite G]

@[expose] def C264One (Ω : Set (Subgroup G)) (z t : G) : Prop :=
  Subgroup.centralizer ({z * t} : Set G) ≤
    Subgroup.normalizer ((Subgroup.closure ({z * t, z} : Set G) ⊔
      oddCoreOf (layerY Ω (z * t)) : Subgroup G) : Set G)

@[expose] noncomputable def secCyc (Ω : Set (Subgroup G)) (x w : G) : Subgroup (SecQuot Ω x) :=
  ((Subgroup.zpowers w).subgroupOf (layerY Ω x)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)))

@[expose] def C264Two (Ω : Set (Subgroup G)) (K : Subgroup G) (z t : G) : Prop :=
  (∃ (N : Subgroup (SecQuot Ω (z * t))) (_ : N.Normal), N = secCyc Ω (z * t) (z * t) ∧
      LieModel ((SecQuot Ω (z * t) ⧸ N) ⧸ Subgroup.center (SecQuot Ω (z * t) ⧸ N)) .PSL 4 3 1) ∧
    ∃ h : G, (∃ x ∈ omegaNbrGen Ω K, x * t * x⁻¹ = h * z * h⁻¹) ∧
      (∀ y ∈ conjSub h (omegaNbrGen Ω K), ⁅z * t, y⁆ ∈ oddCoreOf (conjSub h (omegaNbrGen Ω K))) ∧
      (LieModel (↥(conjSub h (omegaNbrGen Ω K)) ⧸
          classicalInvolutionOddCore ↥(conjSub h (omegaNbrGen Ω K))) .PSL 3 3 1 ∨
        LieModel (↥(conjSub h (omegaNbrGen Ω K)) ⧸
          classicalInvolutionOddCore ↥(conjSub h (omegaNbrGen Ω K))) .PSU 3 3 1)

@[expose] def SecConj264 (Ω : Set (Subgroup G)) (K J : Subgroup G) (x : G) : Prop :=
  ∃ g : SecQuot Ω x, conjSub g (secImg Ω x K) = secImg Ω x J

noncomputable abbrev secOrb (Ω : Set (Subgroup G)) (K : Subgroup G) (x : G) :
    Subgroup (SecQuot Ω x) :=
  Vtx.orbGrp (secFam Ω x) (secImg Ω x K)

@[expose] def SecInO2 (Ω : Set (Subgroup G)) (K : Subgroup G) (x z : G) : Prop :=
  ∃ P : Subgroup ↥(secOrb Ω K x), P.Normal ∧ IsPGroup 2 ↥P ∧
    ∀ c : ↥(secOrb Ω K x), (c : SecQuot Ω x) ∈ secCyc Ω x z → c ∈ P

@[expose] def SecTwinOmega (Ω : Set (Subgroup G)) (K : Subgroup G) (x : G) : Prop :=
  ∃ (N : Subgroup ↥(secOrb Ω K x)) (_ : N.Normal), IsPGroup 2 ↥N ∧
    N ≤ Subgroup.center ↥(secOrb Ω K x) ∧
    (∀ c : ↥(secOrb Ω K x), c ∈ N ↔ (c : SecQuot Ω x) ∈ secCyc Ω x x) ∧
    PhilipHall.Frame.CentOmega3 (↥(secOrb Ω K x) ⧸ N)

end Outcomes

section Cit3

@[expose] def TightC26_4RG (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y)
    (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y), TightStd8R 3 n Rd Sd z J S R T W t →
      tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤ →
        MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W →
          C264One (CoreAssembly.conjClass (tightCore Rd)) z t ∨
            C264Two (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z t

@[expose] def TightC264Pair (n : ℕ) : Prop :=
  TightBelowRPlus 3 n → ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd)
    (z : Y) (J : Subgroup Y) (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y),
    TightStd8R 3 n Rd Sd z J S R T W t →
      tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤ →
        MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W →
          (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd)).Normal →
            (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J).Normal →
              ∀ M ∈ secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t), M.Normal →
                M = secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ∨
                  M = secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J

@[expose] def TightC264E2 (n : ℕ) : Prop :=
  TightBelowRPlus 3 n → ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd)
    (z : Y) (J : Subgroup Y) (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y),
    TightStd8R 3 n Rd Sd z J S R T W t →
      tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤ →
        MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W →
          SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t) →
            SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z →
              C264One (CoreAssembly.conjClass (tightCore Rd)) z t ∨
                C264Two (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z t

@[expose] def TightC264NoTwinE4 (n : ℕ) : Prop :=
  TightBelowRPlus 3 n → ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd)
    (z : Y) (J : Subgroup Y) (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y),
    TightStd8R 3 n Rd Sd z J S R T W t →
      tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤ →
        MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W →
          SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t) →
            ¬ SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z →
              ¬ PhilipHall.Frame.TwinE4
                ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))

@[expose] def TightC264Omega (n : ℕ) : Prop :=
  TightBelowRPlus 3 n → ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd)
    (z : Y) (J : Subgroup Y) (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y),
    TightStd8R 3 n Rd Sd z J S R T W t →
      tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤ →
        MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W →
          SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t) →
            ¬ SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z →
              SecTwinOmega (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) →
                C264Two (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z t

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
