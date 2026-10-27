module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF2Lift
public import CFSG.ClassicalInvolution.Q3.TL4SepCent

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def Res2FConfigR {G : Type} [Group G] [Finite G] (J L L₀ : Subgroup G) : Prop :=
  T4Min 3 G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L ∧
    omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ ∧
    NoInvO2 (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) ∧
    CFSG.IsComponent L₀ ∧ L₀.Normal ∧ layer G = L₀ ∧
    generalizedFitting G = L₀ ⊔ pCore 2 G ∧ pCore 2 G = Subgroup.center G ∧
    Subgroup.centralizer (L₀ : Set G) = Subgroup.center G ∧
    (∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, ∀ z : G,
      IsUniqueInvolution K z → z ∈ L₀)

@[expose] def ExitModelR (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L L₀ : Subgroup G,
    Res2FConfigR J L L₀ → ∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L,
      ∀ (z : G) (hz : IsUniqueInvolution K z),
        (oddCoreImg (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ ∨
          ∃ (W : Subgroup G) (hKW : K ≤ W), IsSubnormal W ⊤ ∧
            (⨆ x : W, conjSub (x : G) K) = W ∧
              PhilipHall.Frame.Thm4Twin.F2.ExitSec W K hKW z hz) → False

end CFSG.ClassicalInvolution.Q3.TL4
