module

public import CFSG.ClassicalInvolution.Q3.TL4Res2FDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def F2CoreConfig {G : Type} [Group G] [Finite G] (J L L₀ : Subgroup G) : Prop :=
  PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G
      (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) ∧
    (¬ ∃ g : G, conjSub g J = L) ∧ ¬ Commutes J L ∧
    omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ ∧
    NoInvO2 (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) ∧
    CFSG.IsComponent L₀ ∧ L₀.Normal ∧ layer G = L₀ ∧
    generalizedFitting G = L₀ ⊔ pCore 2 G ∧ pCore 2 G = Subgroup.center G ∧
    Subgroup.centralizer (L₀ : Set G) = Subgroup.center G ∧
    (∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, ∀ z : G,
      IsUniqueInvolution K z → z ∈ L₀)

theorem F2CoreConfig.of_res2FConfigR {G : Type} [Group G] [Finite G] {J L L₀ : Subgroup G}
    (h : Res2FConfigR J L L₀) : F2CoreConfig J L L₀ := by
  obtain ⟨hm, hgen, hno, hL₀, hn, hlay, hfit, hZ, hC, hmem⟩ := h
  exact ⟨hm.hyp.toTwin, hm.notConj, hm.notComm, hgen, hno, hL₀, hn, hlay, hfit, hZ, hC, hmem⟩

@[expose] def ExitModelCore (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L L₀ : Subgroup G,
    F2CoreConfig J L L₀ → ∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L,
      ∀ (z : G) (hz : IsUniqueInvolution K z),
        (oddCoreImg (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ ∨
          ∃ (W : Subgroup G) (hKW : K ≤ W), IsSubnormal W ⊤ ∧
            (⨆ x : W, conjSub (x : G) K) = W ∧
              PhilipHall.Frame.Thm4Twin.F2.ExitSec W K hKW z hz) → False

theorem exitModelR_of_core {n : ℕ} (h : ExitModelCore n) : ExitModelR n :=
  fun G _ _ hG J L L₀ hc K hK z hz hout =>
    h G hG J L L₀ (F2CoreConfig.of_res2FConfigR hc) K hK z hz hout

end CFSG.ClassicalInvolution.Q3.TL4
