module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinComp

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

namespace Thm4Twin

@[expose] def Thm4TwinRes2C (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L : Subgroup G,
    TwinT4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L →
    omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ →
    TL4.NoInvO2 (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L)

@[expose] def Thm4TwinRes2F (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L : Subgroup G,
    TwinT4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L →
    omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ →
    TL4.NoInvO2 (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) →
    ∀ L₀ : Subgroup G, CFSG.IsComponent L₀ →
      (∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, ∀ z : G,
        IsUniqueInvolution K z → z ∈ L₀) → False

theorem thm4RTwinBelow_of_residuals {r n : ℕ} (hA : Thm4TwinThmA r) (h2c : Thm4TwinRes2C r n)
    (h2f : Thm4TwinRes2F r n) : Thm4RTwinBelow r n :=
  thm4RTwinBelow_of_min fun G _ _ hG J L hm hgen => by
    have hno := h2c G hG J L hm hgen
    obtain ⟨L₀, hL₀, hmem⟩ := hm.inv_mem_component hA hgen hno
    exact h2f G hG J L hm hgen hno L₀ hL₀ hmem

end Thm4Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
