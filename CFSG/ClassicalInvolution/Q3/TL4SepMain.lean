module

public import CFSG.ClassicalInvolution.Q3.TL4SepCompB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def Thm4Res2C (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L : Subgroup G,
    T4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L →
    omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ →
    NoInvO2 (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L)

@[expose] def Thm4Res2F (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L : Subgroup G,
    T4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L →
    omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ →
    NoInvO2 (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) →
    ∀ L₀ : Subgroup G, CFSG.IsComponent L₀ →
      (∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, ∀ z : G,
        IsUniqueInvolution K z → z ∈ L₀) → False

theorem thm4RBelow_of_residuals {r n : ℕ} (h2c : Thm4Res2C r n) (h2f : Thm4Res2F r n) :
    Thm4RBelow r n :=
  thm4RBelow_of_min fun G _ _ hG J L hm hgen => by
    have hno := h2c G hG J L hm hgen
    obtain ⟨L₀, hL₀, hmem⟩ := hm.inv_mem_component hgen hno
    exact h2f G hG J L hm hgen hno L₀ hL₀ hmem

end CFSG.ClassicalInvolution.Q3.TL4
