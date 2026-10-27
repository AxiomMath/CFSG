module

public import CFSG.ClassicalInvolution.Q3.TL4Sep2F
public import CFSG.ClassicalInvolution.Q3.TL4SepMainB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def Thm4Res2F' (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L : Subgroup G,
    T4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L →
    omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ →
    NoInvO2 (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) →
    ∀ L₀ : Subgroup G, CFSG.IsComponent L₀ → L₀.Normal → layer G = L₀ →
      generalizedFitting G = L₀ ⊔ pCore 2 G → pCore 2 G = Subgroup.center G →
      Subgroup.centralizer (L₀ : Set G) = Subgroup.center G →
      (∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, ∀ z : G,
        IsUniqueInvolution K z → z ∈ L₀) → False

theorem thm4Res2F_of_res2F' {r n : ℕ} (h : Thm4Res2F' r n) : Thm4Res2F r n := by
  intro G _ _ hG J L hm hgen hno L₀ hL₀ hmem
  have hyp := hm.hyp
  exact h G hG J L hm hgen hno L₀ hL₀ (hyp.component_normal hgen hno hL₀)
    (hyp.layer_eq_of_inv_mem hgen hno hL₀ hmem)
    (hyp.generalizedFitting_eq_of_inv_mem hgen hno hL₀ hmem) (hyp.pCore_eq_center hgen hno)
    (hyp.centralizer_eq_center_of_inv_mem hgen hno hL₀ hmem) hmem

theorem thm4RBelow_of_res2F' {r n : ℕ} (h3 : r = 3 → Thm4Res2C3 n) (h2f : Thm4Res2F' r n) :
    Thm4RBelow r n :=
  thm4RBelow_of_res2C3 h3 (thm4Res2F_of_res2F' h2f)

end CFSG.ClassicalInvolution.Q3.TL4
