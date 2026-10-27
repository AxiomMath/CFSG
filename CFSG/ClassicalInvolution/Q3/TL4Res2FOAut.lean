module

public import CFSG.ClassicalInvolution.Q3.TL4OddBasic

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isComponent_of_layer_eq {L₀ L : Subgroup G} (hL₀ : CFSG.IsComponent L₀)
    (hlay : layer G = L₀) (hL : CFSG.IsComponent L) : L = L₀ := by
  have hLL₀ : L ≤ L₀ := by
    rw [← hlay]
    exact CFSG.LocalCores.component_le_layer hL
  rcases CFSG.LocalCores.component_subnormal_subgroup hL₀ hL.2 with h | h
  · exact le_antisymm hLL₀ h
  · exfalso
    obtain ⟨a, b, hab⟩ := hL.1.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hc : ⁅(x : G), (y : G)⁆ ∈ ⁅L₀, L⁆ :=
      Subgroup.commutator_mem_commutator (hLL₀ x.2) y.2
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    have hxy : x * y = y * x := Subtype.ext hc
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]

theorem oddCoreImg_eq_bot_of_autOddFreeInner (hO : classicalInvolutionOddCore G = ⊥)
    {L₀ : Subgroup G} (hL₀ : CFSG.IsComponent L₀) (hlay : layer G = L₀) {z : G} (hzL : z ∈ L₀)
    (hz2 : orderOf z = 2) (hA : Q3NM.AutOddFreeInner ↥L₀) :
    oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
  have hO' : CFSG.pPrimeCore 2 G = ⊥ := by
    rw [← hO]
    unfold CFSG.pPrimeCore classicalInvolutionOddCore
    congr 1
    ext N
    simp [Nat.coprime_two_left]
  have ht2 : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have ht1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    omega
  refine oddCent_eq_bot_of_components hO' ht2 ht1 fun L hL _ _ => ?_
  obtain rfl := eq_of_isComponent_of_layer_eq hL₀ hlay hL
  refine hA.toOn.mono fun σ hσ => ⟨⟨z, hzL⟩, MulEquiv.ext fun y => Subtype.ext ?_⟩
  rw [hσ y, MulAut.conj_apply]
  rfl

end CFSG.ClassicalInvolution.Q3.TL4
