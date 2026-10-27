module

import CFSG.ClassicalInvolution.Asc77.AscT3CLate9AEng
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexMain
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateSwap

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

private theorem Std20.late_toG (d : Std20 p f K K' J S R R' W V z t) :
    Std20G K K' J S R R' W V z t :=
  { toStd20F :=
      { d with
        hyp := d.late_hΩ
        late_ne_inv := d.late_ne_inv
        late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.branch.odd d.hyp d.viol.star d.viol.hzJ
        late_card2 := fun hU hK hR =>
          Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp hU hK hR }
    late_hWc := d.late_hWc
    late_t_mem_W := d.late_t_mem_W
    late_z_mem_W := d.late_z_mem_W
    late_hW := d.late_hW
    late_JW := d.late_JW
    late_exists_swap := d.late_exists_swap
    late_swap_data := fun hu huK => d.late_swap_data hu huK }

theorem Std20.late_W_le_N_K (d : Std20 p f K K' J S R R' W V z t) :
    W ≤ Subgroup.normalizer (K : Set G) := by
  exact d.late_toG.late_W_le_N_K

theorem Std20.late_W_le_N_K' (d : Std20 p f K K' J S R R' W V z t) :
    W ≤ Subgroup.normalizer (K' : Set G) := by
  exact d.late_toG.late_W_le_N_K'

theorem Std20.late_V_le_N_RR' (d : Std20 p f K K' J S R R' W V z t) :
    V ≤ Subgroup.normalizer ((R ⊔ R' : Subgroup G) : Set G) := by
  exact d.late_toG.late_V_le_N_RR'

theorem Std20.late_P_inv' (d : Std20 p f K K' J S R R' W V z t)
    (hWeq : W = (W ⊓ K) ⊔ (W ⊓ J)) {x : G} (hxS : x ∈ (S : Subgroup G)) :
    conjSub x (R ⊔ R' ⊔ (J ⊓ W)) = R ⊔ R' ⊔ (J ⊓ W) := by
  exact d.late_toG.late_P_inv' hWeq hxS

theorem Std20.late_98_iff (d : Std20 p f K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) (hWeq : W = (W ⊓ K) ⊔ (W ⊓ J))
    {X : Subgroup G} (hX2 : IsPGroup 2 X) (hXS : X ≤ (S : Subgroup G))
    (hXt : ∀ x ∈ X, x * t = t * x) :
    (∀ x ∈ X, conjSub x K = K) ↔ (∀ x ∈ X, conjSub x J = J) := by
  exact d.late_toG.late_98_iff hJW hWeq hX2 hXS hXt

theorem Std20.late_SX (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z) :
    (S : Subgroup G) ⊓ sec20X (CoreAssembly.conjClass K) z K K' = R ⊔ R' ⊔ V := by
  exact d.late_toG.late_SX c3

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
