module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf2
import CFSG.ClassicalInvolution.Asc77.AscT3CLateCfgEng
public import CFSG.ClassicalInvolution.Q3.Q3T6DConj
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenE612

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Frame.late_hΩ (d : Std20Frame K K' J S R R' W V z t) :
    HypOmegaGen (CoreAssembly.conjClass K) :=
  d.hyp

theorem Std20Frame.late_mem_K (_d : Std20Frame K K' J S R R' W V z t) :
    K ∈ CoreAssembly.conjClass K :=
  CoreAssembly.mem_conjClass_self K

theorem Std20Frame.late_mem_J (d : Std20Frame K K' J S R R' W V z t) :
    J ∈ CoreAssembly.conjClass K :=
  d.viol.mem

theorem Std20Frame.late_mem_K' (d : Std20Frame K K' J S R R' W V z t) :
    K' ∈ CoreAssembly.conjClass K := by
  have h : K' ∈ twinSet (CoreAssembly.conjClass K) K := by rw [d.twins]; exact Or.inr rfl
  exact h.1

theorem Std20Frame.late_hzK' (d : Std20Frame K K' J S R R' W V z t) : IsUniqueInvolution K' z := by
  have h : K' ∈ twinSet (CoreAssembly.conjClass K) K := by rw [d.twins]; exact Or.inr rfl
  obtain ⟨-, z', hz'K, hz'K'⟩ := h
  rw [d.viol.hzK.eq hz'K]
  exact hz'K'

theorem Std20Frame.late_ne_inv (d : Std20Frame K K' J S R R' W V z t) : t ≠ z :=
  aviol_ne_involution d.late_hΩ d.late_mem_K d.viol

private theorem Std20Frame.late_toF (d : Std20Frame K K' J S R R' W V z t) :
    Std20F K K' J S R R' W V z t :=
  { d with
    hyp := d.late_hΩ
    late_ne_inv := d.late_ne_inv
    late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.late_hΩ d.viol.star d.viol.hzJ
    late_card2 := fun hU hK hR =>
      Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ hU hK hR }

theorem Std20Frame.late_J_ne_K (d : Std20Frame K K' J S R R' W V z t) : J ≠ K := d.viol.ne

theorem Std20Frame.late_R_eq (d : Std20Frame K K' J S R R' W V z t) : R = K ⊓ (S : Subgroup G) := by
  exact d.late_toF.late_R_eq

theorem Std20Frame.late_R'_eq (d : Std20Frame K K' J S R R' W V z t) :
    R' = K' ⊓ (S : Subgroup G) := by
  exact d.late_toF.late_R'_eq

theorem Std20Frame.late_K'_le (d : Std20Frame K K' J S R R' W V z t) :
    K' ≤ Subgroup.normalizer (K : Set G) :=
  d.late_toF.late_K'_le

theorem Std20Frame.late_K_le (d : Std20Frame K K' J S R R' W V z t) :
    K ≤ Subgroup.normalizer (K' : Set G) :=
  d.late_toF.late_K_le

theorem Std20Frame.late_conj_K (d : Std20Frame K K' J S R R' W V z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g K = K ∨ conjSub g K = K' := by
  exact d.late_toF.late_conj_K hg

theorem Std20Frame.late_conj_K' (d : Std20Frame K K' J S R R' W V z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g K' = K ∨ conjSub g K' = K' := by
  exact d.late_toF.late_conj_K' hg

theorem Std20Frame.late_conj_iff (d : Std20Frame K K' J S R R' W V z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g K = K ↔ conjSub g K' = K' := by
  exact d.late_toF.late_conj_iff hg

theorem Std20Frame.late_S_inf_sup (d : Std20Frame K K' J S R R' W V z t) :
    (S : Subgroup G) ⊓ (K ⊔ K') = R ⊔ R' := by
  exact d.late_toF.late_S_inf_sup

theorem Std20Frame.late_98 (d : Std20Frame K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) (hWeq : W = (W ⊓ K) ⊔ (W ⊓ J))
    {X : Subgroup G} (hX2 : IsPGroup 2 X) (hXS : X ≤ (S : Subgroup G))
    (hXt : ∀ x ∈ X, x * t = t * x) (hXK : ∀ x ∈ X, conjSub x K = K) :
    ((∀ x ∈ X, conjSub x K = K) ↔ (∀ x ∈ X, conjSub x J = J)) ∧
      ((∀ x ∈ X, ∀ w ∈ W ⊓ K, x * w = w * x) →
        ∃ A : Subgroup G,
          ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ X = ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ A ∧
          ((W ⊓ J) ⊔ (W ⊓ K)) ⊓ A = ⊥ ∧
          (∀ a ∈ A, ∀ y ∈ (W ⊓ J) ⊔ (W ⊓ K), a * y = y * a) ∧
          A ≤ centralizerModOdd ⊤ (K ⊔ K') ∧ A ≤ centralizerModOdd ⊤ J) := by
  exact d.late_toF.late_98 hJW hWeq hX2 hXS hXt hXK

theorem Std20Frame.late_tor (d : Std20Frame K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) (hWeq : W = (W ⊓ K) ⊔ (W ⊓ J)) :
    ∃ r ∈ R, ∃ r' ∈ R', (∀ x ∈ W, (r * r') * x * (r * r')⁻¹ = x⁻¹) ∧ r * t * r⁻¹ = z * t := by
  exact d.late_toF.late_tor hJW hWeq

end Std

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
