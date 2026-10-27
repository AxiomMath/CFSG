module

public import CFSG.ClassicalInvolution.Q3.Q3T6DConj
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenE612
public import CFSG.ClassicalInvolution.Asc77.AscR10G2Q
import CFSG.ClassicalInvolution.Asc77.AscT3CLateCfgEng
public import CFSG.ClassicalInvolution.Q3.Q3T6DStmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Three.late_hΩ (d : Std20Three K K' J S R R' W V z t) :
    HypOmegaGen (CoreAssembly.conjClass K) :=
  hypGen_of_modU d.hyp

theorem Std20Three.late_mem_K (_d : Std20Three K K' J S R R' W V z t) :
    K ∈ CoreAssembly.conjClass K :=
  CoreAssembly.mem_conjClass_self K

theorem Std20Three.late_mem_J (d : Std20Three K K' J S R R' W V z t) :
    J ∈ CoreAssembly.conjClass K :=
  d.viol.mem

theorem Std20Three.late_mem_K' (d : Std20Three K K' J S R R' W V z t) :
    K' ∈ CoreAssembly.conjClass K := by
  have h : K' ∈ twinSet (CoreAssembly.conjClass K) K := by rw [d.twins]; exact Or.inr rfl
  exact h.1

theorem Std20Three.late_hzK' (d : Std20Three K K' J S R R' W V z t) : IsUniqueInvolution K' z := by
  have h : K' ∈ twinSet (CoreAssembly.conjClass K) K := by rw [d.twins]; exact Or.inr rfl
  obtain ⟨-, z', hz'K, hz'K'⟩ := h
  rw [d.viol.hzK.eq hz'K]
  exact hz'K'

theorem Std20Three.late_ne_inv (d : Std20Three K K' J S R R' W V z t) : t ≠ z :=
  AViol.ne_involution_gen d.late_hΩ d.late_mem_K d.viol

private theorem Std20Three.late_toF (d : Std20Three K K' J S R R' W V z t) :
    Std20F K K' J S R R' W V z t :=
  { d with
    hyp := d.late_hΩ
    late_ne_inv := d.late_ne_inv
    late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.late_hΩ d.viol.star d.viol.hzJ
    late_card2 := fun hU hK hR =>
      Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ hU hK hR }

theorem Std20Three.late_J_ne_K (d : Std20Three K K' J S R R' W V z t) : J ≠ K := d.viol.ne

theorem Std20Three.late_J_ne_K' (d : Std20Three K K' J S R R' W V z t) : J ≠ K' := by
  exact d.late_toF.late_J_ne_K'

theorem Std20Three.late_R_eq (d : Std20Three K K' J S R R' W V z t) : R = K ⊓ (S : Subgroup G) := by
  exact d.late_toF.late_R_eq

theorem Std20Three.late_R'_eq (d : Std20Three K K' J S R R' W V z t) :
    R' = K' ⊓ (S : Subgroup G) := by
  exact d.late_toF.late_R'_eq

theorem Std20Three.late_K'_le (d : Std20Three K K' J S R R' W V z t) :
    K' ≤ Subgroup.normalizer (K : Set G) :=
  d.late_toF.late_K'_le

theorem Std20Three.late_K_le (d : Std20Three K K' J S R R' W V z t) :
    K ≤ Subgroup.normalizer (K' : Set G) :=
  d.late_toF.late_K_le

theorem Std20Three.late_conj_K (d : Std20Three K K' J S R R' W V z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g K = K ∨ conjSub g K = K' := by
  exact d.late_toF.late_conj_K hg

theorem Std20Three.late_conj_K' (d : Std20Three K K' J S R R' W V z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g K' = K ∨ conjSub g K' = K' := by
  exact d.late_toF.late_conj_K' hg

theorem Std20Three.late_conj_iff (d : Std20Three K K' J S R R' W V z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g K = K ↔ conjSub g K' = K' := by
  exact d.late_toF.late_conj_iff hg

theorem Std20Three.late_cent_le_normalizer_sup (d : Std20Three K K' J S R R' W V z t) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) := by
  exact d.late_toF.late_cent_le_normalizer_sup

theorem Std20Three.late_S_inf_sup (d : Std20Three K K' J S R R' W V z t) :
    (S : Subgroup G) ⊓ (K ⊔ K') = R ⊔ R' := by
  exact d.late_toF.late_S_inf_sup

theorem Std20Three.late_isSylow2In_RR' (d : Std20Three K K' J S R R' W V z t) :
    IsSylow2In (R ⊔ R') (K ⊔ K') :=
  d.late_toF.late_isSylow2In_RR'

theorem Std20Three.late_J_not_twin (d : Std20Three K K' J S R R' W V z t) :
    J ∉ twinSet (CoreAssembly.conjClass K) K := by
  exact d.late_toF.late_J_not_twin

theorem Std20Three.late_inA (d : Std20Three K K' J S R R' W V z t) :
    InA (CoreAssembly.conjClass K) K J :=
  d.late_toF.late_inA

theorem Std20Three.late_JW_data (d : Std20Three K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    IsPGroup 2 ↥(J ⊓ W) ∧ 4 ≤ Nat.card ↥(J ⊓ W) := by
  exact d.late_toF.late_JW_data hJW

theorem Std20Three.late_t_mem_JW (d : Std20Three K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) : t ∈ J ⊓ W := by
  exact d.late_toF.late_t_mem_JW hJW

theorem Std20Three.late_JW_le_N_K (d : Std20Three K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    J ⊓ W ≤ Subgroup.normalizer (K : Set G) := by
  exact d.late_toF.late_JW_le_N_K hJW

theorem Std20Three.late_JW_le_N_K' (d : Std20Three K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    J ⊓ W ≤ Subgroup.normalizer (K' : Set G) := by
  exact d.late_toF.late_JW_le_N_K' hJW

theorem Std20Three.late_isSylow2In_JW (d : Std20Three K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    IsSylow2In (J ⊓ W) (J ⊓ Subgroup.centralizer ({z} : Set G)) := by
  exact d.late_toF.late_isSylow2In_JW hJW

theorem Std20Three.late_isSylow2In_P (d : Std20Three K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    IsSylow2In (R ⊔ R' ⊔ (J ⊓ W))
      ((K ⊔ K') ⊔ (J ⊓ Subgroup.centralizer ({z} : Set G))) := by
  exact d.late_toF.late_isSylow2In_P hJW

theorem Std20Three.late_P_le_S (d : Std20Three K K' J S R R' W V z t) :
    R ⊔ R' ⊔ (J ⊓ W) ≤ (S : Subgroup G) :=
  d.late_toF.late_P_le_S

theorem Std20Three.late_P_inv (d : Std20Three K K' J S R R' W V z t)
    (hWeq : W = (W ⊓ K) ⊔ (W ⊓ J)) {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxK : conjSub x K = K) :
    conjSub x (R ⊔ R' ⊔ (J ⊓ W)) = R ⊔ R' ⊔ (J ⊓ W) := by
  exact d.late_toF.late_P_inv hWeq hxS hxK

theorem Std20Three.late_98 (d : Std20Three K K' J S R R' W V z t)
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

theorem Std20Three.late_cfg98 (d : Std20Three K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    Sec7.Cfg98 (CoreAssembly.conjClass K) K J K' ⊥ (R ⊔ R' ⊔ (J ⊓ W)) z t S W := by
  exact d.late_toF.late_cfg98 hJW

theorem Std20Three.late_tor (d : Std20Three K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) (hWeq : W = (W ⊓ K) ⊔ (W ⊓ J)) :
    ∃ r ∈ R, ∃ r' ∈ R', (∀ x ∈ W, (r * r') * x * (r * r')⁻¹ = x⁻¹) ∧ r * t * r⁻¹ = z * t := by
  exact d.late_toF.late_tor hJW hWeq


end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
