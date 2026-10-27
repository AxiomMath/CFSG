module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIStmt
public import CFSG.ClassicalInvolution.AschTight.HypOmegaGenMod
import CFSG.ClassicalInvolution.Asc77.AscT3CLateCfgEng
public import CFSG.ClassicalInvolution.AschTight.Sec7L98B

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Elementary

variable {G : Type} [Group G]

theorem late_natCard_conjSub (n : G) (A : Subgroup G) :
    Nat.card ↥(conjSub n A) = Nat.card ↥A :=
  late_natCard_conjSubE n A

theorem late_conjSub_inf (n : G) (A B : Subgroup G) :
    conjSub n (A ⊓ B) = conjSub n A ⊓ conjSub n B :=
  late_conjSub_infE n A B

theorem late_conjSub_sup (n : G) (A B : Subgroup G) :
    conjSub n (A ⊔ B) = conjSub n A ⊔ conjSub n B :=
  late_conjSub_supE n A B

theorem late_mem_normalizer_inf {A B : Subgroup G} {n : G}
    (hA : n ∈ Subgroup.normalizer (A : Set G)) (hB : n ∈ Subgroup.normalizer (B : Set G)) :
    n ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  exact late_mem_normalizer_infE hA hB

theorem late_mem_normalizer_sup {A B : Subgroup G} {n : G}
    (hA : n ∈ Subgroup.normalizer (A : Set G)) (hB : n ∈ Subgroup.normalizer (B : Set G)) :
    n ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  exact late_mem_normalizer_supE hA hB

theorem late_conjSub_eq_of_le {A B : Subgroup G} [Finite G] {n : G} (h : conjSub n A ≤ B)
    (hc : Nat.card ↥B ≤ Nat.card ↥A) : conjSub n A = B :=
  late_conjSub_eq_of_leE h hc

theorem late_le_normalizer_of_comm_le {A K : Subgroup G} (h : ⁅A, K⁆ ≤ K) :
    A ≤ Subgroup.normalizer (K : Set G) := by
  exact late_le_normalizer_of_comm_leE h

end Elementary

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20.late_hΩ (d : Std20 p f K K' J S R R' W V z t) :
    HypOmegaGen (CoreAssembly.conjClass K) :=
  hypOmegaGen_of_mod d.branch.odd d.branch.five d.hyp

theorem Std20.late_mem_K (_d : Std20 p f K K' J S R R' W V z t) :
    K ∈ CoreAssembly.conjClass K :=
  CoreAssembly.mem_conjClass_self K

theorem Std20.late_mem_J (d : Std20 p f K K' J S R R' W V z t) :
    J ∈ CoreAssembly.conjClass K :=
  d.viol.mem

theorem Std20.late_mem_K' (d : Std20 p f K K' J S R R' W V z t) :
    K' ∈ CoreAssembly.conjClass K := by
  have h : K' ∈ twinSet (CoreAssembly.conjClass K) K := by rw [d.twins]; exact Or.inr rfl
  exact h.1

theorem Std20.late_hzK' (d : Std20 p f K K' J S R R' W V z t) : IsUniqueInvolution K' z := by
  have h : K' ∈ twinSet (CoreAssembly.conjClass K) K := by rw [d.twins]; exact Or.inr rfl
  obtain ⟨-, z', hz'K, hz'K'⟩ := h
  rw [d.viol.hzK.eq hz'K]
  exact hz'K'

theorem Std20.late_ne_inv (d : Std20 p f K K' J S R R' W V z t) : t ≠ z :=
  d.viol.ne_involution d.hyp d.late_mem_K

private theorem Std20.late_toF (d : Std20 p f K K' J S R R' W V z t) :
    Std20F K K' J S R R' W V z t :=
  { d with
    hyp := d.late_hΩ
    late_ne_inv := d.late_ne_inv
    late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.branch.odd d.hyp d.viol.star d.viol.hzJ
    late_card2 := fun hU hK hR =>
      Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp hU hK hR }

theorem Std20.late_J_ne_K (d : Std20 p f K K' J S R R' W V z t) : J ≠ K := d.viol.ne

theorem Std20.late_J_ne_K' (d : Std20 p f K K' J S R R' W V z t) : J ≠ K' := by
  exact d.late_toF.late_J_ne_K'

theorem Std20.late_R_eq (d : Std20 p f K K' J S R R' W V z t) : R = K ⊓ (S : Subgroup G) := by
  exact d.late_toF.late_R_eq

theorem Std20.late_R'_eq (d : Std20 p f K K' J S R R' W V z t) : R' = K' ⊓ (S : Subgroup G) := by
  exact d.late_toF.late_R'_eq

theorem Std20.late_K'_le (d : Std20 p f K K' J S R R' W V z t) :
    K' ≤ Subgroup.normalizer (K : Set G) :=
  d.late_toF.late_K'_le

theorem Std20.late_K_le (d : Std20 p f K K' J S R R' W V z t) :
    K ≤ Subgroup.normalizer (K' : Set G) :=
  d.late_toF.late_K_le

theorem Std20.late_conj_K (d : Std20 p f K K' J S R R' W V z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g K = K ∨ conjSub g K = K' := by
  exact d.late_toF.late_conj_K hg

theorem Std20.late_conj_K' (d : Std20 p f K K' J S R R' W V z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g K' = K ∨ conjSub g K' = K' := by
  exact d.late_toF.late_conj_K' hg

theorem Std20.late_conj_iff (d : Std20 p f K K' J S R R' W V z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g K = K ↔ conjSub g K' = K' := by
  exact d.late_toF.late_conj_iff hg

theorem Std20.late_cent_le_normalizer_sup (d : Std20 p f K K' J S R R' W V z t) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) := by
  exact d.late_toF.late_cent_le_normalizer_sup

theorem Std20.late_S_inf_sup (d : Std20 p f K K' J S R R' W V z t) :
    (S : Subgroup G) ⊓ (K ⊔ K') = R ⊔ R' := by
  exact d.late_toF.late_S_inf_sup

theorem Std20.late_isSylow2In_RR' (d : Std20 p f K K' J S R R' W V z t) :
    IsSylow2In (R ⊔ R') (K ⊔ K') :=
  d.late_toF.late_isSylow2In_RR'

theorem Std20.late_J_not_twin (d : Std20 p f K K' J S R R' W V z t) :
    J ∉ twinSet (CoreAssembly.conjClass K) K := by
  exact d.late_toF.late_J_not_twin

theorem Std20.late_inA (d : Std20 p f K K' J S R R' W V z t) :
    InA (CoreAssembly.conjClass K) K J :=
  d.late_toF.late_inA

theorem Std20.late_JW_data (d : Std20 p f K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    IsPGroup 2 ↥(J ⊓ W) ∧ 4 ≤ Nat.card ↥(J ⊓ W) := by
  exact d.late_toF.late_JW_data hJW

theorem Std20.late_t_mem_JW (d : Std20 p f K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) : t ∈ J ⊓ W := by
  exact d.late_toF.late_t_mem_JW hJW

theorem Std20.late_JW_le_N_K (d : Std20 p f K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    J ⊓ W ≤ Subgroup.normalizer (K : Set G) := by
  exact d.late_toF.late_JW_le_N_K hJW

theorem Std20.late_JW_le_N_K' (d : Std20 p f K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    J ⊓ W ≤ Subgroup.normalizer (K' : Set G) := by
  exact d.late_toF.late_JW_le_N_K' hJW

theorem Std20.late_isSylow2In_JW (d : Std20 p f K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    IsSylow2In (J ⊓ W) (J ⊓ Subgroup.centralizer ({z} : Set G)) := by
  exact d.late_toF.late_isSylow2In_JW hJW

theorem Std20.late_isSylow2In_P (d : Std20 p f K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    IsSylow2In (R ⊔ R' ⊔ (J ⊓ W))
      ((K ⊔ K') ⊔ (J ⊓ Subgroup.centralizer ({z} : Set G))) := by
  exact d.late_toF.late_isSylow2In_P hJW

theorem Std20.late_P_le_S (d : Std20 p f K K' J S R R' W V z t) :
    R ⊔ R' ⊔ (J ⊓ W) ≤ (S : Subgroup G) :=
  d.late_toF.late_P_le_S

theorem Std20.late_P_inv (d : Std20 p f K K' J S R R' W V z t)
    (hWeq : W = (W ⊓ K) ⊔ (W ⊓ J)) {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxK : conjSub x K = K) :
    conjSub x (R ⊔ R' ⊔ (J ⊓ W)) = R ⊔ R' ⊔ (J ⊓ W) := by
  exact d.late_toF.late_P_inv hWeq hxS hxK

theorem Std20.late_98 (d : Std20 p f K K' J S R R' W V z t)
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

theorem Std20.late_cfg98 (d : Std20 p f K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) :
    Sec7.Cfg98 (CoreAssembly.conjClass K) K J K' ⊥ (R ⊔ R' ⊔ (J ⊓ W)) z t S W := by
  exact d.late_toF.late_cfg98 hJW

theorem Std20.late_tor (d : Std20 p f K K' J S R R' W V z t)
    (hJW : J ⊓ W ∈ USet (CoreAssembly.conjClass K)) (hWeq : W = (W ⊓ K) ⊔ (W ⊓ J)) :
    ∃ r ∈ R, ∃ r' ∈ R', (∀ x ∈ W, (r * r') * x * (r * r')⁻¹ = x⁻¹) ∧ r * t * r⁻¹ = z * t := by
  exact d.late_toF.late_tor hJW hWeq

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
