module

import CFSG.ClassicalInvolution.Q3.Q3T6DC4Eng
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3Cfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1

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

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace Std20Frame

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem hK'Ω : K' ∈ CoreAssembly.conjClass K := by
  have : K' ∈ twinSet (CoreAssembly.conjClass K) K := by rw [d.twins]; exact Or.inr rfl
  exact this.1

theorem hz' : IsUniqueInvolution K' z := by
  have hK' : K' ∈ twinSet (CoreAssembly.conjClass K) K := by rw [d.twins]; exact Or.inr rfl
  obtain ⟨-, z', hzK, hzK'⟩ := hK'
  have e := d.viol.hzK.eq hzK
  subst e
  exact hzK'

theorem eight_le_R : 8 ≤ Nat.card R :=
  Sec6Gen.eight_le_of_mem_RSet d.late_hΩ 
    (mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) d.hR)

theorem z_mem_R : z ∈ R :=
  mem_of_isPGroup d.viol.hzK d.hR.1 d.hR.2.1 (by have := d.eight_le_R; omega)

theorem z_mem_S : z ∈ (S : Subgroup G) := d.hRS d.z_mem_R

theorem t_mem_S : t ∈ (S : Subgroup G) := d.hVS d.htV

theorem t_ne_z : t ≠ z :=
  aviol_ne_involution d.late_hΩ (CoreAssembly.mem_conjClass_self K) d.viol

theorem K_ne_K' : K ≠ K' := fun h => d.ne h.symm

theorem sup_le_centralizer_z : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) :=
  sup_le (fun _ hw => Subgroup.mem_centralizer_singleton_iff.mpr
    (d.viol.hzK.commute_of_mem hw).symm)
    (fun _ hw => Subgroup.mem_centralizer_singleton_iff.mpr (d.hz'.commute_of_mem hw).symm)

theorem z_mem_cent : z ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K') := by
  have hzM : z ∈ K ⊔ K' := Subgroup.mem_sup_left d.viol.hzK.mem
  refine ⟨d.z_mem_S, Subgroup.le_normalizer hzM,
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hzM), fun l hl => ?_⟩
  have := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (d.sup_le_centralizer_z hl)).symm
  rw [this]
  exact (oddCoreOf _).one_mem

theorem cent_comm_t {a : G} (ha : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K')) :
    a * t = t * a :=
  commutes_of_mem_centModOddCore S.isPGroup' (mem_centModOddCore_of_mem_centralizerModOdd ha)
    ha.1 d.htKK d.t_mem_S

theorem cent_comm_WK {a w : G} (ha : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K'))
    (hw : w ∈ W ⊓ K) : a * w = w * a :=
  commutes_of_mem_centModOddCore S.isPGroup' (mem_centModOddCore_of_mem_centralizerModOdd ha)
    ha.1 (Subgroup.mem_sup_left hw.2) (d.hWS hw.1)

theorem cent_le_normalizer {a : G} (ha : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K')) :
    a ∈ Subgroup.normalizer (K : Set G) := by
  have haS : a ∈ (S : Subgroup G) := ha.1
  have haC : a ∈ Subgroup.centralizer ({z} : Set G) := d.hSz haS
  rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inl rfl) haC with h | h
  · exact mem_normalizer_iff_conjSub_eq.mpr h
  · exfalso
    have hRle : R ≤ conjSub a R := fun r hr => by
      rw [mem_conjSub_iff]
      have hrM : r ∈ K ⊔ K' := Subgroup.mem_sup_left (d.hR.1 hr)
      have hcomm := commutes_of_mem_centModOddCore S.isPGroup'
        (mem_centModOddCore_of_mem_centralizerModOdd ha) haS hrM (d.hRS hr)
      have : a⁻¹ * r * a = r := by
        calc a⁻¹ * r * a = a⁻¹ * (r * a) := by group
          _ = a⁻¹ * (a * r) := by rw [hcomm]
          _ = r := by group
      rw [this]
      exact hr
    have hRK' : R ≤ K' := by
      rw [← h]
      exact hRle.trans (conjSub_mono d.hR.1)
    have := Sec6Gen.card_le_two_of_le_inf d.late_hΩ (CoreAssembly.mem_conjClass_self K) d.hK'Ω
      d.K_ne_K' d.hR.2.1 d.hR.1 hRK'
    have := d.eight_le_R
    omega

end Std20Frame

private theorem Std20Frame.late_toF (d : Std20Frame K K' J S R R' W V z t) :
    Std20F K K' J S R R' W V z t :=
  { d with
    hyp := d.late_hΩ
    late_ne_inv := d.late_ne_inv
    late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.late_hΩ d.viol.star d.viol.hzJ
    late_card2 := fun hU hK hR =>
      Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ hU hK hR }

theorem Std20Frame.concl20_4_of_98 (d : Std20Frame K K' J S R R' W V z t)
    (hex : Hex20 (CoreAssembly.conjClass K) K J W)
    (h98 : (∀ x ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K'), ∀ w ∈ W ⊓ K, x * w = w * x) →
      ∃ A' : Subgroup G,
        ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ centralizerModOdd (S : Subgroup G) (K ⊔ K') =
            ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ A' ∧
          ((W ⊓ J) ⊔ (W ⊓ K)) ⊓ A' = ⊥ ∧
          (∀ a ∈ A', ∀ y ∈ (W ⊓ J) ⊔ (W ⊓ K), a * y = y * a) ∧
          A' ≤ centralizerModOdd ⊤ (K ⊔ K') ∧ A' ≤ centralizerModOdd ⊤ J)
    (htor : ∃ r ∈ R, ∃ r' ∈ R', (∀ x ∈ W, (r * r') * x * (r * r')⁻¹ = x⁻¹) ∧
      r * t * r⁻¹ = z * t) :
    Concl20_4 S K K' J z := by
  exact d.late_toF.concl20_4_of_98 (fun {a w} ha hw => d.cent_comm_WK ha hw) d.z_mem_cent
    (by obtain ⟨η, ⟨S₁, hS₁, hinv⟩, hWη⟩ := d.hW; rw [hWη]; exact etaAbelian_of_gen d.late_hΩ η ⟨S₁, hS₁, hinv⟩)
    hex h98 htor

end Std


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
