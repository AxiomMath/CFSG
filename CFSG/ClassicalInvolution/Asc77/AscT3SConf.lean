module

public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
public import CFSG.ClassicalInvolution.Asc77.AscT3SConfEng
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateHexMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Triple

variable {G : Type} [Group G]

theorem isElemAbelian_closure_three {x y w : G} (hx : x * x = 1) (hy : y * y = 1)
    (hw : w * w = 1) (hxy : x * y = y * x) (hxw : x * w = w * x) (hyw : y * w = w * y) :
    IsElemAbelian 2 (Subgroup.closure ({x, y, w} : Set G)) := by
  have hc : ∀ a ∈ ({x, y, w} : Set G), ∀ b ∈ ({x, y, w} : Set G), a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · rfl
    · exact hxy
    · exact hxw
    · exact hxy.symm
    · rfl
    · exact hyw
    · exact hxw.symm
    · exact hyw.symm
    · rfl
  have hsq : ∀ a ∈ ({x, y, w} : Set G), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hw
  refine ⟨⟨⟨fun a b => Subtype.ext (T7A.commutes_closure hc _ a.2 _ b.2)⟩⟩, fun v hv => ?_⟩
  rw [pow_two]
  exact T7A.sq_closure hsq hc v hv

theorem natCard_closure_three [Finite G] {x y w : G} (hx : x * x = 1) (hy : y * y = 1)
    (hw : w * w = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hw1 : w ≠ 1) (hxy' : x ≠ y)
    (hxy : x * y = y * x) (hxw : x * w = w * x) (hyw : y * w = w * y)
    (hnot : w ∉ Subgroup.closure ({x, y} : Set G)) :
    Nat.card ↥(Subgroup.closure ({x, y, w} : Set G)) = 8 := by
  have hD := T7A.isElemAbelian2_closure_pair hx hy hx1 hy1 hxy' hxy
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw) hw1
  have hcl : Subgroup.closure ({x, y, w} : Set G) =
      Subgroup.closure ({x, y} : Set G) ⊔ Subgroup.zpowers w := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · refine sup_le ?_ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
  have hcomm : Commutes (Subgroup.closure ({x, y} : Set G)) (Subgroup.zpowers w) := by
    have hle : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxw
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hyw
    intro v hv u hu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have : Commute v w := Subgroup.mem_centralizer_singleton_iff.mp (hle hv)
    exact (this.zpow_right i).eq
  have hinf : Subgroup.closure ({x, y} : Set G) ⊓ Subgroup.zpowers w = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rcases T7A.eq_one_or_eq_of_mem_zpowers hw2 he.2 with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · exact absurd (h1 ▸ he.1) hnot
  have hN := T7A.card_sup_mul_card_inf (T7A.le_normalizer_of_commutes hcomm)
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hw2, hD.1, mul_one] at hN
  rw [hcl, sup_comm, hN]
  norm_num

end Triple

section Conf

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K K' J : Subgroup G}
  {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t)
include d

theorem s_comm_z {a : G} (haS : a ∈ (S : Subgroup G)) : a * z = z * a :=
  Subgroup.mem_centralizer_singleton_iff.mp (d.hSz haS)

theorem s_a_not_mem_closure (c4 : Concl20_4 S K K' J z) {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J) (ha1 : a ≠ 1) :
    a ∉ Subgroup.closure ({z, t} : Set G) := by
  obtain ⟨r, hr, r', hr', -, hrt⟩ := d.late_tor d.late_JW d.late_hW
  exact CFSG.ClassicalInvolution.Asc77.T3CII.s_a_not_mem_closure_of d.viol.hzK
    d.viol.hzJ.sq d.late_zt_comm ⟨r, d.hR.1 hr, d.hRS hr, hrt⟩ c4 ha ha1

theorem s_comm_t {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J) :
    a * t = t * a := d.cent_comm_t ha.1

theorem s_B_isElemAbelian {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J)
    (ha2 : a * a = 1) : IsElemAbelian 2 (Subgroup.closure ({z, t, a} : Set G)) :=
  isElemAbelian_closure_three d.viol.hzK.sq d.viol.hzJ.sq ha2 d.late_zt_comm
    (d.s_comm_z ha.1.1).symm (d.s_comm_t ha).symm

theorem s_B_natCard (c4 : Concl20_4 S K K' J z) {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J) (ha1 : a ≠ 1)
    (ha2 : a * a = 1) : Nat.card ↥(Subgroup.closure ({z, t, a} : Set G)) = 8 :=
  natCard_closure_three d.viol.hzK.sq d.viol.hzJ.sq ha2 d.viol.hzK.ne_one d.viol.hzJ.ne_one ha1
    d.late_ne_inv.symm d.late_zt_comm (d.s_comm_z ha.1.1).symm (d.s_comm_t ha).symm
    (d.s_a_not_mem_closure c4 ha ha1)

theorem s_comm_K {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J) {k : G}
    (hk : k ∈ K) : ⁅a, k⁆ ∈ oddCoreOf K := by
  exact CFSG.ClassicalInvolution.Asc77.T3CII.comm_mem_oddCoreOf_of le_sup_left ha.1
    (d.cent_le_normalizer ha.1) hk

theorem s_comm_K' {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J) {k : G}
    (hk : k ∈ K') : ⁅a, k⁆ ∈ oddCoreOf K' := by
  exact CFSG.ClassicalInvolution.Asc77.T3CII.comm_mem_oddCoreOf_of le_sup_right ha.1
    (d.cent_le_normalizer' ha.1) hk

end Std20

end Conf

end CFSG.ClassicalInvolution.Asc77.T3CII
