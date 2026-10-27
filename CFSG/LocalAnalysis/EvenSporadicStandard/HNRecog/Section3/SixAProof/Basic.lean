module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z x : G}

theorem sixA_of_mem (hx : x ∈ orb6A a a) :
    IsConj a x ∧ orderOf (a * x) = 6 ∧ IsConj a ((a * x) ^ 3) := hx

theorem sixA_a_sq (h : IsF5Type a z) : a ^ 2 = 1 := by
  rw [← h.orderOf_a]; exact pow_orderOf_eq_one a

theorem sixA_x_sq (h : IsF5Type a z) (hx : x ∈ orb6A a a) : x ^ 2 = 1 := by
  have := perp_orderOf_of_isConj_a h (sixA_of_mem hx).1
  rw [← this]; exact pow_orderOf_eq_one x

theorem sixA_orderOf_b (h : IsF5Type a z) (hx : x ∈ orb6A a a) : orderOf ((a * x) ^ 3) = 2 :=
  perp_orderOf_of_isConj_a h (sixA_of_mem hx).2.2

theorem sixA_b_sq (h : IsF5Type a z) (hx : x ∈ orb6A a a) : ((a * x) ^ 3) ^ 2 = 1 := by
  rw [← sixA_orderOf_b h hx]; exact pow_orderOf_eq_one _

theorem sixA_b_mul_b (h : IsF5Type a z) (hx : x ∈ orb6A a a) :
    (a * x) ^ 3 * (a * x) ^ 3 = 1 := by
  rw [← pow_two]; exact sixA_b_sq h hx

theorem sixA_dihedral (h : IsF5Type a z) (hx : x ∈ orb6A a a) :
    a * (a * x) ^ 3 = (a * x) ^ 3 * a ∧ x * (a * x) ^ 3 = (a * x) ^ 3 * x ∧
      IsConj a (a * (a * x) ^ 3) ∧ IsConj a (x * (a * x) ^ 3) :=
  tableV_dihedral (sixA_a_sq h) (sixA_x_sq h hx) (sixA_of_mem hx).1 (m := 3)
    (by rw [(sixA_of_mem hx).2.1])

theorem sixA_comm_ab (h : IsF5Type a z) (hx : x ∈ orb6A a a) :
    a * (a * x) ^ 3 = (a * x) ^ 3 * a := (sixA_dihedral h hx).1

theorem sixA_comm_xb (h : IsF5Type a z) (hx : x ∈ orb6A a a) :
    x * (a * x) ^ 3 = (a * x) ^ 3 * x := (sixA_dihedral h hx).2.1

theorem sixA_conj_ab (h : IsF5Type a z) (hx : x ∈ orb6A a a) :
    IsConj a (a * (a * x) ^ 3) := (sixA_dihedral h hx).2.2.1

theorem sixA_conj_y (h : IsF5Type a z) (hx : x ∈ orb6A a a) :
    IsConj a (x * (a * x) ^ 3) := (sixA_dihedral h hx).2.2.2

theorem sixA_y_mul_b (h : IsF5Type a z) (hx : x ∈ orb6A a a) :
    x * (a * x) ^ 3 * (a * x) ^ 3 = x := by
  rw [mul_assoc, sixA_b_mul_b h hx, mul_one]

theorem sixA_mul_eq (h : IsF5Type a z) (hx : x ∈ orb6A a a) (t : G) :
    x * t = x * (a * x) ^ 3 * ((a * x) ^ 3 * t) := by
  rw [mul_assoc, ← mul_assoc ((a * x) ^ 3), sixA_b_mul_b h hx, one_mul]

theorem sixA_orderOf_ay (h : IsF5Type a z) (hx : x ∈ orb6A a a) :
    orderOf (a * (x * (a * x) ^ 3)) = 3 := by
  have h4 : a * (x * (a * x) ^ 3) = (a * x) ^ 4 := by
    rw [← mul_assoc, pow_succ' (a * x) 3]
  rw [h4, orderOf_pow' _ (by norm_num), (sixA_of_mem hx).2.1]
  norm_num

theorem sixA_y_mem_orb3A (h : IsF5Type a z) (hx : x ∈ orb6A a a) :
    x * (a * x) ^ 3 ∈ orb3A a a := by
  refine ⟨sixA_conj_y h hx, sixA_orderOf_ay h hx, (a * x) ^ 3, ?_, ?_⟩
  · exact ⟨(sixA_of_mem hx).2.2, sixA_conj_ab h hx⟩
  · refine ⟨(sixA_of_mem hx).2.2, ?_⟩
    show IsConj a (x * (a * x) ^ 3 * (a * x) ^ 3)
    rw [sixA_y_mul_b h hx]
    exact (sixA_of_mem hx).1

theorem sixA_b_mem_orb2A (h : IsF5Type a z) (hx : x ∈ orb6A a a) :
    (a * x) ^ 3 ∈ orb2A a a ∩ orb2A a (x * (a * x) ^ 3) := by
  refine ⟨⟨(sixA_of_mem hx).2.2, sixA_conj_ab h hx⟩, (sixA_of_mem hx).2.2, ?_⟩
  show IsConj a (x * (a * x) ^ 3 * (a * x) ^ 3)
  rw [sixA_y_mul_b h hx]
  exact (sixA_of_mem hx).1

theorem sixA_Gxy_le (a x : G) : Gxy a x ≤ Gxy a (x * (a * x) ^ 3) := by
  intro g hg
  rw [mem_Gxy, mem_Gx, mem_Gx] at hg ⊢
  have hag : Commute a g := hg.1
  have hxg : Commute x g := hg.2
  exact ⟨hag, (hxg.mul_left ((hag.mul_left hxg).pow_left 3) : Commute _ _)⟩

theorem sixA_comm_b_of_mem {g : G} (hg : g ∈ Gxy a x) : g * (a * x) ^ 3 = (a * x) ^ 3 * g := by
  rw [mem_Gxy, mem_Gx, mem_Gx] at hg
  have hag : Commute a g := hg.1
  have hxg : Commute x g := hg.2
  exact ((hag.mul_left hxg).pow_left 3).symm

theorem sixA_b_mem_Gxy_x (h : IsF5Type a z) (hx : x ∈ orb6A a a) :
    (a * x) ^ 3 ∈ Gxy a x := by
  rw [mem_Gxy, mem_Gx, mem_Gx]
  exact ⟨sixA_comm_ab h hx, sixA_comm_xb h hx⟩

theorem sixA_b_mem_Gxy_y (h : IsF5Type a z) (hx : x ∈ orb6A a a) :
    (a * x) ^ 3 ∈ Gxy a (x * (a * x) ^ 3) := by
  rw [mem_Gxy, mem_Gx, mem_Gx]
  refine ⟨sixA_comm_ab h hx, ?_⟩
  have h1 : Commute x ((a * x) ^ 3) := sixA_comm_xb h hx
  exact h1.mul_left (Commute.refl ((a * x) ^ 3))

theorem sixA_mem_Gxy_iff (h : IsF5Type a z) (hx : x ∈ orb6A a a) {g : G} :
    g ∈ Gxy a x ↔
      g ∈ Gxy a (x * (a * x) ^ 3) ∧ g * (a * x) ^ 3 = (a * x) ^ 3 * g := by
  constructor
  · intro hg
    exact ⟨sixA_Gxy_le a x hg, sixA_comm_b_of_mem hg⟩
  · rintro ⟨hy, hb⟩
    rw [mem_Gxy, mem_Gx, mem_Gx] at hy ⊢
    refine ⟨hy.1, ?_⟩
    have hy' : Commute (x * (a * x) ^ 3) g := hy.2
    have hb' : Commute ((a * x) ^ 3) g := hb.symm
    have : x = x * (a * x) ^ 3 * (a * x) ^ 3 := (sixA_y_mul_b h hx).symm
    rw [this]
    exact hy'.mul_left hb'

end CFSG.EvenSporadicStandard.HNRecog.Section3
