module

public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.InvolutionPair

public section

namespace CFSG.CGT.Higman76

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

def fourGroup (a b : G) : Subgroup G := Subgroup.closure ({a, b} : Set G)

theorem mem_fourGroup_left (a b : G) : a ∈ fourGroup a b :=
  Subgroup.subset_closure (Set.mem_insert a {b})

theorem mem_fourGroup_right (a b : G) : b ∈ fourGroup a b :=
  Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)

theorem exists_conj_pair (S : Sylow 2 G) {a : G} (ha : orderOf a = 2) (haS : a ∈ S)
    (h2 : {x | x ∈ S ∧ IsConj a x}.ncard = 2) :
    ∃ b : G, b ≠ a ∧ b ∈ S ∧ IsConj a b ∧ orderOf b = 2 ∧
      ∀ x : G, x ∈ S → IsConj a x → x = a ∨ x = b := by
  classical
  let T : Set G := {x | x ∈ S ∧ IsConj a x}
  have h2' : T.ncard = 2 := h2
  obtain ⟨x, y, hxy, hT⟩ := Set.ncard_eq_two.mp h2'
  have haT : a ∈ T := ⟨haS, IsConj.refl a⟩
  have haxy : a = x ∨ a = y := by
    have : a ∈ ({x, y} : Set G) := hT ▸ haT
    simpa using this
  have ha2 : a * a = 1 := mul_eq_one_iff_eq_inv.mpr (inv_eq_self_of_orderOf_eq_two ha).symm
  have hb_ne_one : ∀ b : G, IsConj a b → b ≠ 1 := by
    intro b hbconj h
    obtain ⟨c, hc⟩ := isConj_iff.mp hbconj
    have haz : a = 1 := by
      have h1 : c * a * c⁻¹ = 1 := hc.trans h
      have := congrArg (fun w => c⁻¹ * w * c) h1
      simpa [mul_assoc] using this
    rw [haz] at ha
    simp at ha
  have horder : ∀ b : G, IsConj a b → orderOf b = 2 := by
    intro b hbconj
    obtain ⟨c, hc⟩ := isConj_iff.mp hbconj
    have hbb : b * b = 1 := by
      rw [← hc]
      calc (c * a * c⁻¹) * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
        _ = 1 := by rw [ha2]; group
    exact orderOf_eq_prime (by rwa [pow_two]) (hb_ne_one b hbconj)
  rcases haxy with hax | hay
  · refine ⟨y, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hax]; exact hxy.symm
    · exact (show y ∈ T from hT ▸ Set.mem_insert_of_mem x rfl).1
    · exact (show y ∈ T from hT ▸ Set.mem_insert_of_mem x rfl).2
    · exact horder y (show y ∈ T from hT ▸ Set.mem_insert_of_mem x rfl).2
    · intro z hzS hzc
      have hzT : z ∈ T := ⟨hzS, hzc⟩
      rw [hT] at hzT
      rw [show x = a from hax.symm] at hzT
      simpa using hzT
  · refine ⟨x, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hay]; exact hxy
    · exact (show x ∈ T from hT ▸ Set.mem_insert x {y}).1
    · exact (show x ∈ T from hT ▸ Set.mem_insert x {y}).2
    · exact horder x (show x ∈ T from hT ▸ Set.mem_insert x {y}).2
    · intro z hzS hzc
      have hzT : z ∈ T := ⟨hzS, hzc⟩
      rw [hT] at hzT
      rw [show y = a from hay.symm] at hzT
      simpa [or_comm] using hzT

theorem mul_comm_of_conj_pair (S : Sylow 2 G) {a b : G} (hb : orderOf b = 2)
    (haS : a ∈ S) (hbS : b ∈ S) (hne : a ≠ b)
    (hcl : ∀ x : G, x ∈ S → IsConj a x → x = a ∨ x = b) :
    a * b = b * a := by
  have hb2 : b * b = 1 := mul_eq_one_iff_eq_inv.mpr (inv_eq_self_of_orderOf_eq_two hb).symm
  have hmem : b * a * b⁻¹ ∈ S := mul_mem (mul_mem hbS haS) (inv_mem hbS)
  have hconj : IsConj a (b * a * b⁻¹) := isConj_iff.mpr ⟨b, by group⟩
  rcases hcl (b * a * b⁻¹) hmem hconj with h | h
  · have hba : b * a = a * b := by
      have := congrArg (fun w => w * b) h
      simpa [mul_assoc, hb2] using this
    exact hba.symm
  · have hba : b * a = 1 := by
      have := congrArg (fun w => w * b) h
      simpa [mul_assoc, hb2] using this
    exact absurd (mul_left_cancel (hba.trans hb2.symm)) hne

theorem fourGroup_le {a b : G} {S : Subgroup G} (ha : a ∈ S) (hb : b ∈ S) :
    fourGroup a b ≤ S := by
  rw [fourGroup, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

theorem fourGroup_card {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hcomm : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : Nat.card (fourGroup a b) = 4 :=
  CFSG.GroupTheory.card_closure_pair_eq_four ha hb hcomm ha1 hb1 hne

theorem fourGroup_isElemAbelian {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hcomm : a * b = b * a) : IsElemAbelian 2 (fourGroup a b) := by
  rw [fourGroup]
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hcomm
    · exact hcomm.symm
    · rfl
  · intro x hx
    rcases hx with rfl | rfl
    · simpa [pow_two] using ha
    · simpa [pow_two] using hb

theorem mul_not_conj (S : Sylow 2 G) {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (haS : a ∈ S) (hbS : b ∈ S) (hne : a ≠ b) (hcomm : a * b = b * a)
    (hcl : ∀ x : G, x ∈ S → IsConj a x → x = a ∨ x = b) :
    a * b ≠ 1 ∧ a * b ∈ S ∧ ¬ IsConj a (a * b) ∧ orderOf (a * b) = 2 := by
  have ha2 : a * a = 1 := mul_eq_one_iff_eq_inv.mpr (inv_eq_self_of_orderOf_eq_two ha).symm
  have hb2 : b * b = 1 := mul_eq_one_iff_eq_inv.mpr (inv_eq_self_of_orderOf_eq_two hb).symm
  have hnot := mul_notMem_of_orderOf_eq_two ha hb hne
  have hz1 : a * b ≠ 1 := fun h => hnot (by simp [h])
  have hza : a * b ≠ a := fun h => hnot (by simp [h])
  have hzb : a * b ≠ b := fun h => hnot (by simp [h])
  have hzS : a * b ∈ S := mul_mem haS hbS
  have hzconj : ¬ IsConj a (a * b) := by
    intro hc
    rcases hcl (a * b) hzS hc with h | h
    · exact hza h
    · exact hzb h
  have hz2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  exact ⟨hz1, hzS, hzconj, orderOf_eq_prime (by rwa [pow_two]) hz1⟩

theorem fourGroup_weakly_closed (S : Sylow 2 G) {a b : G} (hab : IsConj a b)
    (hcl : ∀ x : G, x ∈ S → IsConj a x → x = a ∨ x = b) :
    ∀ g : G, (fourGroup a b).map (MulAut.conj g⁻¹).toMonoidHom ≤ S →
      (fourGroup a b).map (MulAut.conj g⁻¹).toMonoidHom = fourGroup a b := by
  intro g hg
  have hle : (fourGroup a b).map (MulAut.conj g⁻¹).toMonoidHom ≤ fourGroup a b := by
    rw [fourGroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro x ⟨y, hy, rfl⟩
    have hyab : y = a ∨ y = b := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hy
    have hmem_map : (MulAut.conj g⁻¹).toMonoidHom y ∈
        (fourGroup a b).map (MulAut.conj g⁻¹).toMonoidHom :=
      ⟨y, Subgroup.subset_closure (by simpa using hy), rfl⟩
    have hxS : (MulAut.conj g⁻¹).toMonoidHom y ∈ S := hg hmem_map
    have hconj : IsConj a ((MulAut.conj g⁻¹).toMonoidHom y) := by
      rcases hyab with rfl | rfl
      · exact isConj_iff.mpr ⟨g⁻¹, by simp [MulAut.conj_apply, mul_assoc]⟩
      · exact IsConj.trans hab
          (isConj_iff.mpr ⟨g⁻¹, by simp [MulAut.conj_apply, mul_assoc]⟩)
    rcases hcl _ hxS hconj with h | h
    · rw [h]; exact mem_fourGroup_left a b
    · rw [h]; exact mem_fourGroup_right a b
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

theorem normalClosure_fourGroup_eq_top {a b : G}
    (hgen : Subgroup.normalClosure ({a} : Set G) = ⊤) :
    Subgroup.normalClosure (fourGroup a b : Set G) = ⊤ := by
  have hle : Subgroup.normalClosure ({a} : Set G) ≤
      Subgroup.normalClosure (fourGroup a b : Set G) := by
    refine Subgroup.normalClosure_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact mem_fourGroup_left a b
  rw [hgen] at hle
  exact top_le_iff.mp hle

end CFSG.CGT.Higman76
