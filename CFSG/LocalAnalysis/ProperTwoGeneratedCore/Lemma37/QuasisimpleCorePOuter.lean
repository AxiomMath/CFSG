module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePBasic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G}

theorem conj_mul_centralElt (hc : PartC T Q P₁ e u) (y a : G) :
    y * (a * e) * y⁻¹ = y * a * y⁻¹ * e := by
  calc y * (a * e) * y⁻¹ = y * a * (e * y⁻¹) := by group
    _ = y * a * (y⁻¹ * e) := by rw [hc.commute_centralElt y⁻¹]
    _ = y * a * y⁻¹ * e := by group

theorem inv_eq_mul_centralElt (hc : PartC T Q P₁ e u) {x : G} (hxx : x * x = e) :
    x⁻¹ = x * e :=
  inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hxx, hc.centralElt_mul_self])

theorem exists_inv_conj (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁)
    (hyy : y * y ∈ P₁) :
    ∃ v ∈ Q, v * v = e ∧ y * v * y⁻¹ = v⁻¹ ∧
      ∀ w ∈ Q, (y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) →
        w = 1 ∨ w = e ∨ w = v ∨ w = v * e := by
  obtain ⟨m, hm, hm1, hm2⟩ := hc.outer y hyT hy
  obtain ⟨hmm, hb, hbb⟩ := hc.moved_facts hyT hm hm1
  set b := y * m * y⁻¹ with hbdef
  have hyb : y * b * y⁻¹ = m := by
    have h := hc.commute m hm _ hyy
    calc y * b * y⁻¹ = (y * y) * m * (y * y)⁻¹ := by rw [hbdef]; group
      _ = m * (y * y) * (y * y)⁻¹ := by rw [h]
      _ = m := by group
  have hmb := hc.anticomm hm hb hmm hbb hm1 hm2
  have hbme : b = b * e * e := (hc.mul_centralElt_mul_centralElt b).symm
  refine ⟨m * b, Q.mul_mem hm hb, ?_, ?_, ?_⟩
  · refine hc.mul_self_of_ne (Q.mul_mem hm hb) (fun h => hm2 ?_) (fun h => hm1 ?_)
    · rw [eq_inv_of_mul_eq_one_right h, hc.inv_eq_mul_centralElt hmm]
    · calc b = m⁻¹ * (m * b) := by group
        _ = m := by rw [h, hc.inv_eq_mul_centralElt hmm, hc.mul_centralElt_mul_centralElt]
  · calc y * (m * b) * y⁻¹ = (y * m * y⁻¹) * (y * b * y⁻¹) := by group
      _ = b * m := by rw [← hbdef, hyb]
      _ = b * m * e * e := (hc.mul_centralElt_mul_centralElt _).symm
      _ = m * b * e := by rw [← hmb]
      _ = (m * b)⁻¹ := by
        rw [hc.inv_eq_mul_centralElt (hc.mul_self_of_ne (Q.mul_mem hm hb)
          (fun h => hm2 (by rw [eq_inv_of_mul_eq_one_right h, hc.inv_eq_mul_centralElt hmm]))
          (fun h => hm1 (by
            calc b = m⁻¹ * (m * b) := by group
              _ = m := by
                rw [h, hc.inv_eq_mul_centralElt hmm, hc.mul_centralElt_mul_centralElt])))]
  · intro w hw hfix
    rcases hc.enum hm hb hw hmm hbb hm1 hm2 with h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · subst h
      rcases hfix with h' | h'
      · exact absurd h' hm1
      · exact absurd h' hm2
    · subst h
      rw [hc.conj_mul_centralElt, ← hbdef] at hfix
      rcases hfix with h' | h'
      · exact absurd (mul_right_cancel h') hm1
      · rw [hc.mul_centralElt_mul_centralElt] at h'
        exact absurd (by rw [hbme, h']) hm2
    · subst h
      rw [hyb] at hfix
      rcases hfix with h' | h'
      · exact absurd h'.symm hm1
      · exact absurd (by rw [h', hc.mul_centralElt_mul_centralElt]) hm2
    · subst h
      rw [hc.conj_mul_centralElt, hyb] at hfix
      rcases hfix with h' | h'
      · exact absurd (mul_right_cancel h').symm hm1
      · rw [hc.mul_centralElt_mul_centralElt] at h'
        exact absurd h'.symm hm2
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

@[expose] def cosetUnion (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hyy : y * y ∈ P₁) :
    Subgroup G where
  carrier := {x | x ∈ P₁ ∨ x * y⁻¹ ∈ P₁}
  one_mem' := Or.inl P₁.one_mem
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (P₁.mul_mem ha hb)
    · exact Or.inr (by rw [mul_assoc]; exact P₁.mul_mem ha hb)
    · refine Or.inr ?_
      rw [show a * b * y⁻¹ = (a * y⁻¹) * (y * b * y⁻¹) by group]
      exact P₁.mul_mem ha (hc.normal_right y hyT b hb)
    · refine Or.inl ?_
      rw [show a * b = (a * y⁻¹) * (y * (b * y⁻¹) * y⁻¹) * (y * y) by group]
      exact P₁.mul_mem (P₁.mul_mem ha (hc.normal_right y hyT _ hb)) hyy
  inv_mem' := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl (P₁.inv_mem ha)
    · refine Or.inr ?_
      rw [show a⁻¹ * y⁻¹ = (y * (a * y⁻¹) * y⁻¹ * (y * y))⁻¹ by group]
      exact P₁.inv_mem (P₁.mul_mem (hc.normal_right y hyT _ ha) hyy)

theorem mem_sup_zpowers_iff (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hyy : y * y ∈ P₁) {x : G} :
    x ∈ P₁ ⊔ Subgroup.zpowers y ↔ x ∈ P₁ ∨ x * y⁻¹ ∈ P₁ := by
  constructor
  · intro hx
    have hle : P₁ ⊔ Subgroup.zpowers y ≤ hc.cosetUnion hyT hyy :=
      _root_.sup_le (fun p hp => Or.inl hp) (Subgroup.zpowers_le.mpr (Or.inr (by
        rw [mul_inv_cancel]
        exact P₁.one_mem)))
    exact hle hx
  · rintro (hx | hx)
    · exact Subgroup.mem_sup_left hx
    · rw [show x = x * y⁻¹ * y by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))

theorem sup_zpowers_le (hc : PartC T Q P₁ e u) (hyT : y ∈ T) :
    P₁ ⊔ Subgroup.zpowers y ≤ T :=
  _root_.sup_le hc.right_le (Subgroup.zpowers_le.mpr hyT)

theorem mem_sup_of_mul_inv_mem {x : G} (hx : x * y⁻¹ ∈ P₁) (hxQ : x ∈ Q ⊔ P₁) :
    y ∈ Q ⊔ P₁ := by
  rw [show y = (x * y⁻¹)⁻¹ * x by group]
  exact (Q ⊔ P₁).mul_mem ((Q ⊔ P₁).inv_mem (Subgroup.mem_sup_right hx)) hxQ

theorem eq_of_mem_sup_zpowers (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁)
    (hyy : y * y ∈ P₁) {x : G} (hx : x ∈ P₁ ⊔ Subgroup.zpowers y) (hx2 : orderOf x = 2) :
    x = e := by
  rcases (hc.mem_sup_zpowers_iff hyT hyy).mp hx with h | h
  · exact hc.unique x h hx2
  · exact absurd (mem_sup_of_mul_inv_mem h
      (hc.involution_mem x (hc.sup_zpowers_le hyT hx) hx2)) hy

theorem mem_inf_sup_zpowers (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁)
    (hyy : y * y ∈ P₁) {x : G} (hxQ : x ∈ Q) (hx : x ∈ P₁ ⊔ Subgroup.zpowers y) :
    x = 1 ∨ x = e := by
  rcases (hc.mem_sup_zpowers_iff hyT hyy).mp hx with h | h
  · exact hc.mem_inf x hxQ h
  · exact absurd (mem_sup_of_mul_inv_mem h (Subgroup.mem_sup_left hxQ)) hy

theorem sup_zpowers_sup_eq (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁) :
    (P₁ ⊔ Subgroup.zpowers y) ⊔ Q = T := by
  refine le_antisymm (_root_.sup_le (hc.sup_zpowers_le hyT) hc.left_le) fun t htT => ?_
  have hQP : Q ⊔ P₁ ≤ (P₁ ⊔ Subgroup.zpowers y) ⊔ Q :=
    _root_.sup_le le_sup_right (le_sup_left.trans' le_sup_left)
  by_cases ht : t ∈ Q ⊔ P₁
  · exact hQP ht
  · rw [show t = y * (y⁻¹ * t) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right
      (Subgroup.mem_zpowers y))) (hQP (hc.inv_mul_mem y hyT t htT hy ht))

theorem card_sup_zpowers [Finite G] (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁)
    (hyy : y * y ∈ P₁) :
    Nat.card (P₁ ⊔ Subgroup.zpowers y : Subgroup G) = 2 * Nat.card P₁ := by
  set P := P₁ ⊔ Subgroup.zpowers y with hP
  have hle : P₁ ≤ P := le_sup_left
  have hyP : y ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hindex : (P₁.subgroupOf P).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨y, hyP⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : G) ∈ P₁
    · refine Or.inr ⟨hb, fun h => hy (Subgroup.mem_sup_right ?_)⟩
      rw [show y = (b : G)⁻¹ * (b * y) by group]
      exact P₁.mul_mem (P₁.inv_mem hb) h
    · refine Or.inl ⟨?_, hb⟩
      have h := ((hc.mem_sup_zpowers_iff hyT hyy).mp b.2).resolve_left hb
      rw [show (b : G) * y = b * y⁻¹ * (y * y) by group]
      exact P₁.mul_mem h hyy
  have h := Subgroup.card_mul_index (P₁.subgroupOf P)
  rw [hindex, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
  rw [← h, mul_comm]

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
