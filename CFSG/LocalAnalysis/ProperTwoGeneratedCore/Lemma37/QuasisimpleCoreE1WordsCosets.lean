module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1WordsSubLabels

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem e1PQ_cases : ∀ v : Fin 64, e1PQ v →
    v ≠ 0 ∧ (v.val % 16 = 0 ∨ (v.val < 16 ∧ v.val % 4 = 0)) := by decide

theorem e1PQ_of_cases : ∀ v : Fin 64, v ≠ 0 →
    (v.val % 16 = 0 ∨ (v.val < 16 ∧ v.val % 4 = 0)) → e1PQ v := by decide

@[expose] def e1U (gf : Bool) (v : Fin 64) : Prop :=
  if gf then v.val / 2 % 2 = 0 else v.val / 2 % 2 = v.val % 2

instance (gf : Bool) : DecidablePred (e1U gf) := fun v => by unfold e1U; infer_instance

theorem e1U_zero : ∀ gf : Bool, e1U gf 0 := by decide

theorem e1U_mul : ∀ (gf : Bool) (v w : Fin 64), e1U gf v → e1U gf w → e1U gf (c3Mul v w) := by
  decide +kernel

theorem e1U_facts : ∀ gf : Bool, (Finset.univ.filter (e1U gf)).card = 32 ∧ ¬ e1U gf 2 ∧
    e1U gf (if gf then 1 else 3) := by decide

theorem e1PQ_of_e1U : ∀ (gf : Bool) (v : Fin 64), e1U gf v → c3Mul v v = 0 → v ≠ 0 →
    e1Gen gf (!gf) v = false → e1PQ v := by
  decide +kernel

theorem e1E_conj_classes : ∀ t : Fin 64, e1E t → t ≠ 0 → t ≠ 40 →
    (∃ s : Fin 64, c3Conj s 32 = t) ∨ (∃ s : Fin 64, c3Conj s 2 = t) := by decide +kernel

theorem c3Conj_ne_two : ∀ s : Fin 64, c3Conj s 32 ≠ 2 := by decide

variable {G : Type} [Group G] {T Q P₁ S : Subgroup G} {e u y x m : G}

@[expose] noncomputable def e1UBar (Z : Subgroup G) [Z.Normal] (u m y x : G) (gf : Bool) :
    Subgroup (G ⧸ Z) :=
  e1WordSubgroup Z u m y x (e1U gf)

namespace CaseC3BCD

variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z) [Finite G]
include hb

theorem mem_map_right_or_left_of_not_genuine {s : G ⧸ Z}
    (hs : s ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z)) (hs1 : s ≠ 1) (hgen : ¬ CaseC3.Genuine Z s) :
    s ∈ P₁.map (QuotientGroup.mk' Z) ∨ s ∈ Q.map (QuotientGroup.mk' Z) := by
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word
    (Subgroup.map_mono (hb.partC.sup_le.trans hb.le_top) hs)
  have h4 := hb.caseC3Word_mem_sup_iff.mp hs
  have hv0 : v ≠ 0 := fun h => hs1 (by rw [h, caseC3Word_zero])
  rw [hb.genuine_even_iff (by omega)] at hgen
  rw [hb.caseC3Word_mem_map_right_iff, hb.caseC3Word_mem_map_left_iff]
  exact (e1PQ_cases v ⟨h4, hv0, fun h => hgen (Or.inr h)⟩).2

theorem not_genuine_of_mem_map_right {s : G ⧸ Z} (hs : s ∈ P₁.map (QuotientGroup.mk' Z))
    (hs1 : s ≠ 1) : ¬ CaseC3.Genuine Z s := by
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word
    (Subgroup.map_mono ((hb.partC.right_le).trans hb.le_top) hs)
  have h16 := hb.caseC3Word_mem_map_right_iff.mp hs
  have hv0 : v ≠ 0 := fun h => hs1 (by rw [h, caseC3Word_zero])
  rw [hb.genuine_even_iff (by omega)]
  exact fun h => (e1PQ_of_cases v hv0 (Or.inl h16)).2.2 (h.resolve_left hv0)

theorem not_genuine_of_mem_map_left {s : G ⧸ Z} (hs : s ∈ Q.map (QuotientGroup.mk' Z))
    (hs1 : s ≠ 1) : ¬ CaseC3.Genuine Z s := by
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word
    (Subgroup.map_mono ((hb.partC.left_le).trans hb.le_top) hs)
  have h16 := hb.caseC3Word_mem_map_left_iff.mp hs
  have hv0 : v ≠ 0 := fun h => hs1 (by rw [h, caseC3Word_zero])
  rw [hb.genuine_even_iff (by omega)]
  exact fun h => (e1PQ_of_cases v hv0 (Or.inr h16)).2.2 (h.resolve_left hv0)

theorem caseC3Word_mem_e1UBar_iff {gf : Bool} {v : Fin 64} :
    caseC3Word Z u m y x v ∈ e1UBar Z u m y x gf ↔ e1U gf v :=
  hb.caseC3Word_mem_e1WordSubgroup_iff (e1U_zero gf) (e1U_mul gf)

theorem mem_e1UBar_iff {gf : Bool} {s : G ⧸ Z} :
    s ∈ e1UBar Z u m y x gf ↔ ∃ v, e1U gf v ∧ caseC3Word Z u m y x v = s :=
  hb.mem_e1WordSubgroup_iff (e1U_zero gf) (e1U_mul gf)

theorem e1UBar_le (gf : Bool) : e1UBar Z u m y x gf ≤ S.map (QuotientGroup.mk' Z) :=
  hb.e1WordSubgroup_le _

theorem relIndex_e1UBar (gf : Bool) :
    (e1UBar Z u m y x gf).relIndex (S.map (QuotientGroup.mk' Z)) = 2 := by
  have h := Subgroup.relIndex_mul_card (e1UBar Z u m y x gf) (S.map (QuotientGroup.mk' Z))
  rw [inf_eq_left.mpr (hb.e1UBar_le gf), hb.card_map_top,
    show Nat.card (e1UBar Z u m y x gf) = 32 from
      (hb.card_e1WordSubgroup (e1U_zero gf) (e1U_mul gf)).trans (e1U_facts gf).1] at h
  omega

theorem two_not_mem_e1UBar (gf : Bool) : (y : G ⧸ Z) ∉ e1UBar Z u m y x gf := by
  rw [← caseC3Word_two (Z := Z) (u := u) (m := m) (x := x), hb.caseC3Word_mem_e1UBar_iff]
  exact (e1U_facts gf).2.1

theorem rep_mem_e1UBar : (x : G ⧸ Z) ∈ e1UBar Z u m y x true ∧
    (y : G ⧸ Z) * (x : G ⧸ Z) ∈ e1UBar Z u m y x false := by
  rw [← caseC3Word_three (Z := Z) (u := u) (m := m),
    ← caseC3Word_one (Z := Z) (u := u) (m := m) (y := y), hb.caseC3Word_mem_e1UBar_iff,
    hb.caseC3Word_mem_e1UBar_iff]
  exact ⟨(e1U_facts true).2.2, (e1U_facts false).2.2⟩

theorem mem_map_of_mem_e1UBar_of_typeC {gf gef : Bool} (hgg : (gf && gef) = false)
    (hor : (gf || gef) = true)
    (hlab : ∀ v, CaseC3.Genuine Z (caseC3Word Z u m y x v) ↔ e1Gen gf gef v = true)
    {s : G ⧸ Z} (hs : s ∈ e1UBar Z u m y x gf) (hss : s * s = 1) (hs1 : s ≠ 1)
    (hgen : ¬ CaseC3.Genuine Z s) :
    s ∈ P₁.map (QuotientGroup.mk' Z) ∨ s ∈ Q.map (QuotientGroup.mk' Z) := by
  obtain rfl : gef = !gf := by
    revert hgg hor
    cases gf <;> cases gef <;> simp
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1UBar_iff.mp hs
  have hv0 : v ≠ 0 := fun h => hs1 (by rw [h, caseC3Word_zero])
  rw [hlab, Bool.not_eq_true] at hgen
  rw [hb.caseC3Word_mem_map_right_iff, hb.caseC3Word_mem_map_left_iff]
  exact (e1PQ_cases v (e1PQ_of_e1U gf v hv
    (hb.caseC3Word_mul_self_eq_one_iff.mp hss) hv0 hgen)).2

theorem exists_conj_of_mem_e1EBar {t : G ⧸ Z} (ht : t ∈ e1EBar Z u m y x) (ht1 : t ≠ 1)
    (htz : t ≠ caseC3Word Z u m y x 40) :
    (∃ s ∈ S.map (QuotientGroup.mk' Z), s * (u : G ⧸ Z) * s⁻¹ = t) ∨
      ∃ s ∈ S.map (QuotientGroup.mk' Z), s * (y : G ⧸ Z) * s⁻¹ = t := by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1EBar_iff.mp ht
  have hv0 : v ≠ 0 := fun h => ht1 (by rw [h, caseC3Word_zero])
  have hv40 : v ≠ 40 := fun h => htz (by rw [h])
  rcases e1E_conj_classes v hv hv0 hv40 with ⟨w, hw⟩ | ⟨w, hw⟩
  · refine Or.inl ⟨_, hb.caseC3Word_mem w, ?_⟩
    rw [← caseC3Word_thirtytwo (Z := Z) (m := m) (y := y) (x := x), hb.caseC3Word_conj, hw]
  · refine Or.inr ⟨_, hb.caseC3Word_mem w, ?_⟩
    rw [← caseC3Word_two (Z := Z) (u := u) (m := m) (x := x), hb.caseC3Word_conj, hw]

theorem conj_ne_two {s : G ⧸ Z} (hs : s ∈ S.map (QuotientGroup.mk' Z)) :
    s * (u : G ⧸ Z) * s⁻¹ ≠ (y : G ⧸ Z) := by
  obtain ⟨w, rfl⟩ := hb.exists_caseC3Word hs
  rw [← caseC3Word_thirtytwo (Z := Z) (m := m) (y := y) (x := x),
    ← caseC3Word_two (Z := Z) (u := u) (m := m) (x := x), hb.caseC3Word_conj, Ne,
    hb.caseC3Word_inj]
  exact c3Conj_ne_two w

theorem conj_forty_of_normalizes_e1EBar {c : G ⧸ Z}
    (hc : ∀ t ∈ e1EBar Z u m y x, c * t * c⁻¹ ∈ e1EBar Z u m y x) :
    c * caseC3Word Z u m y x 40 * c⁻¹ = caseC3Word Z u m y x 40 := by
  by_contra hne
  have hgen : CaseC3.Genuine Z (c * caseC3Word Z u m y x 40 * c⁻¹) := by
    have h := CaseC3.genuine_conj Z hb.genuine_forty c⁻¹
    rwa [inv_inv] at h
  refine (hb.not_genuine_of_mem_e1EBar (hc _ hb.forty_mem_e1EBar) (fun h1 => ?_) hne).1 hgen
  have h40 : caseC3Word Z u m y x 40 = 1 := by
    rw [show caseC3Word Z u m y x 40 = c⁻¹ * (c * caseC3Word Z u m y x 40 * c⁻¹) * c by group,
      h1]
    group
  exact absurd (hb.caseC3Word_eq_one_iff.mp h40) (by decide)

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
