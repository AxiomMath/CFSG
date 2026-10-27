
module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutionsBase
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutionsBase

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificate

public section

namespace CFSG.ComponentClassification.PSL3Four

open CFSG.PSL3Four CFSG.PSL3Four.Native

theorem enumerates_S : Enumerates S enumS.tabs.toList :=
  enumerates_closure gensS_cover gensS_tabs certFacts.okS

theorem enumerates_R : Enumerates R enumR.tabs.toList :=
  enumerates_closure gTabs_cover gTabs_tabs certFacts.okR

theorem card_S : Nat.card S = 20160 := by
  rw [enumerates_S.card, Array.length_toList, certFacts.sizeS]

theorem card_R : Nat.card R = 241920 := by
  rw [enumerates_R.card, Array.length_toList, certFacts.sizeR]

theorem R_le_normalizer : R ≤ Subgroup.normalizer (S : Set (Equiv.Perm (Fin 42))) := by
  rw [R, Subgroup.closure_le]
  intro a ha
  obtain ⟨j, hj, hrep⟩ := gTabs_cover a ha
  have key : ∀ s ∈ ({g₁, g₂, g₃} : Set (Equiv.Perm (Fin 42))),
      a * s * a⁻¹ ∈ S ∧ a⁻¹ * s * a ∈ S := by
    intro s hs
    obtain ⟨i, hi, hsrep⟩ := gensS_cover s hs
    exact conj_mem_of_normalOK enumerates_S certFacts.normal hj hi hrep hsrep
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_closure fun s hs => (key s hs).1
  · intro hh
    have := conj_mem_closure (a := a⁻¹) (fun s hs => by rw [inv_inv]; exact (key s hs).2) hh
    rwa [show a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h by group] at this

theorem S_normal : (S.subgroupOf R).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer S_le_R).2 R_le_normalizer

theorem conj_mem_S {c x : Equiv.Perm (Fin 42)} (hc : c ∈ R) (hx : x ∈ S) : c * x * c⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.1 (R_le_normalizer hc) x).1 hx

theorem conj_mem_S' {c x : Equiv.Perm (Fin 42)} (hc : c ∈ R) (hx : c * x * c⁻¹ ∈ S) : x ∈ S :=
  (Subgroup.mem_normalizer_iff.1 (R_le_normalizer hc) x).2 hx

theorem centralizer_S_inf_R : Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hc, hR⟩
  rw [Subgroup.mem_bot]
  apply eq_one_of_centralOK enumerates_R certFacts.central hR
  intro i hi
  obtain ⟨a, ha, hrep⟩ := gensS_tabs i hi
  exact ⟨a, hrep, ((Subgroup.mem_centralizer_iff.1 hc) a (Subgroup.subset_closure ha)).symm⟩

theorem not_mem_S_r₂ : r₂ ∉ S := not_mem_of_notInOK enumerates_S certFacts.notS₂ tabRep_r₂

theorem not_mem_S_r₃ : r₃ ∉ S := not_mem_of_notInOK enumerates_S certFacts.notS₃ tabRep_r₃

theorem not_mem_S_r₄ : r₄ ∉ S := not_mem_of_notInOK enumerates_S certFacts.notS₄ tabRep_r₄

theorem conjClass₁ : (∀ y : R, IsConj y r₁R ↔ ∃ t ∈ (orbitR r₁T).tabs.toList,
    TabRep t (y : Equiv.Perm (Fin 42))) ∧ Nat.card (ConjClasses.mk r₁R).carrier = 315 := by
  obtain ⟨hs, hc, hn⟩ := conj_orbit gTabs_cover gTabs_tabs tabRep_r₁ certFacts.orbit₁
  obtain ⟨h1, h2⟩ := conjClass_of_tabs (x := r₁R) hs hc hn
  rw [Array.length_toList, certFacts.size₁] at h2
  exact ⟨h1, h2⟩

theorem conjClass₂ : (∀ y : R, IsConj y r₂R ↔ ∃ t ∈ (orbitR r₂T).tabs.toList,
    TabRep t (y : Equiv.Perm (Fin 42))) ∧ Nat.card (ConjClasses.mk r₂R).carrier = 360 := by
  obtain ⟨hs, hc, hn⟩ := conj_orbit gTabs_cover gTabs_tabs tabRep_r₂ certFacts.orbit₂
  obtain ⟨h1, h2⟩ := conjClass_of_tabs (x := r₂R) hs hc hn
  rw [Array.length_toList, certFacts.size₂] at h2
  exact ⟨h1, h2⟩

theorem conjClass₃ : (∀ y : R, IsConj y r₃R ↔ ∃ t ∈ (orbitR r₃T).tabs.toList,
    TabRep t (y : Equiv.Perm (Fin 42))) ∧ Nat.card (ConjClasses.mk r₃R).carrier = 1008 := by
  obtain ⟨hs, hc, hn⟩ := conj_orbit gTabs_cover gTabs_tabs tabRep_r₃ certFacts.orbit₃
  obtain ⟨h1, h2⟩ := conjClass_of_tabs (x := r₃R) hs hc hn
  rw [Array.length_toList, certFacts.size₃] at h2
  exact ⟨h1, h2⟩

theorem conjClass₄ : (∀ y : R, IsConj y r₄R ↔ ∃ t ∈ (orbitR r₄T).tabs.toList,
    TabRep t (y : Equiv.Perm (Fin 42))) ∧ Nat.card (ConjClasses.mk r₄R).carrier = 280 := by
  obtain ⟨hs, hc, hn⟩ := conj_orbit gTabs_cover gTabs_tabs tabRep_r₄ certFacts.orbit₄
  obtain ⟨h1, h2⟩ := conjClass_of_tabs (x := r₄R) hs hc hn
  rw [Array.length_toList, certFacts.size₄] at h2
  exact ⟨h1, h2⟩

theorem notIn_orbit {i j : ℕ} (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    notInOK (#[(orbitR r₁T).tabs, (orbitR r₂T).tabs, (orbitR r₃T).tabs,
      (orbitR r₄T).tabs])[i]! rTabs[j]! = true := by
  have h := certFacts.disjoint
  rw [allBelow_eq_true] at h
  have h' := h i hi
  rw [allBelow_eq_true] at h'
  have h'' := h' j hj
  simp only [Bool.or_eq_true, beq_iff_eq] at h''
  exact h''.resolve_left hij

theorem not_isConj₁₂ : ¬ IsConj r₁R r₂R := fun h =>
  not_isConj_of_notIn conjClass₂.1
    (notInOK_spec (notIn_orbit (i := 1) (j := 0) (by norm_num) (by norm_num) (by norm_num))
      rTabs_rep.1) h

theorem not_isConj₁₃ : ¬ IsConj r₁R r₃R := fun h =>
  not_isConj_of_notIn conjClass₃.1
    (notInOK_spec (notIn_orbit (i := 2) (j := 0) (by norm_num) (by norm_num) (by norm_num))
      rTabs_rep.1) h

theorem not_isConj₁₄ : ¬ IsConj r₁R r₄R := fun h =>
  not_isConj_of_notIn conjClass₄.1
    (notInOK_spec (notIn_orbit (i := 3) (j := 0) (by norm_num) (by norm_num) (by norm_num))
      rTabs_rep.1) h

theorem not_isConj₂₃ : ¬ IsConj r₂R r₃R := fun h =>
  not_isConj_of_notIn conjClass₃.1
    (notInOK_spec (notIn_orbit (i := 2) (j := 1) (by norm_num) (by norm_num) (by norm_num))
      rTabs_rep.2.1) h

theorem not_isConj₂₄ : ¬ IsConj r₂R r₄R := fun h =>
  not_isConj_of_notIn conjClass₄.1
    (notInOK_spec (notIn_orbit (i := 3) (j := 1) (by norm_num) (by norm_num) (by norm_num))
      rTabs_rep.2.1) h

theorem not_isConj₃₄ : ¬ IsConj r₃R r₄R := fun h =>
  not_isConj_of_notIn conjClass₄.1
    (notInOK_spec (notIn_orbit (i := 3) (j := 2) (by norm_num) (by norm_num) (by norm_num))
      rTabs_rep.2.2.1) h

theorem involution_rTabs {i : ℕ} (hi : i < 4) : comp 42 rTabs[i]! rTabs[i]! = idTab 42 ∧
    rTabs[i]! ≠ idTab 42 := by
  have h := certFacts.involution
  rw [allBelow_eq_true] at h
  have := h i hi
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at this
  exact this

theorem orderOf_r₁R : orderOf r₁R = 2 :=
  orderOf_eq_two_of_tab tabRep_r₁ (involution_rTabs (i := 0) (by norm_num)).1
    (involution_rTabs (i := 0) (by norm_num)).2

theorem orderOf_r₂R : orderOf r₂R = 2 :=
  orderOf_eq_two_of_tab tabRep_r₂ (involution_rTabs (i := 1) (by norm_num)).1
    (involution_rTabs (i := 1) (by norm_num)).2

theorem orderOf_r₃R : orderOf r₃R = 2 :=
  orderOf_eq_two_of_tab tabRep_r₃ (involution_rTabs (i := 2) (by norm_num)).1
    (involution_rTabs (i := 2) (by norm_num)).2

theorem orderOf_r₄R : orderOf r₄R = 2 :=
  orderOf_eq_two_of_tab tabRep_r₄ (involution_rTabs (i := 3) (by norm_num)).1
    (involution_rTabs (i := 3) (by norm_num)).2

theorem orderOf_eq_two_iff (x : R) :
    orderOf x = 2 ↔ IsConj x r₁R ∨ IsConj x r₂R ∨ IsConj x r₃R ∨ IsConj x r₄R := by
  constructor
  · intro hx
    have hx1 : (x : Equiv.Perm (Fin 42)) ≠ 1 := by
      intro h
      have : x = 1 := Subtype.ext h
      rw [this, orderOf_one] at hx
      exact absurd hx (by norm_num)
    have hx2 : (x : Equiv.Perm (Fin 42)) * x = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx, pow_two] at this
      exact congrArg Subtype.val this
    obtain ⟨i, hi, t, ht, hr⟩ := exists_of_coverOK enumerates_R certFacts.cover x.2 hx1 hx2
    have hi4 : i < 4 := hi
    interval_cases i
    · exact Or.inl ((conjClass₁.1 x).2 ⟨t, ht, hr⟩)
    · exact Or.inr (Or.inl ((conjClass₂.1 x).2 ⟨t, ht, hr⟩))
    · exact Or.inr (Or.inr (Or.inl ((conjClass₃.1 x).2 ⟨t, ht, hr⟩)))
    · exact Or.inr (Or.inr (Or.inr ((conjClass₄.1 x).2 ⟨t, ht, hr⟩)))
  · rintro (h | h | h | h)
    · rw [orderOf_eq_of_isConj h, orderOf_r₁R]
    · rw [orderOf_eq_of_isConj h, orderOf_r₂R]
    · rw [orderOf_eq_of_isConj h, orderOf_r₃R]
    · rw [orderOf_eq_of_isConj h, orderOf_r₄R]

theorem mem_S_of_isConj₁ {x : R} (h : IsConj x r₁R) : (x : Equiv.Perm (Fin 42)) ∈ S := by
  obtain ⟨c, hc, he⟩ := eq_conj_of_isConj h
  rw [he]
  exact conj_mem_S hc r₁_mem_S

theorem not_mem_S_of_isConj {x r : R} (h : IsConj x r) (hr : (r : Equiv.Perm (Fin 42)) ∉ S) :
    (x : Equiv.Perm (Fin 42)) ∉ S := by
  obtain ⟨c, hc, he⟩ := eq_conj_of_isConj h
  intro hx
  rw [he] at hx
  exact hr (conj_mem_S' hc hx)

theorem enumerates_cent {r : Equiv.Perm (Fin 42)} {rT : Tab} (hr : TabRep rT r) :
    Enumerates (Subgroup.centralizer {r} ⊓ S) (centS rT).toList := by
  have := enumerates_S.filter (fun t => comp 42 t rT == comp 42 rT t)
    (K := Subgroup.centralizer {r}) fun t g ht => by
      rw [(ht.comp hr).beq_iff (hr.comp ht), Subgroup.mem_centralizer_singleton_iff]
  simpa only [centS, centTabs, Array.toList_filter] using this

theorem enumerates_C₁ : Enumerates C₁ (centS r₁T).toList := enumerates_cent tabRep_r₁

theorem enumerates_C₂ : Enumerates C₂ (centS r₂T).toList := enumerates_cent tabRep_r₂

theorem enumerates_C₃ : Enumerates C₃ (centS r₃T).toList := enumerates_cent tabRep_r₃

theorem enumerates_C₄ : Enumerates C₄ (centS r₄T).toList := enumerates_cent tabRep_r₄

theorem card_C₁ : Nat.card C₁ = 64 := by
  rw [enumerates_C₁.card, Array.length_toList, certFacts.cent₁]

theorem card_C₂ : Nat.card C₂ = 168 := by
  rw [enumerates_C₂.card, Array.length_toList, certFacts.cent₂]

theorem card_C₃ : Nat.card C₃ = 60 := by
  rw [enumerates_C₃.card, Array.length_toList, certFacts.cent₃]

theorem card_C₄ : Nat.card C₄ = 72 := by
  rw [enumerates_C₄.card, Array.length_toList, certFacts.cent₄]

theorem classes_C₂ : ∃ e : Fin 6 ≃ ConjClasses C₂,
    (∀ i, Nat.card (e i).carrier = ![1, 21, 42, 56, 24, 24] i) ∧ e 0 = ConjClasses.mk 1 := by
  obtain ⟨e, he, l₀, hl₀, hl₀e⟩ := classes_of_classOK enumerates_C₂ certFacts.class₂
  refine ⟨(finCongr (show 6 = sizes₂.size from rfl)).trans e, fun i => ?_, ?_⟩
  · rw [Equiv.trans_apply, he]
    fin_cases i <;> rfl
  · rw [Equiv.trans_apply, ← hl₀e]
    congr 1
    exact Fin.ext hl₀.symm

theorem classes_C₃ : ∃ e : Fin 5 ≃ ConjClasses C₃,
    (∀ i, Nat.card (e i).carrier = ![1, 15, 20, 12, 12] i) ∧ e 0 = ConjClasses.mk 1 := by
  obtain ⟨e, he, l₀, hl₀, hl₀e⟩ := classes_of_classOK enumerates_C₃ certFacts.class₃
  refine ⟨(finCongr (show 5 = sizes₃.size from rfl)).trans e, fun i => ?_, ?_⟩
  · rw [Equiv.trans_apply, he]
    fin_cases i <;> rfl
  · rw [Equiv.trans_apply, ← hl₀e]
    congr 1
    exact Fin.ext hl₀.symm

theorem isSimpleGroup_C₂ : IsSimpleGroup C₂ := by
  obtain ⟨e, he, he0⟩ := classes_C₂
  refine isSimpleGroup_of_classes e _ he 0 he0 (by rw [card_C₂]; norm_num) ?_
  rw [card_C₂]
  decide

theorem isSimpleGroup_C₃ : IsSimpleGroup C₃ := by
  obtain ⟨e, he, he0⟩ := classes_C₃
  refine isSimpleGroup_of_classes e _ he 0 he0 (by rw [card_C₃]; norm_num) ?_
  rw [card_C₃]
  decide

theorem exists_mul_ne_C₂ : ∃ a b : C₂, a * b ≠ b * a := by
  obtain ⟨e, he, -⟩ := classes_C₂
  exact exists_mul_ne_of_class (e 1) (by rw [he]; decide)

theorem exists_mul_ne_C₃ : ∃ a b : C₃, a * b ≠ b * a := by
  obtain ⟨e, he, -⟩ := classes_C₃
  exact exists_mul_ne_of_class (e 1) (by rw [he]; decide)

theorem enumerates_derived₁ : Enumerates (ambientDerived C₄ 1) derived₁.1.toList :=
  enumerates_commutator enumerates_C₄ certFacts.der₁

theorem enumerates_derived₂ : Enumerates (ambientDerived C₄ 2) derived₂.1.toList :=
  enumerates_commutator enumerates_derived₁ certFacts.der₂

theorem enumerates_derived₃ : Enumerates (ambientDerived C₄ 3) derived₃.1.toList :=
  enumerates_commutator enumerates_derived₂ certFacts.der₃

theorem card_derivedSeries_C₄ :
    Nat.card (derivedSeries C₄ 0) = 72 ∧ Nat.card (derivedSeries C₄ 1) = 18 ∧
      Nat.card (derivedSeries C₄ 2) = 9 ∧ Nat.card (derivedSeries C₄ 3) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [card_derivedSeries]
    exact card_C₄
  · rw [card_derivedSeries, enumerates_derived₁.card, Array.length_toList, certFacts.derSize₁]
  · rw [card_derivedSeries, enumerates_derived₂.card, Array.length_toList, certFacts.derSize₂]
  · rw [card_derivedSeries, enumerates_derived₃.card, Array.length_toList, certFacts.derSize₃]

theorem isSolvable_C₄ : Group.IsSolvable C₄ :=
  (Group.isSolvable_def _).2 ⟨3, Subgroup.eq_bot_of_card_eq _ card_derivedSeries_C₄.2.2.2⟩

theorem isSolvable_C₁ : Group.IsSolvable C₁ := by
  have h : IsPGroup 2 C₁ := IsPGroup.of_card (n := 6) (by rw [card_C₁]; norm_num)
  have := h.isNilpotent
  infer_instance


theorem involution_enumeration :
    Nat.card S = 20160 ∧ Nat.card R = 241920 ∧ S ≤ R ∧ (S.subgroupOf R).Normal ∧
      Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R = ⊥ ∧
      (∀ x : R, orderOf x = 2 ↔ IsConj x r₁R ∨ IsConj x r₂R ∨ IsConj x r₃R ∨ IsConj x r₄R) ∧
      (¬ IsConj r₁R r₂R ∧ ¬ IsConj r₁R r₃R ∧ ¬ IsConj r₁R r₄R ∧ ¬ IsConj r₂R r₃R ∧
        ¬ IsConj r₂R r₄R ∧ ¬ IsConj r₃R r₄R) ∧
      Nat.card (ConjClasses.mk r₁R).carrier = 315 ∧
      Nat.card (ConjClasses.mk r₂R).carrier = 360 ∧
      Nat.card (ConjClasses.mk r₃R).carrier = 1008 ∧
      Nat.card (ConjClasses.mk r₄R).carrier = 280 ∧
      (∀ x : R, IsConj x r₁R → (x : Equiv.Perm (Fin 42)) ∈ S) ∧
      (∀ x : R, IsConj x r₂R ∨ IsConj x r₃R ∨ IsConj x r₄R → (x : Equiv.Perm (Fin 42)) ∉ S) ∧
      Nat.card C₁ = 64 ∧ Nat.card C₂ = 168 ∧ Nat.card C₃ = 60 ∧ Nat.card C₄ = 72 ∧
      (IsSimpleGroup C₂ ∧ ∃ a b : C₂, a * b ≠ b * a) ∧
      (IsSimpleGroup C₃ ∧ ∃ a b : C₃, a * b ≠ b * a) ∧
      (∃ e : Fin 6 ≃ ConjClasses C₂, ∀ i, Nat.card (e i).carrier = ![1, 21, 42, 56, 24, 24] i) ∧
      (∃ e : Fin 5 ≃ ConjClasses C₃, ∀ i, Nat.card (e i).carrier = ![1, 15, 20, 12, 12] i) ∧
      Nat.card (derivedSeries C₄ 0) = 72 ∧ Nat.card (derivedSeries C₄ 1) = 18 ∧
      Nat.card (derivedSeries C₄ 2) = 9 ∧ Nat.card (derivedSeries C₄ 3) = 1 ∧
      Group.IsSolvable C₁ ∧ Group.IsSolvable C₄ := by
  obtain ⟨e₂, he₂, -⟩ := classes_C₂
  obtain ⟨e₃, he₃, -⟩ := classes_C₃
  refine ⟨card_S, card_R, S_le_R, S_normal, centralizer_S_inf_R, orderOf_eq_two_iff,
    ⟨not_isConj₁₂, not_isConj₁₃, not_isConj₁₄, not_isConj₂₃, not_isConj₂₄, not_isConj₃₄⟩,
    conjClass₁.2, conjClass₂.2, conjClass₃.2, conjClass₄.2, fun x => mem_S_of_isConj₁,
    fun x hx => ?_, card_C₁, card_C₂, card_C₃, card_C₄, ⟨isSimpleGroup_C₂, exists_mul_ne_C₂⟩,
    ⟨isSimpleGroup_C₃, exists_mul_ne_C₃⟩, ⟨e₂, he₂⟩, ⟨e₃, he₃⟩, card_derivedSeries_C₄.1,
    card_derivedSeries_C₄.2.1, card_derivedSeries_C₄.2.2.1, card_derivedSeries_C₄.2.2.2,
    isSolvable_C₁, isSolvable_C₄⟩
  rcases hx with hx | hx | hx
  · exact not_mem_S_of_isConj hx not_mem_S_r₂
  · exact not_mem_S_of_isConj hx not_mem_S_r₃
  · exact not_mem_S_of_isConj hx not_mem_S_r₄

end CFSG.ComponentClassification.PSL3Four
