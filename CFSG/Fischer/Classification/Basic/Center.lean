module

public import CFSG.Fischer.Uniq.Graph

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer
open scoped commutatorElement

variable {X : Type} [Group X] {E : Set X}

section Simple

theorem commutator_le_of_normal (hZ : Subgroup.center X = ⊥)
    (hs : IsSimpleGroup (commutator X)) {N : Subgroup X} [N.Normal] (hN : N ≠ ⊥) :
    commutator X ≤ N := by
  rcases hs.eq_bot_or_eq_top_of_normal (N.subgroupOf (commutator X)) with h | h
  · exfalso
    apply hN
    rw [Subgroup.subgroupOf_eq_bot] at h
    have hc : ⁅(⊤ : Subgroup X), N⁆ = ⊥ := by
      refine eq_bot_iff.2 fun g hg => ?_
      have h1 : g ∈ N := Subgroup.commutator_le_right ⊤ N hg
      have h2 : g ∈ commutator X := by
        rw [commutator_def]
        exact Subgroup.commutator_mono le_top le_top hg
      exact (Subgroup.disjoint_def.1 h) h1 h2
    rw [Subgroup.commutator_top_left_eq_bot_iff_le_center, hZ] at hc
    exact eq_bot_iff.2 hc
  · exact Subgroup.subgroupOf_eq_top.1 h

end Simple

section Commutator

theorem Pair.mul_inv_mem_commutator (hP : Pair X E) {e f : X} (he : e ∈ E) (hf : f ∈ E) :
    f * e⁻¹ ∈ commutator X := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (Pair.isConj hP he hf)
  rw [← hc, commutator_def, ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top c) (Subgroup.mem_top e)

theorem Pair.top_eq_zpowers_of_forall (hP : Pair X E) {N : Subgroup X} [N.Normal]
    (h : ∀ e ∈ E, ∀ f ∈ E, f * e⁻¹ ∈ N) {e : X} (he : e ∈ E) :
    (⊤ : Subgroup (X ⧸ N)) = Subgroup.zpowers (QuotientGroup.mk e : X ⧸ N) := by
  refine le_antisymm ?_ le_top
  rw [← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), ← Pair.closure_eq hP,
    MonoidHom.map_closure, Subgroup.zpowers_eq_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨f, hf, rfl⟩
  rw [Set.mem_singleton_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
  exact h e he f hf

theorem Pair.index_le_two_of_forall (hP : Pair X E) {N : Subgroup X} [N.Normal]
    (h : ∀ e ∈ E, ∀ f ∈ E, f * e⁻¹ ∈ N) : N.index ≤ 2 := by
  obtain ⟨e, he⟩ := Pair.nonempty hP
  rw [Subgroup.index_eq_card, ← Subgroup.card_top, Pair.top_eq_zpowers_of_forall hP h he,
    Nat.card_zpowers]
  refine orderOf_le_of_pow_eq_one two_pos ?_
  rw [← QuotientGroup.mk_pow, sq, Pair.mul_self hP he, QuotientGroup.mk_one]

theorem Pair.commutator_le_of_forall (hP : Pair X E) {N : Subgroup X} [N.Normal]
    (h : ∀ e ∈ E, ∀ f ∈ E, f * e⁻¹ ∈ N) : commutator X ≤ N := by
  obtain ⟨e, he⟩ := Pair.nonempty hP
  have htop := Pair.top_eq_zpowers_of_forall hP h he
  rw [commutator_def, Subgroup.commutator_le]
  have hcomm : ∀ u v : X ⧸ N, u * v = v * u := by
    intro u v
    have hu : u ∈ Subgroup.zpowers (QuotientGroup.mk e : X ⧸ N) := htop ▸ Subgroup.mem_top u
    have hv : v ∈ Subgroup.zpowers (QuotientGroup.mk e : X ⧸ N) := htop ▸ Subgroup.mem_top v
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact ((Commute.refl _).zpow_zpow i j).eq
  intro a _ b _
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact hcomm _ _

theorem Pair.index_commutator_le_two (hP : Pair X E) : (commutator X).index ≤ 2 :=
  Pair.index_le_two_of_forall hP fun _ he _ hf => Pair.mul_inv_mem_commutator hP he hf

theorem Pair.exists_mem_commutator_conj (hP : Pair X E) {d e : X} (hd : d ∈ E) (he : e ∈ E) :
    ∃ k ∈ commutator X, k * d * k⁻¹ = e := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd he)
  have htop := Pair.top_eq_zpowers_of_forall hP
    (fun _ ha _ hb => Pair.mul_inv_mem_commutator hP ha hb) hd
  have hg : (QuotientGroup.mk g : X ⧸ commutator X) ∈
      Subgroup.zpowers (QuotientGroup.mk d : X ⧸ commutator X) := htop ▸ Subgroup.mem_top _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hg
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hn
  refine ⟨g * d ^ (-n), ?_, by group⟩
  have := (inferInstance : (commutator X).Normal).conj_mem _ hn (d ^ n)
  rwa [show d ^ n * ((d ^ n)⁻¹ * g) * (d ^ n)⁻¹ = g * d ^ (-n) by group] at this

end Commutator

section Center

theorem Pair.exists_not_commute (hP : Pair X E) (hZ : Subgroup.center X = ⊥) :
    ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a := by
  by_contra! h
  obtain ⟨d, hd⟩ := Pair.nonempty hP
  have hc : d ∈ Subgroup.center X := (Pair.mem_center_iff hP).2 fun e he => h e he d hd
  rw [hZ, Subgroup.mem_bot] at hc
  exact Pair.ne_one hP hd hc

theorem Pair.eq_of_mul_mem_center (hP : Pair X E) {d f : X} (hd : d ∈ E) (hf : f ∈ E)
    (hz : d * f ∈ Subgroup.center X) (hnc : ∃ e ∈ E, d * e ≠ e * d) : d = f := by
  obtain ⟨e, he, hde⟩ := hnc
  set w := d * f with hw
  have hwc : ∀ g : X, g * w = w * g := fun g => Subgroup.mem_center_iff.1 hz g
  have hfw : f = d * w := by rw [hw, ← mul_assoc, Pair.mul_self hP hd, one_mul]
  have hef : e * f ≠ f * e := by
    intro h
    apply hde
    have h' : e * d * w = d * e * w := by
      calc e * d * w = e * f := by rw [hfw, mul_assoc]
        _ = f * e := h
        _ = d * (w * e) := by rw [hfw, mul_assoc]
        _ = d * e * w := by rw [← hwc e, mul_assoc]
    exact (mul_right_cancel h').symm
  have h3 : (e * f) ^ 3 = 1 := by
    rw [← Pair.orderOf_mul_eq_three hP he hf hef, pow_orderOf_eq_one]
  have h3' : (e * d) ^ 3 = 1 := by
    rw [← Pair.orderOf_mul_eq_three hP he hd fun h => hde h.symm, pow_orderOf_eq_one]
  have hw3 : w ^ 3 = 1 := by
    have hc : Commute (e * d) w := hwc (e * d)
    rw [show e * f = e * d * w by rw [hfw, mul_assoc], hc.mul_pow, h3', one_mul] at h3
    exact h3
  have hw2 : w ^ 2 = 1 := by
    have hdf : d * f = f * d := by
      have h : d * w = w * d := hwc d
      rw [hw, ← mul_assoc, Pair.mul_self hP hd, one_mul] at h
      exact (Pair.mul_mul_eq_self_iff hP hd f).1 h.symm
    rw [sq, hw]
    calc d * f * (d * f) = d * (f * d) * f := by simp only [mul_assoc]
      _ = d * d * (f * f) := by rw [← hdf]; simp only [mul_assoc]
      _ = 1 := by rw [Pair.mul_self hP hd, Pair.mul_self hP hf, one_mul]
  have hw1 : w = 1 := by
    calc w = w ^ 3 * (w ^ 2)⁻¹ := by group
      _ = 1 := by rw [hw3, hw2, inv_one, one_mul]
  rw [← mul_left_cancel_iff (a := d), ← hw, hw1, Pair.mul_self hP hd]

theorem Pair.center_quotient_center_eq_bot (hP : Pair X E) :
    Subgroup.center (X ⧸ Subgroup.center X) = ⊥ := by
  refine eq_bot_iff.2 fun q hq => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  refine (Pair.mem_center_iff hP).2 fun d hd => ?_
  have hc : ⁅g, d⁆ ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 hq _).symm
  rw [commutatorElement_def, Pair.inv_eq hP hd] at hc
  have hconj : g * d * g⁻¹ = d := by
    by_cases hnc : ∃ e ∈ E, d * e ≠ e * d
    · have hdf : d * (g * d * g⁻¹) ∈ Subgroup.center X :=
        (inferInstance : (Subgroup.center X).Normal).mem_comm hc
      exact (Pair.eq_of_mul_mem_center hP hd (Pair.conj_mem hP hd g) hdf hnc).symm
    · push Not at hnc
      have hdZ : d ∈ Subgroup.center X := (Pair.mem_center_iff hP).2 fun e he => (hnc e he).symm
      rw [Subgroup.mem_center_iff.1 hdZ g, mul_inv_cancel_right]
  rw [mul_inv_eq_iff_eq_mul] at hconj
  exact hconj.symm

end Center

end CFSG.Fischer.Classification
