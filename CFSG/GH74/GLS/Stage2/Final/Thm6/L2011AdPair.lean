module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdLayerP

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

structure PairX (x : X) (K₁ K₂ : Subgroup X) : Prop where
  sq : x * x = 1
  ne_one : x ≠ 1
  mem₁ : x ∈ K₁
  mem₂ : x ∈ K₂
  le₁ : K₁ ≤ centralizer ({x} : Set X)
  le₂ : K₂ ≤ centralizer ({x} : Set X)
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  comp₁ : IsComponent (K₁.subgroupOf (centralizer ({x} : Set X)))
  comp₂ : IsComponent (K₂.subgroupOf (centralizer ({x} : Set X)))
  cent₁ : ∀ u ∈ K₁, (∀ k ∈ K₁, u * k = k * u) → u * u = 1 → u = 1 ∨ u = x
  cent₂ : ∀ u ∈ K₂, (∀ k ∈ K₂, u * k = k * u) → u * u = 1 → u = 1 ∨ u = x
  perf : ∀ M : Subgroup X, M ≤ centralizer ({x} : Set X) → ⁅M, M⁆ = M → M ≤ K₁ ⊔ K₂

omit [Finite X] in
theorem comm_of_commutator_eq_bot {A B : Subgroup X} (h : ⁅A, B⁆ = ⊥) {a b : X} (ha : a ∈ A)
    (hb : b ∈ B) : a * b = b * a := by
  have h1 : ⁅a, b⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

omit [Finite X] in
theorem not_comm_of_isComponent {Q : Subgroup X} (hQ : IsComponent Q) :
    ¬ ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
  intro h
  have hperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.mp hQ.1.1
  have hbot : ⁅Q, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h b hb a ha
  have := isQuasisimple_nontrivial hQ.1
  obtain ⟨⟨q, hq⟩, hne⟩ := exists_ne (1 : ↥Q)
  apply hne
  have h1 : q ∈ ⁅Q, Q⁆ := by rw [hperf]; exact hq
  rw [hbot, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

theorem eq_of_isComponent_of_le {Q Q' : Subgroup X} (hQ : IsComponent Q)
    (hQ' : IsComponent Q') (hle : Q ≤ Q') : Q = Q' := by
  rcases distinct_components_commute hQ hQ' with h | h
  · exact h
  · exfalso
    apply not_comm_of_isComponent hQ
    intro a ha b hb
    exact comm_of_commutator_eq_bot h ha (hle hb)

omit [Finite X] in
theorem comm_of_commutator_subgroupOf_eq_bot {C A B : Subgroup X}
    (h : ⁅A.subgroupOf C, B.subgroupOf C⁆ = ⊥) {a b : X} (haA : a ∈ A) (haC : a ∈ C) (hbB : b ∈ B)
    (hbC : b ∈ C) : a * b = b * a := by
  have h1 := comm_of_commutator_eq_bot h (a := ⟨a, haC⟩) (b := ⟨b, hbC⟩)
    (Subgroup.mem_subgroupOf.mpr haA) (Subgroup.mem_subgroupOf.mpr hbB)
  exact congrArg Subtype.val h1

namespace PairX

variable {x : X} {K₁ K₂ : Subgroup X}

theorem component_eq (h : PairX x K₁ K₂) {Q : Subgroup X} (hQ : IsComponent Q)
    (hQC : Q ≤ centralizer ({x} : Set X)) : Q = K₁ ∨ Q = K₂ := by
  have hperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.mp hQ.1.1
  have hle : Q ≤ K₁ ⊔ K₂ := h.perf Q hQC hperf
  have hQ' : IsComponent (Q.subgroupOf (centralizer ({x} : Set X))) := component_overgroup hQ hQC
  by_contra hcon
  rw [not_or] at hcon
  have hc₁ : ∀ a ∈ Q, ∀ b ∈ K₁, a * b = b * a := by
    rcases distinct_components_commute hQ' h.comp₁ with h' | h'
    · exfalso
      apply hcon.1
      have := Subgroup.subgroupOf_inj.mp h'
      rwa [inf_eq_left.mpr hQC, inf_eq_left.mpr h.le₁] at this
    · intro a ha b hb
      exact comm_of_commutator_subgroupOf_eq_bot h' ha (hQC ha) hb (h.le₁ hb)
  have hc₂ : ∀ a ∈ Q, ∀ b ∈ K₂, a * b = b * a := by
    rcases distinct_components_commute hQ' h.comp₂ with h' | h'
    · exfalso
      apply hcon.2
      have := Subgroup.subgroupOf_inj.mp h'
      rwa [inf_eq_left.mpr hQC, inf_eq_left.mpr h.le₂] at this
    · intro a ha b hb
      exact comm_of_commutator_subgroupOf_eq_bot h' ha (hQC ha) hb (h.le₂ hb)
  apply not_comm_of_isComponent hQ
  intro a ha b hb
  have hsup : K₁ ⊔ K₂ ≤ centralizer ({a} : Set X) := by
    refine sup_le ?_ ?_
    · intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc₁ a ha k hk).symm
    · intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc₂ a ha k hk).symm
  have := hsup (hle hb)
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm


omit [Finite X] in
theorem not_comm₁ (h : PairX x K₁ K₂) : ¬ ∀ a ∈ K₁, ∀ b ∈ K₁, a * b = b * a := by
  intro hc
  apply not_comm_of_isComponent h.comp₁
  rintro ⟨a, haC⟩ ha ⟨b, hbC⟩ hb
  exact Subtype.ext (hc a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb))

omit [Finite X] in
theorem not_comm₂ (h : PairX x K₁ K₂) : ¬ ∀ a ∈ K₂, ∀ b ∈ K₂, a * b = b * a := by
  intro hc
  apply not_comm_of_isComponent h.comp₂
  rintro ⟨a, haC⟩ ha ⟨b, hbC⟩ hb
  exact Subtype.ext (hc a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb))

theorem all_eq_of_same (h : PairX x K₁ K₂) {Q : Subgroup X} (hQ : IsComponent Q) (h₁ : K₁ ≤ Q)
    (h₂ : K₂ ≤ Q) : ∀ Q' : Subgroup X, IsComponent Q' → Q' = Q := by
  intro Q' hQ'
  rcases distinct_components_commute hQ' hQ with h' | h'
  · exact h'
  · have hQ'C : Q' ≤ centralizer ({x} : Set X) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact comm_of_commutator_eq_bot h' ha (h₁ h.mem₁)
    rcases h.component_eq hQ' hQ'C with h'' | h''
    · exact eq_of_isComponent_of_le hQ' hQ (h'' ▸ h₁)
    · exact eq_of_isComponent_of_le hQ' hQ (h'' ▸ h₂)

theorem eq_of_ne (h : PairX x K₁ K₂) {Q₁ Q₂ : Subgroup X} (hQ₁ : IsComponent Q₁)
    (hQ₂ : IsComponent Q₂) (h₁ : K₁ ≤ Q₁) (h₂ : K₂ ≤ Q₂) (hne : Q₁ ≠ Q₂) :
    Q₁ = K₁ ∧ Q₂ = K₂ := by
  have hc : ⁅Q₁, Q₂⁆ = ⊥ := (distinct_components_commute hQ₁ hQ₂).resolve_left hne
  have hQ₁C : Q₁ ≤ centralizer ({x} : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_commutator_eq_bot hc ha (h₂ h.mem₂)
  have hQ₂C : Q₂ ≤ centralizer ({x} : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (comm_of_commutator_eq_bot hc (h₁ h.mem₁) ha).symm
  refine ⟨?_, ?_⟩
  · rcases h.component_eq hQ₁ hQ₁C with e | e
    · exact e
    · exfalso
      apply h.not_comm₁
      intro a ha b hb
      exact h.comm a ha b (e ▸ h₁ hb)
  · rcases h.component_eq hQ₂ hQ₂C with e | e
    · exfalso
      apply h.not_comm₂
      intro a ha b hb
      exact (h.comm b (e ▸ h₂ hb) a ha).symm
    · exact e

end PairX


theorem layer_unique_component {x y : X} {K₁ K₂ K₁' K₂' : Subgroup X} (hx : PairX x K₁ K₂)
    (hy : PairX y K₁' K₂') (hxy : x ≠ y) (hE₁ : K₁ ≤ layer X) (hE₂ : K₂ ≤ layer X)
    (hE₁' : K₁' ≤ layer X) (hE₂' : K₂' ≤ layer X) :
    ∃ Q : Subgroup X, IsComponent Q ∧ K₁ ⊔ K₂ ≤ Q ∧ ∀ Q' : Subgroup X, IsComponent Q' → Q' = Q := by
  obtain ⟨Q₁, hQ₁, h₁⟩ :=
    exists_component_ge_of_component_centralizer (hE₁ hx.mem₁) hE₁ hx.le₁ hx.comp₁
  obtain ⟨Q₂, hQ₂, h₂⟩ :=
    exists_component_ge_of_component_centralizer (hE₁ hx.mem₁) hE₂ hx.le₂ hx.comp₂
  obtain ⟨Q₃, hQ₃, h₃⟩ :=
    exists_component_ge_of_component_centralizer (hE₁' hy.mem₁) hE₁' hy.le₁ hy.comp₁
  obtain ⟨Q₄, hQ₄, h₄⟩ :=
    exists_component_ge_of_component_centralizer (hE₁' hy.mem₁) hE₂' hy.le₂ hy.comp₂
  by_cases h12 : Q₁ = Q₂
  · exact ⟨Q₁, hQ₁, sup_le h₁ (h12 ▸ h₂), hx.all_eq_of_same hQ₁ h₁ (h12 ▸ h₂)⟩
  · exfalso
    obtain ⟨e₁, e₂⟩ := hx.eq_of_ne hQ₁ hQ₂ h₁ h₂ h12
    have hK₁ : IsComponent K₁ := e₁ ▸ hQ₁
    have hK₂ : IsComponent K₂ := e₂ ▸ hQ₂
    by_cases h34 : Q₃ = Q₄
    · have a1 := hy.all_eq_of_same hQ₃ h₃ (h34 ▸ h₄) K₁ hK₁
      have a2 := hy.all_eq_of_same hQ₃ h₃ (h34 ▸ h₄) K₂ hK₂
      apply hx.not_comm₁
      intro a ha b hb
      exact hx.comm a ha b (by rw [a2, ← a1]; exact hb)
    · obtain ⟨e₃, e₄⟩ := hy.eq_of_ne hQ₃ hQ₄ h₃ h₄ h34
      have hK₁' : IsComponent K₁' := e₃ ▸ hQ₃
      have hne₁ : K₁' ≠ K₁ := by
        intro hEq
        have hyK : y ∈ K₁ := hEq ▸ hy.mem₁
        have hcent : ∀ k ∈ K₁, y * k = k * y := by
          intro k hk
          have := hy.le₁ (hEq ▸ hk)
          rw [Subgroup.mem_centralizer_singleton_iff] at this
          exact this.symm
        rcases hx.cent₁ y hyK hcent hy.sq with h0 | h0
        · exact hy.ne_one h0
        · exact hxy h0.symm
      rcases distinct_components_commute hK₁' hK₁ with h' | h'
      · exact hne₁ h'
      · have hK₁'C : K₁' ≤ centralizer ({x} : Set X) := by
          intro a ha
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact comm_of_commutator_eq_bot h' ha hx.mem₁
        rcases hx.component_eq hK₁' hK₁'C with h'' | h''
        · exact hne₁ h''
        · have hyK : y ∈ K₂ := h'' ▸ hy.mem₁
          have hcent : ∀ k ∈ K₂, y * k = k * y := by
            intro k hk
            have := hy.le₁ (h'' ▸ hk)
            rw [Subgroup.mem_centralizer_singleton_iff] at this
            exact this.symm
          rcases hx.cent₂ y hyK hcent hy.sq with h0 | h0
          · exact hy.ne_one h0
          · exact hxy h0.symm

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
