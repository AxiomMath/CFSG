
module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificateBase

public section

namespace CFSG.ComponentClassification.PSL3Four

open CFSG.PSL3Four CFSG.PSL3Four.Native

theorem g₁_mem_S : g₁ ∈ S := Subgroup.subset_closure (by simp)

theorem g₂_mem_S : g₂ ∈ S := Subgroup.subset_closure (by simp)

theorem g₃_mem_S : g₃ ∈ S := Subgroup.subset_closure (by simp)

theorem g₄_mem_R : g₄ ∈ R := Subgroup.subset_closure (by simp)

theorem g₅_mem_R : g₅ ∈ R := Subgroup.subset_closure (by simp)

theorem g₆_mem_R : g₆ ∈ R := Subgroup.subset_closure (by simp)

theorem S_le_R : S ≤ R := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl | rfl <;> simp

theorem conj_mem_closure {G : Type*} [Group G] {A : Set G} {a : G}
    (hA : ∀ s ∈ A, a * s * a⁻¹ ∈ Subgroup.closure A) {h : G} (hh : h ∈ Subgroup.closure A) :
    a * h * a⁻¹ ∈ Subgroup.closure A := by
  induction hh using Subgroup.closure_induction with
  | mem s hs => exact hA s hs
  | one => simp
  | mul x y _ _ hx hy =>
    have := Subgroup.mul_mem _ hx hy
    rwa [show a * x * a⁻¹ * (a * y * a⁻¹) = a * (x * y) * a⁻¹ by group] at this
  | inv x _ hx =>
    have := Subgroup.inv_mem _ hx
    rwa [show (a * x * a⁻¹)⁻¹ = a * x⁻¹ * a⁻¹ by group] at this

theorem r₁_mem_S : r₁ ∈ S :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ g₁_mem_S 2) g₂_mem_S) g₁_mem_S

theorem r₁_mem_R : r₁ ∈ R := S_le_R r₁_mem_S

theorem r₂_mem_R : r₂ ∈ R := g₅_mem_R

theorem r₃_mem_R : r₃ ∈ R := g₆_mem_R

theorem r₄_mem_R : r₄ ∈ R := Subgroup.mul_mem _ g₅_mem_R g₆_mem_R

@[expose] def r₁R : R := ⟨r₁, r₁_mem_R⟩

@[expose] def r₂R : R := ⟨r₂, r₂_mem_R⟩

@[expose] def r₃R : R := ⟨r₃, r₃_mem_R⟩

@[expose] def r₄R : R := ⟨r₄, r₄_mem_R⟩

theorem conjClass_of_tabs {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {x : H} {O : List Tab}
    (hs : ∀ t ∈ O, ∃ c ∈ H, TabRep t (c * (x : Equiv.Perm (Fin n)) * c⁻¹))
    (hc : ∀ c ∈ H, ∃ t ∈ O, TabRep t (c * (x : Equiv.Perm (Fin n)) * c⁻¹)) (hn : O.Nodup) :
    (∀ y : H, IsConj y x ↔ ∃ t ∈ O, TabRep t (y : Equiv.Perm (Fin n))) ∧
      Nat.card (ConjClasses.mk x).carrier = O.length := by
  have hy : ∀ y : H, IsConj y x ↔ ∃ t ∈ O, TabRep t (y : Equiv.Perm (Fin n)) := by
    intro y
    rw [isConj_comm, isConj_iff]
    constructor
    · rintro ⟨c, rfl⟩
      simpa using hc c c.2
    · rintro ⟨t, ht, hr⟩
      obtain ⟨c, hcH, hcr⟩ := hs t ht
      exact ⟨⟨c, hcH⟩, Subtype.ext (by simpa using (hcr.perm_eq hr))⟩
  refine ⟨hy, ?_⟩
  rw [← Nat.card_image_of_injective Subtype.coe_injective]
  apply card_set_of_tabs _ _ hn
  · intro t ht
    obtain ⟨c, hcH, hcr⟩ := hs t ht
    refine ⟨_, ⟨⟨_, H.mul_mem (H.mul_mem hcH x.2) (H.inv_mem hcH)⟩, ?_, rfl⟩, hcr⟩
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_comm,
      isConj_iff]
    exact ⟨⟨c, hcH⟩, rfl⟩
  · rintro _ ⟨y, hyc, rfl⟩
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at hyc
    exact (hy y).1 hyc

theorem not_isConj_of_notIn {x y : R} {O : List Tab}
    (hx : ∀ z : R, IsConj z x ↔ ∃ t ∈ O, TabRep t (z : Equiv.Perm (Fin 42)))
    (hO : ∀ t ∈ O, ¬ TabRep t (y : Equiv.Perm (Fin 42))) : ¬ IsConj y x := by
  intro h
  obtain ⟨t, ht, hr⟩ := (hx y).1 h
  exact hO t ht hr

theorem rTabs_rep : TabRep rTabs[0]! r₁ ∧ TabRep rTabs[1]! r₂ ∧ TabRep rTabs[2]! r₃ ∧
    TabRep rTabs[3]! r₄ :=
  ⟨tabRep_r₁, tabRep_r₂, tabRep_r₃, tabRep_r₄⟩

theorem orderOf_eq_two_of_tab {x : R} {xT : Tab} (hx : TabRep xT (x : Equiv.Perm (Fin 42)))
    (h2 : comp 42 xT xT = idTab 42) (h1 : xT ≠ idTab 42) : orderOf x = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    rw [pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    exact ((hx.comp hx).eq_iff TabRep.idTab).1 h2
  · intro hx1
    apply h1
    rw [hx1] at hx
    exact (hx.eq_iff TabRep.idTab).2 rfl

theorem orderOf_eq_of_isConj {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := h
  exact SemiconjBy.orderOf_eq (c : G) hc

theorem eq_conj_of_isConj {x r : R} (h : IsConj x r) :
    ∃ c ∈ R, (x : Equiv.Perm (Fin 42)) = c * r * c⁻¹ := by
  rw [isConj_comm, isConj_iff] at h
  obtain ⟨c, rfl⟩ := h
  exact ⟨c, c.2, rfl⟩

theorem exists_mul_ne_of_class {G : Type*} [Group G] (c : ConjClasses G)
    (hc : Nat.card c.carrier ≠ 1) : ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  apply hc
  have hx : (ConjClasses.mk x).carrier = {x} := by
    ext y
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
      Set.mem_singleton_iff, isConj_comm, isConj_iff]
    constructor
    · rintro ⟨d, hd⟩
      rw [← hd, h d x, mul_inv_cancel_right]
    · rintro rfl
      exact ⟨1, by group⟩
  rw [hx, Nat.card_unique]

end CFSG.ComponentClassification.PSL3Four
