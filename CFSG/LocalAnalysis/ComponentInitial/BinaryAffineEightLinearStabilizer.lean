module

public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Module

section Defs

variable (E : Type*) [AddCommGroup E] [Module (ZMod 2) E]

@[expose] def linearPerms : Subgroup (Equiv.Perm E) where
  carrier := {σ | ∃ A : E ≃ₗ[ZMod 2] E, ∀ v, σ v = A v}
  one_mem' := ⟨LinearEquiv.refl _ _, fun _ => rfl⟩
  mul_mem' := by
    rintro σ τ ⟨A, hσ⟩ ⟨B, hτ⟩
    exact ⟨B.trans A, fun v => by simp [hσ, hτ]⟩
  inv_mem' := by
    rintro σ ⟨A, hσ⟩
    refine ⟨A.symm, fun v => ?_⟩
    rw [← A.symm_apply_apply (σ⁻¹ v), ← hσ]
    exact congrArg A.symm (σ.apply_symm_apply v)

@[expose] def affinePerms : Subgroup (Equiv.Perm E) where
  carrier := {σ | ∃ (a : E) (A : E ≃ₗ[ZMod 2] E), ∀ v, σ v = a + A v}
  one_mem' := ⟨0, LinearEquiv.refl _ _, fun v => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨a, A, hσ⟩ ⟨b, B, hτ⟩
    exact ⟨a + A b, B.trans A, fun v => by simp [hσ, hτ, add_assoc]⟩
  inv_mem' := by
    rintro σ ⟨a, A, hσ⟩
    refine ⟨-A.symm a, A.symm, fun v => ?_⟩
    have h1 : a + A (σ⁻¹ v) = v := by rw [← hσ]; exact σ.apply_symm_apply v
    have h2 : σ⁻¹ v = A.symm (v - a) := by
      rw [eq_comm, LinearEquiv.symm_apply_eq]
      exact (eq_sub_of_add_eq' h1).symm
    rw [h2, map_sub]
    abel

@[expose] def translationPerms : Subgroup (Equiv.Perm E) where
  carrier := {σ | ∃ a : E, ∀ v, σ v = a + v}
  one_mem' := ⟨0, fun v => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨a, hσ⟩ ⟨b, hτ⟩
    exact ⟨a + b, fun v => by simp [hσ, hτ, add_assoc]⟩
  inv_mem' := by
    rintro σ ⟨a, hσ⟩
    refine ⟨-a, fun v => ?_⟩
    have h1 : a + σ⁻¹ v = v := by rw [← hσ]; exact σ.apply_symm_apply v
    rw [eq_sub_of_add_eq' h1]
    abel

end Defs

namespace BinaryAffineEight

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem f2_add_self (v : E) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem f2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem f2_add_right_eq_iff {v w e : E} : v + e = w ↔ v = w + e := by
  constructor
  · rintro rfl
    rw [add_assoc, f2_add_self, add_zero]
  · rintro rfl
    rw [add_assoc, f2_add_self, add_zero]

theorem mem_span_singleton_iff {e v : E} :
    v ∈ Submodule.span (ZMod 2) {e} ↔ v = 0 ∨ v = e := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rcases f2_cases a with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem mem_span_pair_iff {e x v : E} :
    v ∈ Submodule.span (ZMod 2) {e, x} ↔ v = 0 ∨ v = e ∨ v = x ∨ v = e + x := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases f2_cases a with rfl | rfl <;>
      rcases f2_cases b with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

variable [FiniteDimensional (ZMod 2) E]

theorem card_eq_eight (hE : finrank (ZMod 2) E = 3) : Nat.card E = 8 := by
  have : Finite E := Module.finite_of_finite (ZMod 2)
  let := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hE]
  rfl

theorem eight_le_length (hE : finrank (ZMod 2) E = 3) (l : List E) (hl : ∀ v, v ∈ l) :
    8 ≤ l.length := by
  classical
  have : Finite E := Module.finite_of_finite (ZMod 2)
  let := Fintype.ofFinite E
  have h8 : Fintype.card E = 8 := by rw [← Nat.card_eq_fintype_card, card_eq_eight hE]
  calc 8 = (Finset.univ : Finset E).card := h8.symm
    _ ≤ l.toFinset.card := Finset.card_le_card fun v _ => List.mem_toFinset.mpr (hl v)
    _ ≤ l.length := List.toFinset_card_le l

theorem exists_not_mem_span_singleton (hE : finrank (ZMod 2) E = 3) (e : E) :
    ∃ x, x ∉ Submodule.span (ZMod 2) {e} := by
  by_contra h
  have := eight_le_length hE [0, e] fun v => by
    rcases mem_span_singleton_iff.mp (not_not.mp (not_exists.mp h v)) with rfl | rfl <;> simp
  simp at this

theorem exists_not_mem_span_pair (hE : finrank (ZMod 2) E = 3) (e x : E) :
    ∃ y, y ∉ Submodule.span (ZMod 2) {e, x} := by
  by_contra h
  have := eight_le_length hE [0, e, x, e + x] fun v => by
    rcases mem_span_pair_iff.mp (not_not.mp (not_exists.mp h v)) with rfl | rfl | rfl | rfl <;>
      simp
  simp at this

omit [FiniteDimensional (ZMod 2) E] in
theorem linearIndependent_triple {e x y : E} (he : e ≠ 0)
    (hx : x ∉ Submodule.span (ZMod 2) {e}) (hy : y ∉ Submodule.span (ZMod 2) {e, x}) :
    LinearIndependent (ZMod 2) ![y, x, e] := by
  rw [show (![y, x, e] : Fin 3 → E) = Fin.cons y ![x, e] from rfl, linearIndependent_finCons,
    show (![x, e] : Fin 2 → E) = Fin.cons x ![e] from rfl, linearIndependent_finCons]
  refine ⟨⟨linearIndependent_unique_iff.mpr he, ?_⟩, ?_⟩
  · simpa using hx
  · simpa [Set.pair_comm] using hy

omit [FiniteDimensional (ZMod 2) E] in
noncomputable def tripleBasis (hE : finrank (ZMod 2) E = 3) {e x y : E} (he : e ≠ 0)
    (hx : x ∉ Submodule.span (ZMod 2) {e}) (hy : y ∉ Submodule.span (ZMod 2) {e, x}) :
    Basis (Fin 3) (ZMod 2) E :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_triple he hx hy) (by simp [hE])

omit [FiniteDimensional (ZMod 2) E] in
theorem tripleBasis_zero (hE : finrank (ZMod 2) E = 3) {e x y : E} (he : e ≠ 0)
    (hx : x ∉ Submodule.span (ZMod 2) {e}) (hy : y ∉ Submodule.span (ZMod 2) {e, x}) :
    tripleBasis hE he hx hy 0 = y := by
  simp [tripleBasis]

omit [FiniteDimensional (ZMod 2) E] in
theorem tripleBasis_one (hE : finrank (ZMod 2) E = 3) {e x y : E} (he : e ≠ 0)
    (hx : x ∉ Submodule.span (ZMod 2) {e}) (hy : y ∉ Submodule.span (ZMod 2) {e, x}) :
    tripleBasis hE he hx hy 1 = x := by
  simp [tripleBasis]

omit [FiniteDimensional (ZMod 2) E] in
theorem tripleBasis_two (hE : finrank (ZMod 2) E = 3) {e x y : E} (he : e ≠ 0)
    (hx : x ∉ Submodule.span (ZMod 2) {e}) (hy : y ∉ Submodule.span (ZMod 2) {e, x}) :
    tripleBasis hE he hx hy 2 = e := by
  simp [tripleBasis]

omit [FiniteDimensional (ZMod 2) E] in
theorem exists_coords (b : Basis (Fin 3) (ZMod 2) E) (v : E) :
    ∃ a₀ a₁ a₂ : ZMod 2, v = a₀ • b 0 + a₁ • b 1 + a₂ • b 2 :=
  ⟨b.repr v 0, b.repr v 1, b.repr v 2, by
    have := b.sum_repr v
    rw [Fin.sum_univ_three] at this
    exact this.symm⟩

omit [FiniteDimensional (ZMod 2) E] in
theorem exists_linearEquiv_triple (hE : finrank (ZMod 2) E = 3) {e x y e' x' y' : E}
    (he : e ≠ 0) (hx : x ∉ Submodule.span (ZMod 2) {e}) (hy : y ∉ Submodule.span (ZMod 2) {e, x})
    (he' : e' ≠ 0) (hx' : x' ∉ Submodule.span (ZMod 2) {e'})
    (hy' : y' ∉ Submodule.span (ZMod 2) {e', x'}) :
    ∃ A : E ≃ₗ[ZMod 2] E, A y = y' ∧ A x = x' ∧ A e = e' := by
  set b := tripleBasis hE he hx hy
  set b' := tripleBasis hE he' hx' hy'
  refine ⟨b.equiv b' (Equiv.refl _), ?_, ?_, ?_⟩
  · rw [← tripleBasis_zero hE he hx hy, Basis.equiv_apply, Equiv.refl_apply,
      tripleBasis_zero hE he' hx' hy']
  · rw [← tripleBasis_one hE he hx hy, Basis.equiv_apply, Equiv.refl_apply,
      tripleBasis_one hE he' hx' hy']
  · rw [← tripleBasis_two hE he hx hy, Basis.equiv_apply, Equiv.refl_apply,
      tripleBasis_two hE he' hx' hy']

theorem exists_linearEquiv_apply_eq (hE : finrank (ZMod 2) E = 3) {u w : E} (hu : u ≠ 0)
    (hw : w ≠ 0) : ∃ A : E ≃ₗ[ZMod 2] E, A u = w := by
  obtain ⟨x, hx⟩ := exists_not_mem_span_singleton hE u
  obtain ⟨y, hy⟩ := exists_not_mem_span_pair hE u x
  obtain ⟨x', hx'⟩ := exists_not_mem_span_singleton hE w
  obtain ⟨y', hy'⟩ := exists_not_mem_span_pair hE w x'
  obtain ⟨A, -, -, hA⟩ := exists_linearEquiv_triple hE hu hx hy hw hx' hy'
  exact ⟨A, hA⟩

omit [FiniteDimensional (ZMod 2) E] in
theorem exists_linearEquiv_fix_fix_move (hE : finrank (ZMod 2) E = 3) {e x z : E} (he : e ≠ 0)
    (hx : x ∉ Submodule.span (ZMod 2) {e}) (hz : z ∉ Submodule.span (ZMod 2) {e, x}) :
    ∃ A : E ≃ₗ[ZMod 2] E, A e = e ∧ A x = x ∧ A z ≠ z := by
  have hz' : z + e ∉ Submodule.span (ZMod 2) {e, x} := fun h => hz (by
    have he' : e ∈ Submodule.span (ZMod 2) {e, x} := Submodule.subset_span (by simp)
    have := Submodule.sub_mem _ h he'
    simpa using this)
  obtain ⟨A, hAz, hAx, hAe⟩ := exists_linearEquiv_triple hE he hx hz he hx hz'
  refine ⟨A, hAe, hAx, fun h => he ?_⟩
  rw [hAz] at h
  simpa using h

omit [FiniteDimensional (ZMod 2) E] in
theorem f2_neg (v : E) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, f2_add_self]

omit [FiniteDimensional (ZMod 2) E] in
theorem swap_add_e [DecidableEq E] (e w : E) :
    Equiv.swap 0 e (w + e) = Equiv.swap 0 e w + e := by
  by_cases hw0 : w = 0
  · rw [hw0, zero_add, Equiv.swap_apply_right, Equiv.swap_apply_left, f2_add_self]
  by_cases hwe : w = e
  · rw [hwe, f2_add_self, Equiv.swap_apply_left, Equiv.swap_apply_right, zero_add]
  have h1 : w + e ≠ 0 := fun h => hwe (by rw [f2_add_right_eq_iff, zero_add] at h; exact h)
  have h2 : w + e ≠ e := fun h => hw0 (by rwa [add_eq_right] at h)
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne hw0 hwe]

omit [FiniteDimensional (ZMod 2) E] in
theorem forall_of_basis (b : Basis (Fin 3) (ZMod 2) E) {P : E → Prop} (h0 : P 0)
    (hx : P (b 1)) (hy : P (b 0)) (hxy : P (b 0 + b 1)) (he : ∀ v, P v → P (v + b 2)) (v : E) :
    P v := by
  obtain ⟨a₀, a₁, a₂, rfl⟩ := exists_coords b v
  have hbase : P (a₀ • b 0 + a₁ • b 1) := by
    rcases f2_cases a₀ with rfl | rfl <;>
      rcases f2_cases a₁ with rfl | rfl <;> simpa
  rcases f2_cases a₂ with rfl | rfl
  · simpa using hbase
  · simpa using he _ hbase

omit [FiniteDimensional (ZMod 2) E] in
theorem span_pair_add_le {e x : E} :
    Submodule.span (ZMod 2) {e, x + e} ≤ Submodule.span (ZMod 2) {e, x} := by
  rw [Submodule.span_le]
  rintro v (rfl | rfl)
  · exact Submodule.subset_span (by simp)
  · exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))

theorem affine_or_swap [DecidableEq E] (hE : finrank (ZMod 2) E = 3) {e : E} (he : e ≠ 0)
    (s : Equiv.Perm E) (hs0 : s 0 = e) (hse : s e = 0) (hs : ∀ v, s (v + e) = s v + e) :
    (∃ A : E ≃ₗ[ZMod 2] E, ∀ v, s v = e + A v) ∨
      ∃ A : E ≃ₗ[ZMod 2] E, ∀ v, s v = Equiv.swap 0 e (A v) := by
  obtain ⟨x, hx⟩ := exists_not_mem_span_singleton hE e
  obtain ⟨y, hy⟩ := exists_not_mem_span_pair hE e x
  have hspan_e : e ∈ Submodule.span (ZMod 2) {e, x} := Submodule.subset_span (by simp)
  have hspan_x : x ∈ Submodule.span (ZMod 2) {e, x} := Submodule.subset_span (by simp)
  have hinj : ∀ {u w}, s u = s w → u = w := fun h => s.injective h
  have hx0 : x ≠ 0 := fun h => hx (by rw [h]; exact Submodule.zero_mem _)
  have hxe : x ≠ e := fun h => hx (by rw [h]; exact Submodule.mem_span_singleton_self e)
  have hy0 : y ≠ 0 := fun h => hy (by rw [h]; exact Submodule.zero_mem _)
  have hye : y ≠ e := fun h => hy (by rw [h]; exact hspan_e)
  have hyx : y ≠ x := fun h => hy (by rw [h]; exact hspan_x)
  have hyxe : y ≠ x + e := fun h => hy (by rw [h]; exact Submodule.add_mem _ hspan_x hspan_e)
  set x' := s x + e with hx'def
  set y' := s y + e with hy'def
  have hsx : s x = x' + e := by rw [hx'def, add_assoc, f2_add_self, add_zero]
  have hsy : s y = y' + e := by rw [hy'def, add_assoc, f2_add_self, add_zero]
  have hsxe : s (x + e) = x' := by rw [hs, hx'def]
  have hsye : s (y + e) = y' := by rw [hs, hy'def]
  have hx' : x' ∉ Submodule.span (ZMod 2) {e} := by
    rw [mem_span_singleton_iff]
    rintro (h | h)
    · exact hx0 ((add_eq_right).mp (hinj (hsxe.trans (h.trans hse.symm))))
    · exact hxe ((f2_add_right_eq_iff.mp (hinj (hsxe.trans (h.trans hs0.symm)))).trans
        (zero_add e))
  have hy' : y' ∉ Submodule.span (ZMod 2) {e, x'} := by
    rw [mem_span_pair_iff]
    rintro (h | h | h | h)
    · exact hy0 ((add_eq_right).mp (hinj (hsye.trans (h.trans hse.symm))))
    · exact hye ((f2_add_right_eq_iff.mp (hinj (hsye.trans (h.trans hs0.symm)))).trans
        (zero_add e))
    · exact hyx ((add_left_inj e).mp (hinj (hsye.trans (h.trans hsxe.symm))))
    · have : s (y + e) = s x := by
        rw [hsye, h, hsx, add_comm]
      exact hyxe (f2_add_right_eq_iff.mp (hinj this))
  have hspan'_e : e ∈ Submodule.span (ZMod 2) {e, x'} := Submodule.subset_span (by simp)
  have hspan'_x : x' ∈ Submodule.span (ZMod 2) {e, x'} := Submodule.subset_span (by simp)
  have hz : s (x + y) = y' + x' + e ∨ s (x + y) = y' + x' := by
    obtain ⟨a₀, a₁, a₂, hval⟩ := exists_coords (tripleBasis hE he hx' hy') (s (x + y))
    rw [tripleBasis_zero, tripleBasis_one, tripleBasis_two] at hval
    rcases f2_cases a₀ with rfl | rfl <;>
      rcases f2_cases a₁ with rfl | rfl <;>
      rcases f2_cases a₂ with rfl | rfl <;>
      simp only [zero_smul, one_smul, zero_add, add_zero] at hval
    · exact absurd (by rw [eq_neg_add_of_add_eq (hinj (hval.trans hse.symm)), f2_neg]) hyxe
    · exact absurd (by rw [eq_neg_add_of_add_eq (hinj (hval.trans hs0.symm)), f2_neg,
        add_zero]) hyx
    · exact absurd (add_left_cancel (hinj (hval.trans hsxe.symm))) hye
    · exact absurd ((add_eq_left).mp (hinj (hval.trans hsx.symm))) hy0
    · exact absurd (add_right_cancel ((hinj (hval.trans hsye.symm)).trans (add_comm y e))) hxe
    · exact absurd ((add_eq_right).mp (hinj (hval.trans hsy.symm))) hx0
    · exact Or.inr hval
    · exact Or.inl hval
  set b := tripleBasis hE he hx hy
  have hb0 : b 0 = y := tripleBasis_zero hE he hx hy
  have hb1 : b 1 = x := tripleBasis_one hE he hx hy
  have hb2 : b 2 = e := tripleBasis_two hE he hx hy
  rcases hz with hz | hz
  ·
    obtain ⟨A, hAy, hAx, hAe⟩ := exists_linearEquiv_triple hE he hx hy he hx' hy'
    refine Or.inl ⟨A, forall_of_basis b (P := fun v => s v = e + A v) ?_ ?_ ?_ ?_ ?_⟩
    · simp [hs0]
    · simp only [hb1, hsx, hAx, add_comm]
    · simp only [hb0, hsy, hAy, add_comm]
    · rw [hb0, hb1, add_comm y x, hz, map_add, hAx, hAy]
      abel
    · intro v hv
      rw [hb2, hs, hv, map_add, hAe]
      abel
  ·
    have hx'' : x' + e ∉ Submodule.span (ZMod 2) {e} := fun h => hx' (by
      have := Submodule.add_mem _ h (Submodule.mem_span_singleton_self e)
      rwa [add_assoc, f2_add_self, add_zero] at this)
    have hy'' : y' + e ∉ Submodule.span (ZMod 2) {e, x' + e} := fun h => hy' (by
      have := Submodule.add_mem _ (span_pair_add_le h) hspan'_e
      rwa [add_assoc, f2_add_self, add_zero] at this)
    obtain ⟨A, hAy, hAx, hAe⟩ := exists_linearEquiv_triple hE he hx hy he hx'' hy''
    have hfix : ∀ w, w ∉ Submodule.span (ZMod 2) {e} → Equiv.swap 0 e w = w := fun w hw =>
      Equiv.swap_apply_of_ne_of_ne (fun h => hw (by rw [h]; exact Submodule.zero_mem _))
        (fun h => hw (by rw [h]; exact Submodule.mem_span_singleton_self e))
    refine Or.inr ⟨A, forall_of_basis b (P := fun v => s v = Equiv.swap 0 e (A v))
      ?_ ?_ ?_ ?_ ?_⟩
    · simp [hs0]
    · simp only [hb1, hsx, hAx]
      exact (hfix _ hx'').symm
    · simp only [hb0, hsy, hAy]
      refine (hfix _ fun h => hy' ?_).symm
      have := Submodule.add_mem _ (Submodule.span_mono (by simp) h :
        y' + e ∈ Submodule.span (ZMod 2) {e, x'}) hspan'_e
      rwa [add_assoc, f2_add_self, add_zero] at this
    · rw [hb0, hb1, add_comm y x, hz, map_add, hAx, hAy]
      have hsum : x' + e + (y' + e) = y' + x' := by
        rw [add_add_add_comm, f2_add_self, add_zero, add_comm]
      rw [hsum]
      refine (hfix _ fun h => hy' ?_).symm
      rcases mem_span_singleton_iff.mp h with h | h
      · rw [eq_neg_of_add_eq_zero_left h, f2_neg]
        exact hspan'_x
      · rw [eq_add_neg_of_add_eq h, f2_neg]
        exact Submodule.add_mem _ hspan'_e hspan'_x
    · intro v hv
      rw [hb2, hs, hv, map_add, hAe, swap_add_e]


omit [FiniteDimensional (ZMod 2) E] in
theorem map_add_e (hE : finrank (ZMod 2) E = 3) {K : Subgroup (Equiv.Perm E)}
    (hlin : ∀ σ ∈ K, σ 0 = 0 → ∃ A : E ≃ₗ[ZMod 2] E, ∀ v, σ v = A v)
    (hK : ∀ A : E ≃ₗ[ZMod 2] E, A.toEquiv ∈ K) {e : E} (he : e ≠ 0) {s : Equiv.Perm E}
    (hs : s ∈ K) (hs0 : s 0 = e) (hse : s e = 0) (v : E) : s (v + e) = s v + e := by
  have hsi0 : s⁻¹ e = 0 := Equiv.Perm.inv_eq_iff_eq.mpr hs0.symm
  have hsie : s⁻¹ 0 = e := Equiv.Perm.inv_eq_iff_eq.mpr hse.symm
  by_cases hv : v ∈ Submodule.span (ZMod 2) {e}
  · rcases mem_span_singleton_iff.mp hv with rfl | rfl
    · rw [zero_add, hse, hs0, f2_add_self]
    · rw [f2_add_self, hs0, hse, zero_add]
  have hsv : s v ∉ Submodule.span (ZMod 2) {e} := by
    rw [mem_span_singleton_iff]
    rintro (h | h)
    · exact hv (mem_span_singleton_iff.mpr (Or.inr (s.injective (h.trans hse.symm))))
    · exact hv (mem_span_singleton_iff.mpr (Or.inl (s.injective (h.trans hs0.symm))))
  have hmem : s (v + e) ∈ Submodule.span (ZMod 2) {e, s v} := by
    by_contra hz
    obtain ⟨A, hAe, hAx, hAz⟩ := exists_linearEquiv_fix_fix_move hE he hsv hz
    have hσK : s⁻¹ * A.toEquiv * s ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hs) (hK A)) hs
    have happ : ∀ w, (s⁻¹ * A.toEquiv * s) w = s⁻¹ (A (s w)) := fun _ => rfl
    obtain ⟨B, hB⟩ := hlin _ hσK (by rw [happ, hs0, hAe, hsi0])
    have hBe : B e = e := by rw [← hB, happ, hse, map_zero, hsie]
    have hBv : B v = v := by
      rw [← hB, happ, hAx]
      exact s.symm_apply_apply v
    apply hAz
    have h := hB (v + e)
    rw [map_add B v e, hBv, hBe, happ, Equiv.Perm.inv_eq_iff_eq] at h
    exact h
  rcases mem_span_pair_iff.mp hmem with h | h | h | h
  · exact absurd (mem_span_singleton_iff.mpr
      (Or.inl ((add_eq_right).mp (s.injective (h.trans hse.symm))))) hv
  · exact absurd (mem_span_singleton_iff.mpr
      (Or.inr ((f2_add_right_eq_iff.mp (s.injective (h.trans hs0.symm))).trans (zero_add e)))) hv
  · exact absurd ((add_eq_left).mp (s.injective h)) he
  · rw [h, add_comm]

theorem swap_not_mem [DecidableEq E] (hE : finrank (ZMod 2) E = 3) {K : Subgroup (Equiv.Perm E)}
    (hlin : ∀ σ ∈ K, σ 0 = 0 → ∃ A : E ≃ₗ[ZMod 2] E, ∀ v, σ v = A v)
    (hK : ∀ A : E ≃ₗ[ZMod 2] E, A.toEquiv ∈ K) {e : E} (he : e ≠ 0) :
    Equiv.swap 0 e ∉ K := by
  intro hτ
  obtain ⟨x, hx⟩ := exists_not_mem_span_singleton hE e
  obtain ⟨y, hy⟩ := exists_not_mem_span_pair hE e x
  have hx0 : x ≠ 0 := fun h => hx (by rw [h]; exact Submodule.zero_mem _)
  have hxe : x ≠ e := fun h => hx (by rw [h]; exact Submodule.mem_span_singleton_self e)
  obtain ⟨B, hB⟩ := exists_linearEquiv_apply_eq hE he hx0
  have h1 : Equiv.swap 0 x ∈ K := by
    have := Equiv.swap_apply_apply B.toEquiv 0 e
    rw [show B.toEquiv 0 = 0 from map_zero B, show B.toEquiv e = x from hB] at this
    rw [this]
    exact K.mul_mem (K.mul_mem (hK B) hτ) (K.inv_mem (hK B))
  have h2 : Equiv.swap e x ∈ K := by
    have := Equiv.swap_apply_apply (Equiv.swap 0 e) 0 x
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hx0 hxe] at this
    rw [this]
    exact K.mul_mem (K.mul_mem hτ h1) (K.inv_mem hτ)
  obtain ⟨C, hC⟩ := hlin _ h2 (Equiv.swap_apply_of_ne_of_ne he.symm hx0.symm)
  have hspan_e : e ∈ Submodule.span (ZMod 2) {e, x} := Submodule.subset_span (by simp)
  have hspan_x : x ∈ Submodule.span (ZMod 2) {e, x} := Submodule.subset_span (by simp)
  have hye : y ≠ e := fun h => hy (by rw [h]; exact hspan_e)
  have hyx : y ≠ x := fun h => hy (by rw [h]; exact hspan_x)
  have h3 : e + y ≠ e := fun h => hy (by rw [(add_eq_left).mp h]; exact Submodule.zero_mem _)
  have h4 : e + y ≠ x := fun h => hy (by
    rw [eq_neg_add_of_add_eq h, f2_neg]
    exact Submodule.add_mem _ hspan_e hspan_x)
  have hCe : C e = x := by rw [← hC, Equiv.swap_apply_left]
  have hCy : C y = y := by rw [← hC, Equiv.swap_apply_of_ne_of_ne hye hyx]
  have hey := hC (e + y)
  rw [Equiv.swap_apply_of_ne_of_ne h3 h4, map_add, hCe, hCy] at hey
  exact hxe (add_right_cancel hey).symm

theorem card_linearEquiv (hE : finrank (ZMod 2) E = 3) : Nat.card (E ≃ₗ[ZMod 2] E) = 168 := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) E hE
  let e1 : (E ≃ₗ[ZMod 2] E) ≃* GL (Fin 3) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) E).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)
  rw [Nat.card_congr e1.toEquiv, Matrix.card_GL_field]
  simp [Fin.prod_univ_three, ZMod.card]

end BinaryAffineEight

open BinaryAffineEight in
theorem binary_affine_eight_full_linear_point_stabilizer {E : Type*} [AddCommGroup E]
    [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E] (hE : finrank (ZMod 2) E = 3)
    (K : Subgroup (Equiv.Perm E)) (htrans : ∀ v w : E, ∃ k ∈ K, k v = w)
    (hstab : K ⊓ MulAction.stabilizer (Equiv.Perm E) (0 : E) = linearPerms E) :
    K = affinePerms E ∧ translationPerms E ≤ K ∧
      (∀ v w : E, ∃! t, t ∈ translationPerms E ∧ t v = w) ∧
      (∀ s ∈ translationPerms E, ∀ t ∈ translationPerms E, s * t = t * s) ∧
      (∀ t ∈ translationPerms E, t * t = 1) ∧ Nat.card (translationPerms E) = 8 ∧
      ((translationPerms E).subgroupOf K).Normal ∧ IsPGroup 2 (translationPerms E) ∧
      (∀ N : Subgroup (Equiv.Perm E), N ≤ K → (N.subgroupOf K).Normal → IsPGroup 2 N →
        N ≤ translationPerms E) ∧
      CFSG.Assembly.pCoreOf 2 K = translationPerms E ∧
      translationPerms E ⊓ (K ⊓ MulAction.stabilizer (Equiv.Perm E) (0 : E)) = ⊥ ∧
      translationPerms E ⊔ (K ⊓ MulAction.stabilizer (Equiv.Perm E) (0 : E)) = K ∧
      Nat.card K = 1344 := by
  classical
  have hlin : ∀ σ ∈ K, σ 0 = 0 → ∃ A : E ≃ₗ[ZMod 2] E, ∀ v, σ v = A v := fun σ hσ h0 => by
    have hmem : σ ∈ K ⊓ MulAction.stabilizer (Equiv.Perm E) (0 : E) :=
      ⟨hσ, MulAction.mem_stabilizer_iff.mpr h0⟩
    rw [hstab] at hmem
    exact hmem
  have hK : ∀ A : E ≃ₗ[ZMod 2] E, A.toEquiv ∈ K := fun A => by
    have hmem : A.toEquiv ∈ linearPerms E := ⟨A, fun _ => rfl⟩
    rw [← hstab] at hmem
    exact hmem.1
  have haff : ∀ k ∈ K, ∃ (a : E) (A : E ≃ₗ[ZMod 2] E), ∀ v, k v = a + A v := by
    intro k hk
    by_cases h0 : k 0 = 0
    · obtain ⟨A, hA⟩ := hlin k hk h0
      exact ⟨0, A, fun v => by rw [hA, zero_add]⟩
    have hw : k⁻¹ 0 ≠ 0 := fun h => h0 (by
      have h1 : k (k⁻¹ 0) = 0 := k.apply_symm_apply 0
      rwa [h] at h1)
    obtain ⟨A, hA⟩ := exists_linearEquiv_apply_eq hE h0 hw
    have hs : k * A.toEquiv ∈ K := K.mul_mem hk (hK A)
    have hs0 : (k * A.toEquiv) 0 = k 0 := by
      show k (A 0) = k 0
      rw [map_zero]
    have hse : (k * A.toEquiv) (k 0) = 0 := by
      show k (A (k 0)) = 0
      rw [hA]
      exact k.apply_symm_apply 0
    have hcomm := map_add_e hE hlin hK h0 hs hs0 hse
    rcases affine_or_swap hE h0 _ hs0 hse hcomm with ⟨B, hB⟩ | ⟨B, hB⟩
    · refine ⟨k 0, A.symm.trans B, fun v => ?_⟩
      have h := hB (A.symm v)
      rw [show (k * A.toEquiv) (A.symm v) = k v from congrArg k (A.apply_symm_apply v)] at h
      rw [h]
      rfl
    · exfalso
      apply swap_not_mem hE hlin hK h0
      have : Equiv.swap 0 (k 0) = k * A.toEquiv * B.toEquiv⁻¹ := by
        ext v
        show Equiv.swap 0 (k 0) v = (k * A.toEquiv) (B.symm v)
        rw [hB, B.apply_symm_apply]
      rw [this]
      exact K.mul_mem hs (K.inv_mem (hK B))
  have htmem : ∀ a : E, Equiv.addLeft a ∈ translationPerms E := fun a => ⟨a, fun _ => rfl⟩
  have htK : translationPerms E ≤ K := by
    rintro t ⟨a, ht⟩
    obtain ⟨k, hk, hk0⟩ := htrans 0 a
    obtain ⟨b, B, hkB⟩ := haff k hk
    have hb : b = a := by rw [← hk0, hkB, map_zero, add_zero]
    have : t = k * B.toEquiv⁻¹ := by
      ext v
      show t v = k (B.symm v)
      rw [ht, hkB, B.apply_symm_apply, hb]
    rw [this]
    exact K.mul_mem hk (K.inv_mem (hK B))
  have hKeq : K = affinePerms E := by
    refine le_antisymm (fun k hk => haff k hk) ?_
    rintro σ ⟨a, A, hσ⟩
    have : σ = Equiv.addLeft a * A.toEquiv := by
      ext v
      exact hσ v
    rw [this]
    exact K.mul_mem (htK (htmem a)) (hK A)
  have hreg : ∀ v w : E, ∃! t, t ∈ translationPerms E ∧ t v = w := by
    intro v w
    refine ⟨Equiv.addLeft (w - v), ⟨htmem _, by simp⟩, ?_⟩
    rintro t ⟨⟨a, ht⟩, htv⟩
    ext u
    rw [ht] at htv ⊢
    show a + u = w - v + u
    rw [eq_sub_of_add_eq htv]
  have hcommU : ∀ s ∈ translationPerms E, ∀ t ∈ translationPerms E, s * t = t * s := by
    rintro s ⟨a, hs⟩ t ⟨b, ht⟩
    ext v
    simp only [Equiv.Perm.mul_apply, hs, ht]
    abel
  have hsq : ∀ t ∈ translationPerms E, t * t = 1 := by
    rintro t ⟨a, ht⟩
    ext v
    simp only [Equiv.Perm.mul_apply, ht, Equiv.Perm.one_apply]
    rw [← add_assoc, f2_add_self, zero_add]
  have hcardU : Nat.card (translationPerms E) = 8 := by
    rw [← card_eq_eight hE]
    refine Nat.card_congr
      { toFun := fun t => (t : Equiv.Perm E) 0
        invFun := fun a => ⟨Equiv.addLeft a, htmem a⟩
        left_inv := fun t => ?_
        right_inv := fun a => ?_ }
    · obtain ⟨a, ht⟩ := t.2
      apply Subtype.ext
      ext v
      show (t : Equiv.Perm E) 0 + v = (t : Equiv.Perm E) v
      rw [ht, ht, add_zero]
    · show a + 0 = a
      rw [add_zero]
  have hU2 : IsPGroup 2 (translationPerms E) := IsPGroup.of_card (n := 3) (by rw [hcardU]; rfl)
  have hconj : ∀ k ∈ K, ∀ t ∈ translationPerms E, k * t * k⁻¹ ∈ translationPerms E := by
    rintro k hk t ⟨b, ht⟩
    obtain ⟨a, A, hkA⟩ := haff k hk
    refine ⟨A b, fun v => ?_⟩
    show k (t (k⁻¹ v)) = A b + v
    have h : a + A (k⁻¹ v) = v := by
      rw [← hkA]
      exact k.apply_symm_apply v
    rw [ht, hkA, map_add]
    calc a + (A b + A (k⁻¹ v)) = A b + (a + A (k⁻¹ v)) := by abel
      _ = A b + v := by rw [h]
  have hUn : ((translationPerms E).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer htK]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨hconj k hk t, fun h => ?_⟩
    have := hconj k⁻¹ (K.inv_mem hk) _ h
    rwa [show k⁻¹ * (k * t * k⁻¹) * k⁻¹⁻¹ = t by group] at this
  have hmax : ∀ N : Subgroup (Equiv.Perm E), N ≤ K → (N.subgroupOf K).Normal →
      IsPGroup 2 N → N ≤ translationPerms E := by
    intro N hNK hNn hN2
    have hNnorm : K ≤ Subgroup.normalizer (N : Set (Equiv.Perm E)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hNn
    have hlinpart : ∀ n ∈ N, ∃ A : E ≃ₗ[ZMod 2] E, ∀ v, n v - n 0 = A v := by
      intro n hn
      obtain ⟨a, A, hA⟩ := haff n (hNK hn)
      exact ⟨A, fun v => by rw [hA, hA, map_zero, add_zero, add_sub_cancel_left]⟩
    have hne : ∀ n : Equiv.Perm E, ∀ v : E, v ≠ 0 → n v - n 0 ≠ 0 := fun n v hv h =>
      hv (n.injective (sub_eq_zero.mp h))
    let act : MulAction N {v : E // v ≠ 0} :=
      { smul := fun n v => ⟨(n : Equiv.Perm E) v - (n : Equiv.Perm E) 0, hne _ v v.2⟩
        one_smul := fun v => Subtype.ext (by
          show ((1 : N) : Equiv.Perm E) v - ((1 : N) : Equiv.Perm E) 0 = v
          simp)
        mul_smul := fun n m v => Subtype.ext (by
          obtain ⟨A, hA⟩ := hlinpart n n.2
          show ((n * m : N) : Equiv.Perm E) v - ((n * m : N) : Equiv.Perm E) 0 =
            (n : Equiv.Perm E) ((m : Equiv.Perm E) v - (m : Equiv.Perm E) 0) -
              (n : Equiv.Perm E) 0
          rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hA, map_sub,
            ← hA, ← hA]
          abel) }
    have : Finite E := Module.finite_of_finite (ZMod 2)
    have h7 : Nat.card {v : E // v ≠ 0} = 7 := by
      let := Fintype.ofFinite E
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
        ← Nat.card_eq_fintype_card, card_eq_eight hE]
    have hmod := hN2.card_modEq_card_fixedPoints {v : E // v ≠ 0}
    rw [h7] at hmod
    have hpos : Nat.card (MulAction.fixedPoints N {v : E // v ≠ 0}) ≠ 0 := by
      intro h0
      rw [h0] at hmod
      exact absurd hmod (by decide)
    obtain ⟨⟨v₀, hv₀⟩⟩ := (Nat.card_ne_zero.mp hpos).1
    have hfixall : ∀ n ∈ N, ∀ w : E, n w - n 0 = w := by
      intro n hn w
      by_cases hw : w = 0
      · rw [hw, sub_self]
      obtain ⟨B, hB⟩ := exists_linearEquiv_apply_eq hE v₀.2 hw
      have hn' : B.toEquiv⁻¹ * n * B.toEquiv ∈ N := by
        have := (Subgroup.mem_normalizer_iff.mp (hNnorm (K.inv_mem (hK B))) n).mp hn
        rwa [inv_inv] at this
      have h : B.symm (n (B v₀)) - B.symm (n (B 0)) = v₀ :=
        congrArg Subtype.val (hv₀ ⟨_, hn'⟩)
      rw [map_zero, ← map_sub, hB] at h
      have h2 := congrArg B h
      rw [B.apply_symm_apply, hB] at h2
      exact h2
    intro n hn
    exact ⟨n 0, fun v => eq_add_of_sub_eq' (hfixall n hn v)⟩
  have hpcore : CFSG.Assembly.pCoreOf 2 K = translationPerms E := by
    apply le_antisymm
    · apply hmax
      · exact Subgroup.map_subtype_le _
      · have : ((CFSG.Assembly.pCore 2 K).map K.subtype).subgroupOf K =
            CFSG.Assembly.pCore 2 K :=
          Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
        rw [CFSG.Assembly.pCoreOf, this]
        infer_instance
      · exact (CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_isPGroup_assembly 2 K).map
          K.subtype
    · have hU2' : IsPGroup 2 ((translationPerms E).subgroupOf K) :=
        IsPGroup.of_card (n := 3) (by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe htK).toEquiv, hcardU]
          rfl)
      rw [← Subgroup.map_subgroupOf_eq_of_le htK]
      exact Subgroup.map_mono
        (CFSG.Assembly.Dichotomy.CentralizerContainment.le_pCore_assembly hUn hU2')
  have hinf : translationPerms E ⊓ (K ⊓ MulAction.stabilizer (Equiv.Perm E) (0 : E)) = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨⟨a, ht⟩, -, hst⟩
    have hst' : t 0 = 0 := hst
    have ha : a = 0 := by
      have := ht 0
      rwa [add_zero, hst', eq_comm] at this
    rw [Subgroup.mem_bot]
    ext v
    rw [ht, ha, zero_add]
    rfl
  have hsup : translationPerms E ⊔ (K ⊓ MulAction.stabilizer (Equiv.Perm E) (0 : E)) = K := by
    refine le_antisymm (sup_le htK inf_le_left) fun k hk => ?_
    have h1 := htmem (k 0)
    have h2 : (Equiv.addLeft (k 0))⁻¹ * k ∈ K ⊓ MulAction.stabilizer (Equiv.Perm E) (0 : E) := by
      refine ⟨K.mul_mem (K.inv_mem (htK h1)) hk, ?_⟩
      show (Equiv.addLeft (k 0)).symm (k 0) = 0
      simp
    have := Subgroup.mul_mem_sup h1 h2
    rwa [mul_inv_cancel_left] at this
  have hcardK : Nat.card K = 1344 := by
    rw [hKeq]
    let f : E × (E ≃ₗ[ZMod 2] E) → affinePerms E := fun p =>
      ⟨Equiv.addLeft p.1 * p.2.toEquiv, ⟨p.1, p.2, fun _ => rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨a, A⟩ ⟨b, B⟩ h
        have h' : ∀ v, a + A v = b + B v := fun v =>
          congrArg (fun σ : affinePerms E => (σ : Equiv.Perm E) v) h
        have hab : a = b := by simpa using h' 0
        subst hab
        refine Prod.ext rfl (LinearEquiv.ext fun v => ?_)
        exact add_left_cancel (h' v)
      · rintro ⟨σ, a, A, hσ⟩
        exact ⟨(a, A), Subtype.ext (Equiv.ext fun v => (hσ v).symm)⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, card_eq_eight hE,
      card_linearEquiv hE]
  exact ⟨hKeq, htK, hreg, hcommU, hsq, hcardU, hUn, hU2, hmax, hpcore, hinf, hsup, hcardK⟩

end CFSG.LocalAnalysis.ComponentInitial
