module

public import CFSG.ClassicalInvolution.Asc77.AscE189OrthV
public import CFSG.ClassicalInvolution.Balance.StrongPowOrthElem

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM.S4L

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

structure IsON (Q : QuadraticForm F V) {n : ℕ} (w : Fin n → V) : Prop where
  q : ∀ i, Q (w i) = 1
  o : ∀ i j, i ≠ j → polar Q (w i) (w j) = 0

namespace IsON

variable {n : ℕ} {w : Fin n → V}

theorem polar_apply (h : IsON Q w) (i j : Fin n) :
    polar Q (w i) (w j) = if i = j then 2 else 0 := by
  by_cases hij : i = j
  · subst hij
    simp [polar_self, h.q]
  · simp [hij, h.o i j hij]

theorem polar_comb_basis (h : IsON Q w) (c : Fin n → F) (j : Fin n) :
    polar Q (∑ i, c i • w i) (w j) = 2 * c j := by
  have h1 := LinearMap.BilinForm.sum_left (polarBilin Q) Finset.univ (fun i => c i • w i) (w j)
  simp only [polarBilin_apply_apply] at h1
  rw [h1]
  simp [polar_smul_left, h.polar_apply, mul_comm]

theorem polar_basis_comb (h : IsON Q w) (c : Fin n → F) (j : Fin n) :
    polar Q (w j) (∑ i, c i • w i) = 2 * c j := by
  rw [polar_comm, h.polar_comb_basis]

theorem polar_comb (h : IsON Q w) (c d : Fin n → F) :
    polar Q (∑ i, c i • w i) (∑ i, d i • w i) = 2 * ∑ i, c i * d i := by
  have h1 := LinearMap.BilinForm.sum_left (polarBilin Q) Finset.univ (fun i => c i • w i)
    (∑ i, d i • w i)
  simp only [polarBilin_apply_apply] at h1
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [polar_smul_left, polar_basis_comb h, smul_eq_mul]
  ring

theorem linearIndependent (h : IsON Q w) (h2 : (2 : F) ≠ 0) : LinearIndependent F w := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have := h.polar_comb_basis c j
  rw [hc, polar_zero_left] at this
  have h' : (2 : F) * c j = 0 := this.symm
  exact (mul_eq_zero.mp h').resolve_left h2

end IsON

section Sp

variable {n : ℕ} (w : Fin n → V)

@[expose] def Sp (F : Type) [Field F] [Module F V] (s : Finset (Fin n)) : Submodule F V :=
  Submodule.span F (w '' (s : Set (Fin n)))

variable {w}

theorem mem_Sp_iff {s : Finset (Fin n)} {v : V} :
    v ∈ Sp w F s ↔ ∃ c : Fin n → F, (∀ i ∉ s, c i = 0) ∧ v = ∑ i, c i • w i := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨Pi.single i 1, fun j hj => ?_, by simp⟩
      have : j ≠ i := fun h => hj (h ▸ hi)
      simp [this]
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, rfl⟩ := hy
      refine ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], ?_⟩
      simp [add_smul, Finset.sum_add_distrib]
    | smul a x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨a • c, fun i hi => by simp [hc i hi], ?_⟩
      simp [Finset.smul_sum, smul_smul]
  · rintro ⟨c, hc, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ s
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · simp [hc i hi]

theorem Sp_mono {s t : Finset (Fin n)} (h : s ⊆ t) : Sp w F s ≤ Sp w F t :=
  Submodule.span_mono (Set.image_mono (by exact_mod_cast h))

theorem Sp_sup (s t : Finset (Fin n)) : Sp w F s ⊔ Sp w F t = Sp w F (s ∪ t) := by
  simp only [Sp, Finset.coe_union, Set.image_union, Submodule.span_union]

theorem w_mem_Sp {s : Finset (Fin n)} {i : Fin n} (hi : i ∈ s) : w i ∈ Sp w F s :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem polar_Sp_Sp (hw : IsON Q w) {s t : Finset (Fin n)} (hd : Disjoint s t) {x y : V}
    (hx : x ∈ Sp w F s) (hy : y ∈ Sp w F t) : polar Q x y = 0 := by
  obtain ⟨c, hc, rfl⟩ := mem_Sp_iff.mp hx
  obtain ⟨d, hd', rfl⟩ := mem_Sp_iff.mp hy
  rw [hw.polar_comb]
  have : ∀ i, c i * d i = 0 := fun i => by
    by_cases hi : i ∈ s
    · have : i ∉ t := Finset.disjoint_left.mp hd hi
      simp [hd' i this]
    · simp [hc i hi]
  simp [this]

theorem polarNondegOn_Sp (hw : IsON Q w) (h2 : (2 : F) ≠ 0) (s : Finset (Fin n)) :
    PolarNondegOn Q (Sp w F s) := by
  intro x hx hxx
  obtain ⟨c, hc, rfl⟩ := mem_Sp_iff.mp hx
  have : ∀ j, c j = 0 := fun j => by
    by_cases hj : j ∈ s
    · have h1 := hxx (w j) (w_mem_Sp hj)
      rw [hw.polar_comb_basis] at h1
      exact (mul_eq_zero.mp h1).resolve_left h2
    · exact hc j hj
  simp [this]

theorem finrank_Sp (hw : IsON Q w) (h2 : (2 : F) ≠ 0) (s : Finset (Fin n)) :
    Module.finrank F (Sp w F s) = s.card := by
  have hli : LinearIndependent F (fun i : (s : Set (Fin n)) => w i) :=
    (hw.linearIndependent h2).comp Subtype.val Subtype.val_injective
  have := finrank_span_eq_card hli
  rw [Sp, Set.image_eq_range]
  simpa using this

end Sp

section Cmp

variable [FiniteDimensional F V] {n : ℕ}

@[expose] def Cmp (w : Fin n → V) (Q : QuadraticForm F V) : Submodule F V :=
  LinearMap.BilinForm.orthogonal (polarBilin Q) (Sp w F Finset.univ)

variable {w : Fin n → V}

theorem mem_Cmp_iff {z : V} : z ∈ Cmp w Q ↔ ∀ x ∈ Sp w F Finset.univ, polar Q z x = 0 :=
  mem_perp_iff

theorem isCompl_Cmp (hw : IsON Q w) (h2 : (2 : F) ≠ 0) :
    IsCompl (Sp w F Finset.univ) (Cmp w Q) :=
  isCompl_perp (nondegenerate_polarBilin_restrict (polarNondegOn_Sp hw h2 Finset.univ))

theorem polarNondegOn_Cmp (hw : IsON Q w) (h2 : (2 : F) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) : PolarNondegOn Q (Cmp w Q) :=
  CFSG.ClassicalInvolution.Asc77.polarNondegOn_of_isCompl hQ (isCompl_Cmp hw h2).symm
    (fun _ hx y hy => (mem_Cmp_iff.mp hx) y hy)

theorem finrank_Cmp (hw : IsON Q w) (h2 : (2 : F) ≠ 0) :
    Module.finrank F (Cmp w Q) + n = Module.finrank F V := by
  have h1 := Submodule.finrank_add_eq_of_isCompl (isCompl_Cmp hw h2)
  rw [finrank_Sp hw h2] at h1
  simpa [add_comm] using h1

theorem Cmp_ne_bot (hw : IsON Q w) (h2 : (2 : F) ≠ 0) (hdim : n < Module.finrank F V) :
    Cmp w Q ≠ ⊥ := by
  intro h
  have h1 := finrank_Cmp hw h2
  rw [h, finrank_bot] at h1
  omega

end Cmp

end CFSG.ClassicalInvolution.Q3.Q3AM.S4L
