module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open scoped Pointwise

variable {M Q : Type*} [Group M] [Group Q]

theorem central_inversion_phase_complement (D : Subgroup M) (_hDn : D.Normal)
    (_hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hD3 : ∀ d ∈ D, d ^ 3 = 1) (π : M →* Q)
    (hπ : π.ker = D) (E : Subgroup M) (hED : E ≤ D) {k : ℕ} (r : M) (g : Fin k → M)
    (hrE : r ∈ Subgroup.normalizer (E : Set M))
    (hgE : ∀ i, g i ∈ Subgroup.normalizer (E : Set M)) (hr2 : r ^ 2 = 1)
    (hrD : ∀ d ∈ D, r * d * r⁻¹ = d⁻¹) (hδ : ∀ i, r * g i * r⁻¹ * (g i)⁻¹ ∈ E) :
    let c : Fin k → M := fun i => (r * g i * r⁻¹ * (g i)⁻¹) ^ 2 * g i
    let C : Subgroup M := Subgroup.closure (insert r (Set.range c))
    let A : Subgroup M := Subgroup.closure ((E : Set M) ∪ insert r (Set.range g))
    (∀ x ∈ C, x * r = r * x) ∧ C ⊓ D = ⊥ ∧
    (∃ e : C ≃* Subgroup.closure (insert (π r) (Set.range fun i => π (g i))),
      ∀ x : C, (e x : Q) = π x) ∧
    E ≤ A ∧ C ≤ A ∧ (E.subgroupOf A).Normal ∧ E ⊓ C = ⊥ ∧
    (A : Set M) = (E : Set M) * (C : Set M) := by
  intro c C A
  set δ : Fin k → M := fun i => r * g i * r⁻¹ * (g i)⁻¹ with hδdef
  have hδinv : ∀ i, δ i ^ 2 = (δ i)⁻¹ := by
    intro i
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact hD3 _ (hED (hδ i))
  have hcr : ∀ i, r * c i * r⁻¹ = c i := by
    intro i
    change r * (δ i ^ 2 * g i) * r⁻¹ = δ i ^ 2 * g i
    calc r * (δ i ^ 2 * g i) * r⁻¹ = (r * δ i * r⁻¹) ^ 2 * (δ i * g i) := by
          rw [conj_pow]
          simp only [hδdef]
          group
      _ = (δ i)⁻¹ ^ 2 * (δ i * g i) := by rw [hrD _ (hED (hδ i))]
      _ = (δ i)⁻¹ * g i := by group
      _ = δ i ^ 2 * g i := by rw [hδinv]
  have hcent : ∀ x ∈ C, x * r = r * x := by
    intro x hx
    have hle : C ≤ Subgroup.centralizer ({r} : Set M) := by
      rw [Subgroup.closure_le]
      rintro y (rfl | ⟨i, rfl⟩)
      · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
      · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        have h := hcr i
        rw [mul_inv_eq_iff_eq_mul] at h
        exact h.symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have hCD : C ⊓ D = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun d hd => ?_
    obtain ⟨hdC, hdD⟩ := Subgroup.mem_inf.1 hd
    have h1 : r * d * r⁻¹ = d := by rw [← hcent d hdC, mul_inv_cancel_right]
    have h2 : d = d⁻¹ := h1.symm.trans (hrD d hdD)
    have h4 : d * d = 1 := (congrArg (d * ·) h2).trans (mul_inv_cancel d)
    have h3 := hD3 d hdD
    rw [pow_succ, pow_two, h4, one_mul] at h3
    exact h3
  have hinj : Function.Injective (π.domRestrict C) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxD : (x : M) ∈ D := by
      rw [← hπ, MonoidHom.mem_ker]
      exact hx
    have : (x : M) ∈ C ⊓ D := Subgroup.mem_inf.2 ⟨x.2, hxD⟩
    rw [hCD, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hπδ : ∀ i, π (δ i) = 1 := by
    intro i
    rw [← MonoidHom.mem_ker, hπ]
    exact hED (hδ i)
  have hrange : (π.domRestrict C).range =
      Subgroup.closure (insert (π r) (Set.range fun i => π (g i))) := by
    rw [MonoidHom.domRestrict_range, MonoidHom.map_closure, Set.image_insert_eq,
      ← Set.range_comp]
    congr 3
    funext i
    change π (δ i ^ 2 * g i) = π (g i)
    rw [map_mul, map_pow, hπδ, one_pow, one_mul]
  refine ⟨hcent, hCD, ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange),
    fun x => rfl⟩, ?_⟩
  have hEA : E ≤ A := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hrA : r ∈ A := Subgroup.subset_closure (Or.inr (Set.mem_insert r _))
  have hgA : ∀ i, g i ∈ A := fun i =>
    Subgroup.subset_closure (Or.inr (Set.mem_insert_of_mem r ⟨i, rfl⟩))
  have hCA : C ≤ A := by
    rw [Subgroup.closure_le]
    rintro y (rfl | ⟨i, rfl⟩)
    · exact hrA
    · exact mul_mem (pow_mem (hEA (hδ i)) 2) (hgA i)
  have hAN : A ≤ Subgroup.normalizer (E : Set M) := by
    rw [Subgroup.closure_le]
    rintro y (hy | rfl | ⟨i, rfl⟩)
    · exact Subgroup.le_normalizer hy
    · exact hrE
    · exact hgE i
  have hCN : C ≤ Subgroup.normalizer (E : Set M) := hCA.trans hAN
  have hEC : E ⊓ C = ⊥ := by
    rw [eq_bot_iff, ← hCD, inf_comm]
    exact inf_le_inf_left C hED
  have hAsup : A = E ⊔ C := by
    refine le_antisymm ?_ (sup_le hEA hCA)
    rw [Subgroup.closure_le]
    rintro y (hy | hy | ⟨i, rfl⟩)
    · exact Subgroup.mem_sup_left hy
    · subst hy
      exact Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_insert y _))
    · have hci : c i ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem r ⟨i, rfl⟩)
      have : g i = (δ i ^ 2)⁻¹ * c i := by
        change g i = (δ i ^ 2)⁻¹ * (δ i ^ 2 * g i)
        group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left (inv_mem (pow_mem (hδ i) 2)))
        (Subgroup.mem_sup_right hci)
  refine ⟨hEA, hCA, (Subgroup.normal_subgroupOf_iff_le_normalizer hEA).2 hAN, hEC, ?_⟩
  rw [hAsup]
  exact Subgroup.coe_mul_of_right_le_normalizer_left E C hCN

end CFSG.GroupTheory
