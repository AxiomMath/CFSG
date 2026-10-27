module

public import CFSG.GH74.Uniqueness.Section126Basic
public import CFSG.GH74.Uniqueness.Section126Bender
public import CFSG.GH74.Uniqueness.Section12BenderSub

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X} {c : Ctx12 Z M} {n i : ℕ}

theorem lemma126_first (h124 : Lemma124Stmt Z M) (h : LData c n i) {u : X} (hu : u ∈ c.D)
    (hu2 : orderOf u = 2) (hzu : u * c.z = c.z * u) (hz2 : orderOf c.z = 2) :
    ∀ x ∈ deltaSet Z M u, x = u ∨ IsConj (u * c.z) x := by
  intro x hx
  by_cases hxu : x = u
  · exact Or.inl hxu
  refine Or.inr ?_
  have hzmem : u * c.z ∈ deltaSet Z M u :=
    ⟨c.z, Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hzu.symm,
      Subgroup.subset_closure ⟨c.hz, c.hzM⟩⟩, hzu⟩
  have hne : u * c.z ≠ u := by
    intro h1
    have : c.z = 1 := by
      have h2 : u * c.z = u * 1 := by rw [h1, mul_one]
      exact mul_left_cancel h2
    rw [this, orderOf_one] at hz2
    omega
  obtain ⟨g, -, hg⟩ := (h124 c n i h u hu hu2).2.2.2.1 (u * c.z) hzmem x hx hne hxu
  exact isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv, hg]⟩

theorem lemma126_a (h : LData c n i) {u : X} (huM : u ∈ M) (hu2 : orderOf u = 2)
    (hns : ¬ Shears Z M u) : zHull Z M ≤ centralizer ({u} : Set X) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_contra hxu
  apply hns
  have hu1 : u * u = 1 := sec126_involution_mul_self hu2
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu1
  have hx1 : x * x = 1 := h.sec126_zHull_sq hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx1
  have key : ∀ p q : X, u * (p * q) * u = (u * p * u) * (u * q * u) := by
    intro p q
    calc u * (p * q) * u = u * p * (u * u) * q * u := by rw [hu1]; group
      _ = (u * p * u) * (u * q * u) := by group
  have hbM : u * x * u ∈ zHull Z M := by
    have := h.sec126_conj_mem_zHull' huM hx
    rwa [hui] at this
  have hb1 : (u * x * u) * (u * x * u) = 1 := h.sec126_zHull_sq hbM
  have hbc : x * (u * x * u) = (u * x * u) * x := h.sec126_zHull_comm hx hbM
  have hyM : x * (u * x * u) ∈ zHull Z M := (zHull Z M).mul_mem hx hbM
  have hubu : u * (u * x * u) * u = x := by
    calc u * (u * x * u) * u = (u * u) * x * (u * u) := by group
      _ = x := by rw [hu1]; group
  have huyu : u * (x * (u * x * u)) * u = x * (u * x * u) := by
    rw [key, hubu]
    exact hbc.symm
  have hyc : (x * (u * x * u)) * u = u * (x * (u * x * u)) := by
    calc (x * (u * x * u)) * u = (u * (x * (u * x * u)) * u) * u := by rw [huyu]
      _ = u * (x * (u * x * u)) * (u * u) := by group
      _ = u * (x * (u * x * u)) := by rw [hu1, mul_one]
  have hx₀ : x⁻¹ * u * x = (x * (u * x * u)) * u := by
    rw [hxi]
    calc x * u * x = x * (u * x * (u * u)) := by rw [hu1, mul_one]; group
      _ = (x * (u * x * u)) * u := by group
  refine ⟨x⁻¹ * u * x, ⟨x * (u * x * u), Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hyc, hyM⟩, hx₀⟩, ?_, isConj_iff.mpr ⟨x⁻¹, ?_⟩⟩
  · intro heq
    apply hxu
    have h1 : (x * (u * x * u)) * u = 1 * u := by rw [← hx₀, heq, one_mul]
    have h2 : x * (u * x * u) = 1 := mul_right_cancel h1
    have h3 : x = u * x * u := ((eq_inv_of_mul_eq_one_right h2).trans hxi).symm
    calc x * u = (u * x * u) * u := by rw [← h3]
      _ = u * x * (u * u) := by group
      _ = u * x := by rw [hu1, mul_one]
  · rw [inv_inv]

theorem lemma126_b
    (S : ZDSetup X Z M) (h : LData c n i) {u : X} (huD : u ∈ c.D)
    (hu2 : orderOf u = 2) (ha : zHull Z M ≤ centralizer ({u} : Set X)) (hns : ¬ Shears Z M u) :
    ∀ u' ∈ deltaSet Z M u, u' ≠ u → centralizer ({u'} : Set X) ≤ M := by
  intro u' hu' hne
  obtain ⟨y₀, hy₀, rfl⟩ := hu'
  have hy₀H : y₀ ∈ zHull Z M := (Subgroup.mem_inf.mp hy₀).2
  have hy₀1 : y₀ ≠ 1 := fun h1 => hne (by rw [h1, one_mul])
  by_contra hFM
  apply hns
  have huM : u ∈ M := (Subgroup.mem_inf.mp huD).1
  have hu1 : u * u = 1 := sec126_involution_mul_self hu2
  obtain ⟨hy₀Z, hy₀M⟩ := h.sec126_mem_Z_of_mem_zHull hy₀H hy₀1
  have hy₀2 : orderOf y₀ = 2 := S.invariant.1 y₀ hy₀Z
  have hy₀s : y₀ * y₀ = 1 := h.sec126_zHull_sq hy₀H
  have hcomm : ∀ x ∈ zHull Z M, x * (y₀ * u) = (y₀ * u) * x := by
    intro x hx
    have h1 : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp (ha hx)
    calc x * (y₀ * u) = (x * y₀) * u := by rw [mul_assoc]
      _ = (y₀ * x) * u := by rw [h.sec126_zHull_comm hx hy₀H]
      _ = y₀ * (x * u) := by rw [mul_assoc]
      _ = y₀ * (u * x) := by rw [h1]
      _ = (y₀ * u) * x := by rw [mul_assoc]
  have hu'1 : y₀ * u ≠ 1 := by
    intro h1
    apply h.sec126_not_mem_zHull S huD hu2
    rw [eq_inv_of_mul_eq_one_right h1]
    exact (zHull Z M).inv_mem hy₀H
  have hFtop : centralizer ({y₀ * u} : Set X) ≠ ⊤ := S.sec126_centralizer_singleton_ne_top hu'1
  have hy₀F : y₀ ∈ centralizer ({y₀ * u} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y₀ hy₀H)
  obtain ⟨b, hbH, hby₀, hb1⟩ := h.sec126_exists_ne y₀ 1
  obtain ⟨hbZ, hbM⟩ := h.sec126_mem_Z_of_mem_zHull hbH hb1
  have hbF : b ∈ centralizer ({y₀ * u} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm b hbH)
  have hne' : (Z ∩ ((centralizer ({y₀ * u} : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty :=
    ⟨y₀, hy₀Z, Subgroup.mem_inf.mpr ⟨hy₀F, hy₀M⟩⟩
  have hns' : ¬ Group.IsSolvable ↥(zHull Z (centralizer ({y₀ * u} : Set X))) :=
    S.not_solvable_zHull_of_ne hFtop hFM ⟨hy₀Z, Subgroup.mem_inf.mpr ⟨hy₀F, hy₀M⟩⟩
      ⟨hbZ, Subgroup.mem_inf.mpr ⟨hbF, hbM⟩⟩ (Ne.symm hby₀)
  obtain ⟨m, j, e, hB⟩ := S.benderSub_exists hFtop hFM hne' hns'
  obtain ⟨g, hg, hgy⟩ := hB.exists_not_commute (y := y₀) (Cor713.mem_zHull_of_mem hy₀Z hy₀F)
    hy₀M hy₀2
  have hgM : g ∈ M := (Subgroup.mem_inf.mp hg).2
  have hgF : g ∈ centralizer ({y₀ * u} : Set X) :=
    Cor713.zHull_le (centralizer ({y₀ * u} : Set X)) (Subgroup.mem_inf.mp hg).1
  have hgc : g * (y₀ * u) = (y₀ * u) * g := Subgroup.mem_centralizer_singleton_iff.mp hgF
  have hgc' : g⁻¹ * (y₀ * u) * g = y₀ * u := by
    calc g⁻¹ * (y₀ * u) * g = g⁻¹ * ((y₀ * u) * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * (y₀ * u)) := by rw [hgc]
      _ = y₀ * u := by group
  have hwH : (g⁻¹ * y₀ * g) * y₀ ∈ zHull Z M :=
    (zHull Z M).mul_mem (h.sec126_conj_mem_zHull hgM hy₀H) hy₀H
  have hx₀ : g⁻¹ * u * g = ((g⁻¹ * y₀ * g) * y₀) * u := by
    calc g⁻¹ * u * g = g⁻¹ * (y₀ * (y₀ * u)) * g := by
          rw [← mul_assoc y₀ y₀ u, hy₀s, one_mul]
      _ = (g⁻¹ * y₀ * g) * (g⁻¹ * (y₀ * u) * g) := by group
      _ = (g⁻¹ * y₀ * g) * (y₀ * u) := by rw [hgc']
      _ = ((g⁻¹ * y₀ * g) * y₀) * u := (mul_assoc (g⁻¹ * y₀ * g) y₀ u).symm
  refine ⟨g⁻¹ * u * g, ⟨(g⁻¹ * y₀ * g) * y₀, Subgroup.mem_inf.mpr ⟨ha hwH, hwH⟩, hx₀⟩, ?_,
    isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩⟩
  intro heq
  apply hgy
  have h1 : ((g⁻¹ * y₀ * g) * y₀) * u = 1 * u := by rw [← hx₀, heq, one_mul]
  have h2 : (g⁻¹ * y₀ * g) * y₀ = 1 := mul_right_cancel h1
  rw [eq_inv_of_mul_eq_one_left h2, inv_eq_of_mul_eq_one_right hy₀s]

end CFSG.GH74.Uniqueness
