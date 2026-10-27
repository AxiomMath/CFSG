module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootComb

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem mr_finite_roots_E6 : {α : Fin 6 → ℤ | IsRoot Tag.E6 α}.Finite := by
  refine (Set.finite_range fun p : WeylGroup Tag.E6 × Fin Tag.E6.rank =>
    p.1 • (Pi.single p.2 1 : Fin Tag.E6.rank → ℤ)).subset ?_
  intro α hα
  obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 (show IsRoot Tag.E6 α from hα)
  exact ⟨(w, j), hwj⟩

theorem mr_pairing_add (l α β : Fin 6 → ℤ) :
    ∑ i, l i * (α + β) i = ∑ i, l i * α i + ∑ i, l i * β i := by
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem mr_pairing_single (l : Fin 6 → ℤ) (i : Fin 6) :
    ∑ j, l j * (Pi.single i 1 : Fin 6 → ℤ) j = l i := by
  simp [Pi.single_apply]

theorem mr_pairing_neg_single (l : Fin 6 → ℤ) (i : Fin 6) :
    ∑ j, l j * (-(Pi.single i 1 : Fin 6 → ℤ)) j = -l i := by
  simp [Pi.single_apply]

theorem mr_E6_simplyLaced : Tag.E6 = .D4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 :=
  Or.inr (Or.inl rfl)

theorem mr_iform_add_add
    (α β : Fin 6 → ℤ) :
    iform (τ := Tag.E6) (α + β) (α + β) =
      iform (τ := Tag.E6) α α + 2 * iform (τ := Tag.E6) α β + iform (τ := Tag.E6) β β :=
  kr_iform_add_add (τ := Tag.E6) α β

theorem exists_max_root_pairing (l : Fin 6 → ℤ) (hl : l ≠ 0) :
    ∃ m : ℤ, 0 < m ∧ (∃ α, IsRoot Tag.E6 α ∧ ∑ i, l i * α i = m) ∧
      ∀ α, IsRoot Tag.E6 α → ∑ i, l i * α i ≤ m := by
  obtain ⟨α₀, hα₀, hmax⟩ := Set.exists_max_image {α : Fin 6 → ℤ | IsRoot Tag.E6 α}
    (fun α => ∑ i, l i * α i) mr_finite_roots_E6
    ⟨(Pi.single (0 : Fin 6) (1 : ℤ) : Fin 6 → ℤ), IsRoot.basis (τ := Tag.E6) (0 : Fin 6)⟩
  obtain ⟨i, hi⟩ : ∃ i, l i ≠ 0 := by
    by_contra! h
    exact hl (funext h)
  have hpos : 0 < ∑ j, l j * α₀ j := by
    rcases hi.lt_or_gt with hneg | hgt
    · have h1 : ∑ j, l j * (-(Pi.single i 1 : Fin 6 → ℤ)) j ≤ ∑ j, l j * α₀ j :=
        hmax (-(Pi.single i 1 : Fin 6 → ℤ)) (IsRoot.neg (IsRoot.basis (τ := Tag.E6) i))
      rw [mr_pairing_neg_single] at h1
      linarith
    · have h1 : ∑ j, l j * (Pi.single i 1 : Fin 6 → ℤ) j ≤ ∑ j, l j * α₀ j :=
        hmax (Pi.single i 1 : Fin 6 → ℤ) (IsRoot.basis (τ := Tag.E6) i)
      rw [mr_pairing_single] at h1
      linarith
  exact ⟨_, hpos, ⟨α₀, hα₀, rfl⟩, fun α hα => hmax α hα⟩

theorem not_isRoot_add_of_max_pairing (l : Fin 6 → ℤ) {m : ℤ} (hm : 0 < m)
    (hmax : ∀ γ, IsRoot Tag.E6 γ → ∑ i, l i * γ i ≤ m) {α β : Fin 6 → ℤ}
    (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β) (hαm : ∑ i, l i * α i = m)
    (hβm : ∑ i, l i * β i = m) : ¬ IsRoot Tag.E6 (α + β) := by
  intro h
  have h1 : ∑ i, l i * (α + β) i ≤ m := hmax (α + β) h
  rw [mr_pairing_add l α β] at h1
  linarith

theorem mr_isRoot_add_of_iform_eq_neg_one
    {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (h : iform (τ := Tag.E6) α β = -1) : IsRoot Tag.E6 (α + β) := by
  have hr := IsRoot.smul hβ (rootReflection (τ := Tag.E6) α)
  rw [kr_rootReflection_smul mr_E6_simplyLaced hα β, h, neg_one_smul, sub_neg_eq_add,
    add_comm] at hr
  exact hr

theorem iform_nonneg_of_max_pairing
    (l : Fin 6 → ℤ) {m : ℤ} (hm : 0 < m)
    (hmax : ∀ γ, IsRoot Tag.E6 γ → ∑ i, l i * γ i ≤ m) {α β : Fin 6 → ℤ}
    (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β) (hαm : ∑ i, l i * α i = m)
    (hβm : ∑ i, l i * β i = m) (hne : α ≠ β) :
    0 ≤ iform (τ := Tag.E6) α β := by
  have hnot := not_isRoot_add_of_max_pairing l hm hmax hα hβ hαm hβm
  have hne0 : α + β ≠ 0 := by
    intro h0
    have h1 : ∑ i, l i * (α + β) i = 0 := by
      rw [h0]
      simp
    rw [mr_pairing_add l α β] at h1
    linarith
  have hpos : 0 < iform (τ := Tag.E6) (α + β) (α + β) := iform_self_pos (τ := Tag.E6) hne0
  rw [mr_iform_add_add α β, kr_iform_self mr_E6_simplyLaced hα,
    kr_iform_self mr_E6_simplyLaced hβ] at hpos
  have hge : -1 ≤ iform (τ := Tag.E6) α β := by omega
  by_contra hneg
  have hx : iform (τ := Tag.E6) α β = -1 := by omega
  exact hnot (mr_isRoot_add_of_iform_eq_neg_one hα hβ hx)

end CFSG.LieType.SeitzGeneration.ExcHighThree
