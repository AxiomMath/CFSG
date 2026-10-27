module

public import CFSG.GH74.GLS.C3.Layer1.BkA7Facts

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG
open CFSG.LieType.SteinbergBR.SmallAlt Equiv Equiv.Perm

theorem model_center : ∀ i : Fin 8, (∀ j : Fin 8, a7P i * a7P j = a7P j * a7P i) → a7P i ≠ 1 →
    a7P i = a7P 1 := by decide +kernel

theorem model_cent6 : ∀ e : Perm (Fin 6),
    (∀ i : Fin 8, decomposeFin.symm (0, e) * a7P i = a7P i * decomposeFin.symm (0, e)) →
    decomposeFin.symm (0, e) = 1 ∨ decomposeFin.symm (0, e) = a7P 1 ∨
      decomposeFin.symm (0, e) = swap 5 6 ∨
      decomposeFin.symm (0, e) = swap 1 3 * swap 2 4 * swap 5 6 := by decide +kernel

theorem model_final2_6 : ∀ e : Perm (Fin 6),
    decomposeFin.symm (0, e) * a7P 1 = a7P 1 * decomposeFin.symm (0, e) →
    decomposeFin.symm (0, e) * swap 5 6 = swap 5 6 * decomposeFin.symm (0, e) →
    decomposeFin.symm (0, e) ^ 4 = 1 := by decide +kernel

theorem model_final3_6 : ∀ e : Perm (Fin 6),
    decomposeFin.symm (0, e) * a7P 1 = a7P 1 * decomposeFin.symm (0, e) →
    decomposeFin.symm (0, e) * (swap 1 3 * swap 2 4 * swap 5 6) =
      (swap 1 3 * swap 2 4 * swap 5 6) * decomposeFin.symm (0, e) →
    decomposeFin.symm (0, e) ^ 4 = 1 := by decide +kernel

theorem fix_c1_c2 : ∀ y : Fin 7, (a7P 1) y = y → (swap 5 6 : Perm (Fin 7)) y = y → y = 0 := by
  decide +kernel

theorem fix_c3 : ∀ y : Fin 7, (swap 1 3 * swap 2 4 * swap 5 6 : Perm (Fin 7)) y = y → y = 0 := by
  decide +kernel

theorem a7P_zero : (a7P 0 : Perm (Fin 7)) = 1 := rfl
theorem a7P_one_fix_zero : (a7P 1 : Perm (Fin 7)) 0 = 0 := by decide +kernel
theorem swap56_fix_zero : (swap 5 6 : Perm (Fin 7)) 0 = 0 := by decide +kernel
theorem c3_fix_zero : (swap 1 3 * swap 2 4 * swap 5 6 : Perm (Fin 7)) 0 = 0 := by decide +kernel

theorem fix_of_comm {τ u : Perm (Fin 7)} (hu : τ * u = u * τ) (hu0 : u 0 = 0)
    (hy : ∀ y, u y = y → y = 0) : τ 0 = 0 := by
  have h := congrArg (fun f : Perm (Fin 7) => f 0) hu
  simp only [Equiv.Perm.mul_apply] at h
  rw [hu0] at h
  exact hy _ h.symm

theorem fix_of_comm2 {τ u v : Perm (Fin 7)} (hu : τ * u = u * τ) (hv : τ * v = v * τ)
    (hu0 : u 0 = 0) (hv0 : v 0 = 0) (hy : ∀ y, u y = y → v y = y → y = 0) : τ 0 = 0 := by
  have h1 := congrArg (fun f : Perm (Fin 7) => f 0) hu
  have h2 := congrArg (fun f : Perm (Fin 7) => f 0) hv
  simp only [Equiv.Perm.mul_apply] at h1 h2
  rw [hu0] at h1
  rw [hv0] at h2
  exact hy _ h1.symm h2.symm

theorem comm_conj_perm {α : Type*} [Group α] (C u v : α) (h : u * v = v * u) :
    (C⁻¹ * u * C) * (C⁻¹ * v * C) = (C⁻¹ * v * C) * (C⁻¹ * u * C) := by
  calc (C⁻¹ * u * C) * (C⁻¹ * v * C) = C⁻¹ * (u * v) * C := by group
    _ = C⁻¹ * (v * u) * C := by rw [h]
    _ = (C⁻¹ * v * C) * (C⁻¹ * u * C) := by group

theorem alt7_odd_centralizer {X : Subgroup (alternatingGroup (Fin 7))} (hX : Nat.card ↥X = 8)
    {ρ g σ : Perm (Fin 7)} (hρX : ∃ r ∈ X, (r : Perm (Fin 7)) = ρ) (hρ1 : ρ ≠ 1)
    (hρc : ∀ y ∈ X, (y : Perm (Fin 7)) * ρ = ρ * (y : Perm (Fin 7)))
    (hgc : ∀ y ∈ X, g * (y : Perm (Fin 7)) = (y : Perm (Fin 7)) * g)
    (hgX : ∀ y ∈ X, (y : Perm (Fin 7)) ≠ g) (hσρ : σ * ρ = ρ * σ) (hσg : σ * g = g * σ) :
    σ ^ 4 = 1 := by
  obtain ⟨c, hcY, hcX⟩ := exists_conj_model hX
  set C : Perm (Fin 7) := (c : Perm (Fin 7)) with hC
  have hmodel : ∀ j : Fin 8, ∃ y ∈ X, (y : Perm (Fin 7)) = C * a7P j * C⁻¹ := by
    intro j
    have hyj : (⟨a7P j, (Equiv.Perm.mem_alternatingGroup).2 (a7P_sign j)⟩ :
        alternatingGroup (Fin 7)) ∈ finSubgroup a7P a7P_mul a7P_inv a7P_one := ⟨j, rfl⟩
    refine ⟨c * ⟨a7P j, (Equiv.Perm.mem_alternatingGroup).2 (a7P_sign j)⟩ * c⁻¹, hcY _ hyj, ?_⟩
    simp [hC]
  obtain ⟨r, hrX, hrρ⟩ := hρX
  obtain ⟨i, hi⟩ := hcX r hrX
  have hρ'i : a7P i = C⁻¹ * ρ * C := by
    rw [← hrρ]
    have := hi
    simpa [hC] using this
  have hρ'c : ∀ j : Fin 8, a7P j * (C⁻¹ * ρ * C) = (C⁻¹ * ρ * C) * a7P j := by
    intro j
    obtain ⟨y, hyX, hy⟩ := hmodel j
    have h1 := hρc y hyX
    rw [hy] at h1
    calc a7P j * (C⁻¹ * ρ * C) = C⁻¹ * ((C * a7P j * C⁻¹) * ρ) * C := by group
      _ = C⁻¹ * (ρ * (C * a7P j * C⁻¹)) * C := by rw [h1]
      _ = (C⁻¹ * ρ * C) * a7P j := by group
  have hρ'1 : a7P i ≠ 1 := by
    rw [hρ'i]
    intro h1
    apply hρ1
    have : ρ = C * (C⁻¹ * ρ * C) * C⁻¹ := by group
    rw [this, h1]
    group
  have hρ'eq : C⁻¹ * ρ * C = a7P 1 := by
    rw [← hρ'i]
    refine model_center i (fun j => ?_) hρ'1
    have := hρ'c j
    rw [← hρ'i] at this
    exact this.symm
  have hg'c : ∀ j : Fin 8, (C⁻¹ * g * C) * a7P j = a7P j * (C⁻¹ * g * C) := by
    intro j
    obtain ⟨y, hyX, hy⟩ := hmodel j
    have h1 := hgc y hyX
    rw [hy] at h1
    calc (C⁻¹ * g * C) * a7P j = C⁻¹ * (g * (C * a7P j * C⁻¹)) * C := by group
      _ = C⁻¹ * ((C * a7P j * C⁻¹) * g) * C := by rw [h1]
      _ = a7P j * (C⁻¹ * g * C) := by group
  have hg'not : ∀ j : Fin 8, C⁻¹ * g * C ≠ a7P j := by
    intro j hj
    obtain ⟨y, hyX, hy⟩ := hmodel j
    apply hgX y hyX
    rw [hy, ← hj]
    group
  have hg'0 : (C⁻¹ * g * C) 0 = 0 := by
    have h4 := congrArg (fun f : Perm (Fin 7) => f 0) (hg'c 4)
    simp only [Equiv.Perm.mul_apply] at h4
    rw [a7P_fix_zero 4] at h4
    exact a7P_four_fix _ h4.symm
  obtain ⟨e, he⟩ := perm_zero_decomp (C⁻¹ * g * C) hg'0
  have hg'cases : C⁻¹ * g * C = swap 5 6 ∨ C⁻¹ * g * C = swap 1 3 * swap 2 4 * swap 5 6 := by
    have h1 : decomposeFin.symm (0, e) = 1 ∨ decomposeFin.symm (0, e) = a7P 1 ∨
        decomposeFin.symm (0, e) = swap 5 6 ∨
        decomposeFin.symm (0, e) = swap 1 3 * swap 2 4 * swap 5 6 :=
      model_cent6 e (fun i => by rw [← he]; exact hg'c i)
    rcases h1 with h1 | h1 | h1 | h1
    · exact absurd (he.trans (h1.trans a7P_zero.symm)) (hg'not 0)
    · exact absurd (he.trans h1) (hg'not 1)
    · exact Or.inl (he.trans h1)
    · exact Or.inr (he.trans h1)
  have hσ'ρ : (C⁻¹ * σ * C) * a7P 1 = a7P 1 * (C⁻¹ * σ * C) := by
    rw [← hρ'eq]
    exact comm_conj_perm C σ ρ hσρ
  have hσ'g : (C⁻¹ * σ * C) * (C⁻¹ * g * C) = (C⁻¹ * g * C) * (C⁻¹ * σ * C) :=
    comm_conj_perm C σ g hσg
  have hσ'4 : (C⁻¹ * σ * C) ^ 4 = 1 := by
    rcases hg'cases with h1 | h1
    · rw [h1] at hσ'g
      have hz : (C⁻¹ * σ * C) 0 = 0 :=
        fix_of_comm2 hσ'ρ hσ'g a7P_one_fix_zero swap56_fix_zero fix_c1_c2
      obtain ⟨e', he'⟩ := perm_zero_decomp _ hz
      rw [he'] at hσ'ρ hσ'g ⊢
      exact model_final2_6 e' hσ'ρ hσ'g
    · rw [h1] at hσ'g
      have hz : (C⁻¹ * σ * C) 0 = 0 := fix_of_comm hσ'g c3_fix_zero fix_c3
      obtain ⟨e', he'⟩ := perm_zero_decomp _ hz
      rw [he'] at hσ'ρ hσ'g ⊢
      exact model_final3_6 e' hσ'ρ hσ'g
  have e1 : σ = C * (C⁻¹ * σ * C) * C⁻¹ := by group
  rw [e1, conj_pow, hσ'4]
  group

end CFSG.GH74.GLS.C3.Layer1.Bk
