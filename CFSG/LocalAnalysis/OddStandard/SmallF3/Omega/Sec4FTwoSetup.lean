module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FConjA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec4FTwo (A P : Subgroup G) (x : G) : Prop where
  AP : A ≤ P
  PM : P ≤ normalizer (A : Set G)
  P2 : IsPGroup 2 ↥P
  max : ∀ P' : Subgroup G, P ≤ P' → P' ≤ normalizer (A : Set G) → IsPGroup 2 ↥P' → P' = P
  xP : x ∈ normalizer (P : Set G)
  x2 : x * x ∈ P
  T2 : IsPGroup 2 ↥(P ⊔ zpowers x)
  xM : x ∉ normalizer (A : Set G)

@[expose] def sec4FD (t : G) (φ : (Fin 7 → ZMod 2) → G) (x : G) (c : Option (Fin 7)) : G :=
  x⁻¹ * sec4MPt t φ c * x

@[expose] def sec4FR (t : G) (φ : (Fin 7 → ZMod 2) → G) (x : G) (a c : Option (Fin 7)) : Prop :=
  ¬ (sec4MPt t φ a * sec4FD t φ x c = sec4FD t φ x c * sec4MPt t φ a)

variable [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B P : Subgroup G} {x : G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem sec4F_swap_eq_of_iff {Ω : Type} [DecidableEq Ω] {u v a b : Ω} (huv : u ≠ v)
    (hab : a ≠ b) (h : ∀ g : Ω, (g = u ∨ g = v) ↔ (g = a ∨ g = b)) :
    Equiv.swap u v = Equiv.swap a b := by
  have hu : u = a ∨ u = b := (h u).mp (Or.inl rfl)
  have hv : v = a ∨ v = b := (h v).mp (Or.inr rfl)
  rcases hu with hua | hub
  · rcases hv with hva | hvb
    · exact absurd (hua.trans hva.symm) huv
    · rw [hua, hvb]
  · rcases hv with hva | hvb
    · rw [hub, hva, Equiv.swap_comm]
    · exact absurd (hub.trans hvb.symm) huv

theorem Sec4FSetup.d_mem_P (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x)
    (c : Option (Fin 7)) : sec4FD t φ x c ∈ P := by
  have hpP : sec4MPt t φ c ∈ P := hT.AP (sec4MPt_mem_A h.data c)
  have h1 := (Subgroup.mem_set_normalizer_iff.mp (inv_mem hT.xP) (sec4MPt t φ c)).mp hpP
  simpa [sec4FD, inv_inv] using h1

theorem Sec4FSetup.d_conj (h : Sec4FSetup t L S z A B φ) (c : Option (Fin 7)) :
    ∃ g : G, sec4FD t φ x c = g⁻¹ * t * g := by
  obtain ⟨k, hk⟩ := (conj_iff_mem_conjClassIn_top (t := t)).mpr (h.pt_mem_conj c)
  exact ⟨k * x, by rw [sec4FD, hk]; group⟩

theorem Sec4FSetup.d_sq (h : Sec4FSetup t L S z A B φ) (c : Option (Fin 7)) :
    sec4FD t φ x c * sec4FD t φ x c = 1 := by
  calc sec4FD t φ x c * sec4FD t φ x c
      = x⁻¹ * (sec4MPt t φ c * sec4MPt t φ c) * x := by simp only [sec4FD]; group
    _ = 1 := by rw [h.A_sq (sec4MPt_mem_A h.data c)]; group

theorem Sec4FSetup.d_inj (h : Sec4FSetup t L S z A B φ) :
    Function.Injective (sec4FD t φ x) := by
  intro c c' hcc
  apply h.pt_injective
  simp only [sec4FD] at hcc
  exact mul_left_cancel (mul_right_cancel hcc)

theorem Sec4FSetup.d_comm (h : Sec4FSetup t L S z A B φ) (c c' : Option (Fin 7)) :
    sec4FD t φ x c * sec4FD t φ x c' = sec4FD t φ x c' * sec4FD t φ x c := by
  have hcc := h.A_comm (sec4MPt_mem_A h.data c) (sec4MPt_mem_A h.data c')
  calc sec4FD t φ x c * sec4FD t φ x c'
      = x⁻¹ * (sec4MPt t φ c * sec4MPt t φ c') * x := by simp only [sec4FD]; group
    _ = x⁻¹ * (sec4MPt t φ c' * sec4MPt t φ c) * x := by rw [hcc]
    _ = sec4FD t φ x c' * sec4FD t φ x c := by simp only [sec4FD]; group

theorem Sec4FSetup.d_swap (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x)
    (c : Option (Fin 7)) :
    ∃ u v : Option (Fin 7), u ≠ v ∧ Sec4MRealizes t φ (sec4FD t φ x c) (Equiv.swap u v) := by
  have hdM : sec4FD t φ x c ∈ normalizer (A : Set G) := hT.PM (h.d_mem_P hT c)
  have hdconj : ∃ g : G, sec4FD t φ x c = g⁻¹ * t * g := h.d_conj c
  rcases h.kcases hdconj hdM with ⟨p, hp⟩ | hswap
  · exfalso
    have hdA : sec4FD t φ x c ∈ A := by rw [hp]; exact sec4MPt_mem_A h.data p
    have hg : CFSG.conjugate A x ≤ P := by
      intro e he
      have heA : x * e * x⁻¹ ∈ A := (mem_conjugate_iff A x e).mp he
      have h1 :=
        (Subgroup.mem_set_normalizer_iff.mp (inv_mem hT.xP) (x * e * x⁻¹)).mp (hT.AP heA)
      rw [inv_inv] at h1
      rwa [show x⁻¹ * (x * e * x⁻¹) * x = e by group] at h1
    have hne : CFSG.conjugate A x ≠ A :=
      fun hAx => hT.xM (mem_normalizer_of_conjugate_eq hAx)
    have he : sec4FD t φ x c ∈ CFSG.conjugate A x := by
      have hx : x * sec4FD t φ x c * x⁻¹ = sec4MPt t φ c := by rw [sec4FD]; group
      rw [mem_conjugate_iff, hx]
      exact sec4MPt_mem_A h.data c
    exact h.conjA_disjoint hT.PM hg hne he hdconj hdA
  · exact hswap

theorem Sec4FSetup.pt_d (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x)
    (a : Option (Fin 7)) :
    ∃ u v : Option (Fin 7), u ≠ v ∧ ∀ c : Option (Fin 7),
      sec4MPt t φ a * sec4FD t φ x c * (sec4MPt t φ a)⁻¹ = sec4FD t φ x (Equiv.swap u v c) := by
  obtain ⟨ρ, hρ⟩ := h.exists_realizes (hT.PM hT.x2)
  have hxq : ∀ q : Option (Fin 7),
      x * sec4MPt t φ q * x⁻¹ = sec4FD t φ x (ρ q) := by
    intro q
    rw [sec4FD, ← hρ q]
    group
  have hxa : x * sec4FD t φ x a * x⁻¹ = sec4MPt t φ a := by
    rw [sec4FD]; group
  obtain ⟨u, v, huv, hr⟩ := h.d_swap hT a
  refine ⟨ρ u, ρ v, fun hne => huv (ρ.injective hne), fun c => ?_⟩
  have hdc : sec4FD t φ x c = x * sec4MPt t φ (ρ.symm c) * x⁻¹ := by
    have h1 : sec4FD t φ x (ρ (ρ.symm c)) = x * sec4MPt t φ (ρ.symm c) * x⁻¹ :=
      (hxq (ρ.symm c)).symm
    rwa [ρ.apply_symm_apply c] at h1
  calc sec4MPt t φ a * sec4FD t φ x c * (sec4MPt t φ a)⁻¹
      = (x * sec4FD t φ x a * x⁻¹) * (x * sec4MPt t φ (ρ.symm c) * x⁻¹)
          * (x * sec4FD t φ x a * x⁻¹)⁻¹ := by rw [← hxa, hdc]
    _ = x * (sec4FD t φ x a * sec4MPt t φ (ρ.symm c) * (sec4FD t φ x a)⁻¹) * x⁻¹ := by
          group
    _ = x * sec4MPt t φ (Equiv.swap u v (ρ.symm c)) * x⁻¹ := by rw [hr (ρ.symm c)]
    _ = sec4FD t φ x (ρ (Equiv.swap u v (ρ.symm c))) := hxq (Equiv.swap u v (ρ.symm c))
    _ = sec4FD t φ x (Equiv.swap (ρ u) (ρ v) c) := by
          rw [Equiv.swap_apply_apply ρ u v]
          rfl

end CFSG.OddStandard.SmallF3.Omega
