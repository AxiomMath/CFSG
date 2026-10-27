module

public import CFSG.CGT.PushingUpLit.CGT6.TwoFivePerm
public import CFSG.CGT.PushingUpLit.CGT6.TwoFiveTv
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.ComponentClassification.OutcomeLocal Module Equiv

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

structure TwoFiveHyp (ρ : G →* LinearMap.GeneralLinearGroup (ZMod 2) V) (D : Set G) {m : ℕ}
    (σ : Perm (Fin (2 * m + 1)) →* G) : Prop where
  ρ_inj : Function.Injective ρ
  σ_inj : Function.Injective σ
  isTransvection : ∀ d ∈ D, IsF2Transvection (ρ d)
  swap_mem : ∀ i j, i ≠ j → σ (swap i j) ∈ D
  conj_swap : ∀ P : Subgroup G, IsPGroup 2 P →
    ∃ c : G ≃* G, ∀ d ∈ D, d ∈ P → ∃ i j, i ≠ j ∧ c d = σ (swap i j)

namespace TwoFiveHyp

variable {ρ : G →* LinearMap.GeneralLinearGroup (ZMod 2) V} {D : Set G} {m : ℕ}
  {σ : Perm (Fin (2 * m + 1)) →* G}

theorem exists_data (h : TwoFiveHyp ρ D σ) {d : G} (hd : d ∈ D) :
    ∃ (φ : Dual (ZMod 2) V) (a : V), φ ≠ 0 ∧ a ≠ 0 ∧ IsTv (ρ d) φ a :=
  exists_isTv_of_isF2Transvection (h.isTransvection d hd)

theorem mul_self_eq_one (h : TwoFiveHyp ρ D σ) {d : G} (hd : d ∈ D) : d * d = 1 := by
  obtain ⟨φ, a, -, -, hg⟩ := h.exists_data hd
  apply h.ρ_inj
  rw [map_mul, hg.mul_self, map_one]

theorem comm_of_pow_four (h : TwoFiveHyp ρ D σ) {d d' : G} (hd : d ∈ D)
    (hd' : d' ∈ D) (h4 : (d * d') ^ 4 = 1) : d * d' = d' * d := by
  obtain ⟨c, hc⟩ := h.conj_swap _ (isPGroup_closure_pair_of_dihedral (h.mul_self_eq_one hd)
    (h.mul_self_eq_one hd') h4)
  obtain ⟨i, j, hij, e1⟩ := hc d hd (Subgroup.subset_closure (by simp))
  obtain ⟨k, l, hkl, e2⟩ := hc d' hd' (Subgroup.subset_closure (by simp))
  have h4' : (σ (swap i j) * σ (swap k l)) ^ 4 = 1 := by
    rw [← e1, ← e2, ← map_mul, ← map_pow, h4, map_one]
  have h4'' : (swap i j * swap k l) ^ 4 = 1 := by
    apply h.σ_inj
    rw [map_pow, map_mul, map_one]
    exact h4'
  have hcomm := swap_comm_of_pow_four hij hkl h4''
  have hcomm' : σ (swap i j) * σ (swap k l) = σ (swap k l) * σ (swap i j) := by
    rw [← map_mul, ← map_mul, hcomm]
  rw [← e1, ← e2, ← map_mul, ← map_mul] at hcomm'
  exact c.injective hcomm'

theorem three_trans (h : TwoFiveHyp ρ D σ) {d d' : G} (hd : d ∈ D) (hd' : d' ∈ D)
    {φ ψ : Dual (ZMod 2) V} {a c : V} (hg : IsTv (ρ d) φ a) (hg' : IsTv (ρ d') ψ c)
    (hnc : d * d' ≠ d' * d) : φ c = 1 ∧ ψ a = 1 := by
  rcases zmod2_eq_zero_or_one (φ c) with h1 | h1 <;> rcases zmod2_eq_zero_or_one (ψ a) with h2 | h2
  · exfalso
    apply hnc
    apply h.ρ_inj
    rw [map_mul, map_mul]
    exact hg.comm_of_apply_eq_zero hg' h1 h2
  · exfalso
    have h4 : (ρ d' * ρ d) ^ 4 = 1 := hg'.pow_four_of_dihedral hg h2 h1
    have h4' : (d' * d) ^ 4 = 1 := by
      apply h.ρ_inj
      rw [map_pow, map_mul, map_one]
      exact h4
    exact hnc (h.comm_of_pow_four hd' hd h4').symm
  · exfalso
    have h4 : (ρ d * ρ d') ^ 4 = 1 := hg.pow_four_of_dihedral hg' h1 h2
    have h4' : (d * d') ^ 4 = 1 := by
      apply h.ρ_inj
      rw [map_pow, map_mul, map_one]
      exact h4
    exact hnc (h.comm_of_pow_four hd hd' h4')
  · exact ⟨h1, h2⟩

theorem card_commuting_le (h : TwoFiveHyp ρ D σ) (C : Finset G)
    (hCD : ∀ x ∈ C, x ∈ D) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) : C.card ≤ m := by
  classical
  have hP := isPGroup_closure_of_commuting_involutions (C := (C : Set G))
    (fun x hx => h.mul_self_eq_one (hCD x hx)) (fun x hx y hy => hC x hx y hy)
  obtain ⟨c, hc⟩ := h.conj_swap _ hP
  have hsw : ∀ x ∈ C, ∃ i j, i ≠ j ∧ c x = σ (swap i j) := fun x hx =>
    hc x (hCD x hx) (Subgroup.subset_closure hx)
  let S : Finset (Perm (Fin (2 * m + 1))) := Finset.univ.filter fun s => σ s ∈ C.image c
  have hS : ∀ s ∈ S, ∃ x ∈ C, σ s = c x := fun s hs => by
    obtain ⟨x, hx, e⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hs).2
    exact ⟨x, hx, e.symm⟩
  have hSsw : ∀ s ∈ S, ∃ i j, i ≠ j ∧ s = swap i j := fun s hs => by
    obtain ⟨x, hx, e⟩ := hS s hs
    obtain ⟨i, j, hij, e'⟩ := hsw x hx
    exact ⟨i, j, hij, h.σ_inj (e.trans e')⟩
  have hSc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := fun s hs t ht => by
    obtain ⟨x, hx, ex⟩ := hS s hs
    obtain ⟨y, hy, ey⟩ := hS t ht
    apply h.σ_inj
    rw [map_mul, map_mul, ex, ey, ← map_mul, ← map_mul, hC x hx y hy]
  have hcard : S.card = C.card := by
    have h1 : S.image σ = C.image c := by
      ext z
      constructor
      · intro hz
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hz
        exact (Finset.mem_filter.1 hs).2
      · intro hz
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
        obtain ⟨i, j, hij, e⟩ := hsw x hx
        refine Finset.mem_image.2 ⟨swap i j, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, e.symm⟩
        rw [← e]
        exact Finset.mem_image_of_mem c hx
    rw [← Finset.card_image_of_injective S h.σ_inj, h1, Finset.card_image_of_injective _ c.injective]
  have := two_mul_card_le_of_commute S hSsw hSc
  omega

theorem no_three (h : TwoFiveHyp ρ D σ) {d : G} (hd : d ∈ D)
    (i j k : Fin (2 * m + 1)) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    d * σ (swap i j) = σ (swap i j) * d ∨ d * σ (swap j k) = σ (swap j k) * d ∨
      d * σ (swap i k) = σ (swap i k) * d := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have h1D := h.swap_mem i j hij
  have h2D := h.swap_mem j k hjk
  have h3D := h.swap_mem i k hik
  obtain ⟨φ, a, -, -, hg⟩ := h.exists_data hd
  obtain ⟨ψ₁, c₁, -, -, hg₁⟩ := h.exists_data h1D
  obtain ⟨ψ₂, c₂, -, -, hg₂⟩ := h.exists_data h2D
  obtain ⟨ψ₃, c₃, hψ₃, hc₃, hg₃⟩ := h.exists_data h3D
  have e1 := (h.three_trans hd h1D hg hg₁ h1).1
  have e2 := (h.three_trans hd h2D hg hg₂ h2).1
  have e3 := (h.three_trans hd h3D hg hg₃ h3).1
  have hnc : σ (swap i j) * σ (swap j k) ≠ σ (swap j k) * σ (swap i j) := by
    intro hc
    rw [← map_mul, ← map_mul] at hc
    exact swap_mul_swap_ne_comm' hij hjk hik (h.σ_inj hc)
  obtain ⟨f1, f2⟩ := h.three_trans h1D h2D hg₁ hg₂ hnc
  have hconj := hg₁.conj_dihedral hg₂ f1 f2
  have hρ : ρ (σ (swap i j)) * ρ (σ (swap j k)) * ρ (σ (swap i j)) = ρ (σ (swap i k)) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, swap_mul_swap_mul_swap_eq hjk hik]
  rw [hρ] at hconj
  have hu := hg₃.unique hconj hψ₃ hc₃
  rw [hu.2, map_add] at e3
  rw [e1, e2] at e3
  exact absurd e3 (by decide)

theorem eq_swap (h : TwoFiveHyp ρ D σ) {d : G} (hd : d ∈ D) :
    ∃ i j, i ≠ j ∧ d = σ (swap i j) := by
  classical
  obtain ⟨S, hScard, hS, hSc⟩ := exists_swap_matching (n := 2 * m + 1) (m := m) rfl
    (fun i j => d * σ (swap i j) = σ (swap i j) * d) (fun i j k hij hjk hik =>
      h.no_three hd i j k hij hjk hik)
  by_cases hdin : d ∈ S.image σ
  · obtain ⟨s, hs, hsd⟩ := Finset.mem_image.1 hdin
    obtain ⟨i, j, hij, -, rfl⟩ := hS s hs
    exact ⟨i, j, hij, hsd.symm⟩
  · exfalso
    have hcard : (insert d (S.image σ)).card = m + 1 := by
      rw [Finset.card_insert_of_notMem hdin, Finset.card_image_of_injective _ h.σ_inj, hScard]
    have hle := h.card_commuting_le (insert d (S.image σ)) ?_ ?_
    · omega
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hd
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨i, j, hij, -, rfl⟩ := hS s hs
        exact h.swap_mem i j hij
    · intro x hx y hy
      rcases Finset.mem_insert.1 hx with hxd | hx'
      · rcases Finset.mem_insert.1 hy with hyd | hy'
        · rw [hxd, hyd]
        · rw [hxd]
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy'
          obtain ⟨i, j, hij, hE, rfl⟩ := hS t ht
          exact hE
      · rcases Finset.mem_insert.1 hy with hyd | hy'
        · rw [hyd]
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx'
          obtain ⟨i, j, hij, hE, rfl⟩ := hS s hs
          exact hE.symm
        · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx'
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy'
          rw [← map_mul, ← map_mul, hSc s hs t ht]

theorem surjective (h : TwoFiveHyp ρ D σ) (hgen : Subgroup.closure D = ⊤) :
    Function.Surjective σ := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
  intro d hd
  obtain ⟨i, j, -, rfl⟩ := h.eq_swap hd
  exact ⟨swap i j, rfl⟩

end TwoFiveHyp

theorem twoFive_surjective' {ρ : G →* LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hρ : Function.Injective ρ) {D : Set G} (hDtv : ∀ d ∈ D, IsF2Transvection (ρ d))
    (hDgen : Subgroup.closure D = ⊤) {m : ℕ} (σ : Perm (Fin (2 * m + 1)) →* G)
    (hσ : Function.Injective σ) (hσD : ∀ i j, i ≠ j → σ (swap i j) ∈ D)
    (hconj : ∀ P : Subgroup G, IsPGroup 2 P →
      ∃ c : G ≃* G, ∀ d ∈ D, d ∈ P → ∃ i j, i ≠ j ∧ c d = σ (swap i j)) :
    Function.Surjective σ :=
  TwoFiveHyp.surjective ⟨hρ, hσ, hDtv, hσD, hconj⟩ hDgen

end CFSG.CGT.PushingUpLit.CGT6
