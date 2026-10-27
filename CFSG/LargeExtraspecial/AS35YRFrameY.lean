module

public import CFSG.LargeExtraspecial.AS35YRFrameB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal

namespace AS35YR

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

namespace Frame

variable (F : Frame q)

theorem tau_one (v : V) : F.tau 1 v = 0 := by
  rw [tau_def]
  simp

theorem tau_t_c : F.tau F.t F.c = 0 := by
  rw [tau_def, F.t_apply, polar_comm q F.c F.a, F.ac, polar_comm q F.c F.b, F.bc]
  simp [F.proj_a]

variable {F}

theorem tau_inv {p : V ≃ₗ[ZMod 2] V} (hp : F.InU p) (hpi : F.InU p⁻¹) (v : V) :
    F.tau p⁻¹ v = F.tau p v := by
  have h := tau_mul hp hpi v
  rw [mul_inv_cancel, tau_one] at h
  calc F.tau p⁻¹ v = F.tau p v + (F.tau p v + F.tau p⁻¹ v) := by
        rw [← add_assoc, add_self_YR, zero_add]
    _ = F.tau p v := by rw [← h, add_zero]

structure RadHyp (F : Frame q) (P : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  inU : ∀ p ∈ P, F.InU p
  s₁_conj : ∀ p ∈ P, F.s₁ * p * F.s₁⁻¹ ∈ P
  s₂_conj : ∀ p ∈ P, F.s₂ * p * F.s₂⁻¹ ∈ P
  center : ∀ p ∈ P, (∀ p' ∈ P, p * p' = p' * p) → p = 1 ∨ p = F.t

@[expose] def Y (F : Frame q) (P : Subgroup (V ≃ₗ[ZMod 2] V)) (hU : ∀ p ∈ P, F.InU p) :
    Submodule (ZMod 2) V where
  carrier := {y | ∃ p ∈ P, F.tau p F.c = y ∧ F.tau p F.c' = 0}
  add_mem' := by
    rintro _ _ ⟨p₁, hp₁, rfl, h₁⟩ ⟨p₂, hp₂, rfl, h₂⟩
    refine ⟨p₁ * p₂, mul_mem hp₁ hp₂, tau_mul (hU _ hp₁) (hU _ hp₂) _, ?_⟩
    rw [tau_mul (hU _ hp₁) (hU _ hp₂), h₁, h₂, add_zero]
  zero_mem' := ⟨1, one_mem _, F.tau_one _, F.tau_one _⟩
  smul_mem' := by
    rintro x _ ⟨p, hp, rfl, h⟩
    rcases zmod2_cases_YR x with rfl | rfl
    · exact ⟨1, one_mem _, by rw [F.tau_one, zero_smul], F.tau_one _⟩
    · exact ⟨p, hp, by rw [one_smul], h⟩

namespace RadHyp

variable {P : Subgroup (V ≃ₗ[ZMod 2] V)} (h : F.RadHyp P)
include h

theorem exists_zero_left {y : V} (hy : y ∈ F.Y P h.inU) :
    ∃ p ∈ P, F.tau p F.c = 0 ∧ F.tau p F.c' = y := by
  obtain ⟨r, hr, hrc, hrc'⟩ := hy
  obtain ⟨hU₁, h₁c, h₁c'⟩ := tau_conj_s₁ (h.inU r hr)
  have hm := h.s₁_conj r hr
  refine ⟨F.s₁ * r * F.s₁⁻¹ * r⁻¹, mul_mem hm (inv_mem hr), ?_, ?_⟩
  · rw [tau_mul hU₁ (h.inU _ (inv_mem hr)), tau_inv (h.inU r hr) (h.inU _ (inv_mem hr)), h₁c,
      add_self_YR]
  · rw [tau_mul hU₁ (h.inU _ (inv_mem hr)), tau_inv (h.inU r hr) (h.inU _ (inv_mem hr)), h₁c',
      hrc', hrc, zero_add, add_zero]

theorem tau_mem_Y {p : V ≃ₗ[ZMod 2] V} (hp : p ∈ P) :
    F.tau p F.c ∈ F.Y P h.inU ∧ F.tau p F.c' ∈ F.Y P h.inU := by
  have hU := h.inU p hp
  have hpi := h.inU _ (inv_mem hp)
  obtain ⟨hU₂, h₂c, h₂c'⟩ := tau_conj_s₂ hU
  have hm₂ := h.s₂_conj p hp
  have hY₂ : F.tau p F.c' ∈ F.Y P h.inU := by
    refine ⟨F.s₂ * p * F.s₂⁻¹ * p⁻¹, mul_mem hm₂ (inv_mem hp), ?_, ?_⟩
    · rw [tau_mul hU₂ hpi, tau_inv hU hpi, h₂c, add_comm (F.tau p F.c) (F.tau p F.c'), add_assoc,
        add_self_YR, add_zero]
    · rw [tau_mul hU₂ hpi, tau_inv hU hpi, h₂c', add_self_YR]
  refine ⟨?_, hY₂⟩
  obtain ⟨hU₁, h₁c, h₁c'⟩ := tau_conj_s₁ hU
  have hm₁ := h.s₁_conj p hp
  set r := F.s₁ * p * F.s₁⁻¹ * p⁻¹ with hr
  have hrP : r ∈ P := mul_mem hm₁ (inv_mem hp)
  have hrU := h.inU r hrP
  have hrc : F.tau r F.c = 0 := by
    rw [hr, tau_mul hU₁ hpi, tau_inv hU hpi, h₁c, add_self_YR]
  have hrc' : F.tau r F.c' = F.tau p F.c := by
    rw [hr, tau_mul hU₁ hpi, tau_inv hU hpi, h₁c', add_comm (F.tau p F.c') (F.tau p F.c),
      add_assoc, add_self_YR, add_zero]
  obtain ⟨hU₃, h₃c, h₃c'⟩ := tau_conj_s₂ hrU
  have hm₃ := h.s₂_conj r hrP
  refine ⟨F.s₂ * r * F.s₂⁻¹ * r⁻¹, mul_mem hm₃ (inv_mem hrP), ?_, ?_⟩
  · rw [tau_mul hU₃ (h.inU _ (inv_mem hrP)), tau_inv hrU (h.inU _ (inv_mem hrP)), h₃c, hrc,
      hrc', zero_add, add_zero]
  · rw [tau_mul hU₃ (h.inU _ (inv_mem hrP)), tau_inv hrU (h.inU _ (inv_mem hrP)), h₃c',
      add_self_YR]

theorem exists_tau_eq {y₁ y₂ : V} (hy₁ : y₁ ∈ F.Y P h.inU) (hy₂ : y₂ ∈ F.Y P h.inU) :
    ∃ p ∈ P, F.tau p F.c = y₁ ∧ F.tau p F.c' = y₂ := by
  obtain ⟨p₁, hp₁, h₁c, h₁c'⟩ := hy₁
  obtain ⟨p₂, hp₂, h₂c, h₂c'⟩ := h.exists_zero_left hy₂
  refine ⟨p₁ * p₂, mul_mem hp₁ hp₂, ?_, ?_⟩
  · rw [tau_mul (h.inU _ hp₁) (h.inU _ hp₂), h₁c, h₂c, add_zero]
  · rw [tau_mul (h.inU _ hp₁) (h.inU _ hp₂), h₁c', h₂c', zero_add]

theorem eq_zero_of_polar_eq_zero {y : V} (hy : y ∈ F.Y P h.inU)
    (hperp : ∀ y' ∈ F.Y P h.inU, polar q y y' = 0) : y = 0 := by
  obtain ⟨p₁, hp₁, h₁c, h₁c'⟩ := hy
  have hcen : ∀ p' ∈ P, p₁ * p' = p' * p₁ := by
    intro p' hp'
    refine commute_of_polar (h.inU _ hp₁) (h.inU _ hp') ?_
    rw [h₁c', polar_zero_right, h₁c, hperp _ (h.tau_mem_Y hp').2]
  rcases h.center p₁ hp₁ hcen with rfl | rfl
  · rw [← h₁c, F.tau_one]
  · rw [← h₁c, F.tau_t_c]

theorem exists_ne_zero_mem_Y {p : V ≃ₗ[ZMod 2] V} (hp : p ∈ P) (hp1 : p ≠ 1) (hpt : p ≠ F.t) :
    ∃ y ∈ F.Y P h.inU, y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 := hcon _ (h.tau_mem_Y hp).1
  have h2 := hcon _ (h.tau_mem_Y hp).2
  rcases eq_one_or_eq_t (h.inU p hp) h1 h2 with h' | h'
  · exact hp1 h'
  · exact hpt h'

theorem apply_mem_Y {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (ga : g F.a = F.a) (gb : g F.b = F.b) (gc : g F.c = F.c) (gc' : g F.c' = F.c')
    (hgP : ∀ p ∈ P, g * p * g⁻¹ ∈ P) {y : V} (hy : y ∈ F.Y P h.inU) : g y ∈ F.Y P h.inU := by
  obtain ⟨p, hp, hpc, hpc'⟩ := hy
  obtain ⟨-, hτ⟩ := tau_conj_of_fix hg ga gb gc gc' (h.inU p hp)
  refine ⟨g * p * g⁻¹, hgP p hp, ?_, ?_⟩
  · rw [hτ _ gc, hpc]
  · rw [hτ _ gc', hpc', map_zero]

theorem polar_of_mem_Y {y : V} (hy : y ∈ F.Y P h.inU) :
    polar q y F.a = 0 ∧ polar q y F.b = 0 ∧ polar q y F.c = 0 ∧ polar q y F.c' = 0 := by
  obtain ⟨p, hp, rfl, -⟩ := hy
  exact ⟨polar_tau_a (h.inU p hp) _, polar_tau_b (h.inU p hp) _, polar_tau_c _ _,
    polar_tau_c' _ _⟩

theorem card_Y_mul_le [Finite P] :
    Nat.card (F.Y P h.inU) * Nat.card (F.Y P h.inU) ≤ Nat.card P := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective
    (fun p : P => (⟨F.tau p F.c, (h.tau_mem_Y p.2).1⟩, ⟨F.tau p F.c', (h.tau_mem_Y p.2).2⟩)) ?_
  rintro ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩
  obtain ⟨p, hp, h₁, h₂⟩ := h.exists_tau_eq hy₁ hy₂
  exact ⟨⟨p, hp⟩, by simp [h₁, h₂]⟩

omit h in
theorem exists_ne_one_ne_t [Finite P] (hcard : 2 < Nat.card P) :
    ∃ p ∈ P, p ≠ 1 ∧ p ≠ F.t := by
  by_contra hcon
  push Not at hcon
  have hsub : (P : Set (V ≃ₗ[ZMod 2] V)) ⊆ {1, F.t} := by
    intro p hp
    by_cases h1 : p = 1
    · exact Or.inl h1
    · exact Or.inr (hcon p hp h1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, F.t} : Set (V ≃ₗ[ZMod 2] V)).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : V ≃ₗ[ZMod 2] V) {F.t}
    rwa [Set.ncard_singleton] at this
  rw [← Nat.card_coe_set_eq] at h1
  change Nat.card P ≤ _ at h1
  omega

theorem false_of_card_eq_eight [Finite V] [Finite P] (hcard : Nat.card P = 8) : False := by
  obtain ⟨p, hp, hp1, hpt⟩ := exists_ne_one_ne_t (F := F) (P := P) (by omega)
  obtain ⟨y, hy, hy0⟩ := h.exists_ne_zero_mem_Y hp hp1 hpt
  have hle := h.card_Y_mul_le
  rw [hcard] at hle
  have hY2 : Nat.card (F.Y P h.inU) ≤ 2 := by
    by_contra h3
    push Not at h3
    have : 3 * 3 ≤ Nat.card (F.Y P h.inU) * Nat.card (F.Y P h.inU) := Nat.mul_le_mul h3 h3
    omega
  have hall : ∀ y' ∈ F.Y P h.inU, y' = 0 ∨ y' = y := by
    intro y' hy'
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, hyy⟩ := hcon
    have hsub : ({0, y, y'} : Set V) ⊆ (F.Y P h.inU : Set V) := by
      rintro x (rfl | rfl | rfl)
      · exact (F.Y P h.inU).zero_mem
      · exact hy
      · exact hy'
    have h3 : ({0, y, y'} : Set V).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hyy)]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm hy0, Ne.symm h0⟩
    have h4 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h3, ← Nat.card_coe_set_eq] at h4
    change 3 ≤ Nat.card (F.Y P h.inU) at h4
    omega
  apply hy0
  refine h.eq_zero_of_polar_eq_zero hy fun y' hy' => ?_
  rcases hall y' hy' with rfl | rfl
  · exact polar_zero_right _ _
  · rw [QuadraticMap.polar_self, two_nsmul]
    exact CharTwo.add_self_eq_zero _

end RadHyp

end Frame

end AS35YR

end CFSG.LargeExtraspecial
