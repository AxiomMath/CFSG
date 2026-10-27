module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S12Cen

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath Open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

set_option linter.unusedSectionVars false

section Perm

open Equiv

theorem exists_wj_check : ∀ a b : Fin 5, a ≠ b → ∃ w j : Perm (Fin 5), Perm.sign w = 1 ∧
    Perm.sign j = 1 ∧ w ^ 3 = 1 ∧ w ≠ 1 ∧ j * j = 1 ∧ j ≠ 1 ∧ w * swap a b = swap a b * w ∧
    j * swap a b = swap a b * j ∧ j * w * j⁻¹ = w⁻¹ := by
  decide +kernel

end Perm

section Phi

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {E : Subgroup G} {z : G}
  (a : PA11 L t E z)

@[expose] noncomputable def PA11.phiK : ↥a.K₁ →* Wr2 (Equiv.Perm (Fin 5)) :=
  a.phi.comp (Subgroup.inclusion a.K₁_le)

theorem PA11.phiK_apply (k : ↥a.K₁) : a.phiK k = a.phi ⟨k, a.K₁_le k.2⟩ := rfl

theorem PA11.phiK_injective : Function.Injective a.phiK := by
  intro k l h
  exact Subtype.ext (a.K₁_inj k.2 l.2 h)

theorem PA11.exists_phiK (ρ : alternatingGroup (Fin 5)) :
    ∃ k : ↥a.K₁, a.phiK k = base (ρ : Equiv.Perm (Fin 5)) 1 := by
  obtain ⟨k, hk, h⟩ := a.K₁_onto ρ
  exact ⟨⟨k, hk⟩, h⟩

theorem PA11.comm_ub_of_phi {k : ↥a.K₁} {s ρ : Equiv.Perm (Fin 5)}
    (hub : a.phi ⟨a.ub, a.ub_cy⟩ = base s s) (hk : a.phiK k = base ρ 1)
    (hρ : ρ * s = s * ρ) : (k : G) * a.ub = a.ub * k := by
  have hmem : a.ub * k * a.ub⁻¹ ∈ a.K₁ := a.conj_mem_K₁ a.ub_cy hub k.2
  have h1 : a.phiK ⟨a.ub * k * a.ub⁻¹, hmem⟩ = a.phiK k := by
    have e : (⟨a.ub * k * a.ub⁻¹, a.K₁_le hmem⟩ : ↥(Cen a.y)) =
        ⟨a.ub, a.ub_cy⟩ * ⟨k, a.K₁_le k.2⟩ * ⟨a.ub, a.ub_cy⟩⁻¹ := rfl
    have hk' : a.phi ⟨k, a.K₁_le k.2⟩ = base ρ 1 := hk
    rw [a.phiK_apply, e, map_mul, map_mul, map_inv, hub, hk', conj_base_base, hk]
    have e1 : s * ρ * s⁻¹ = ρ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hρ.symm
    have e2 : s * 1 * s⁻¹ = (1 : Equiv.Perm (Fin 5)) := by group
    rw [e1, e2]
  have h2 := congrArg Subtype.val (a.phiK_injective h1)
  have h3 : a.ub * (k : G) * a.ub⁻¹ = k := h2
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3.symm

theorem PA11.exists_wj : ∃ w j : ↥a.K₁, w * (w * w) = 1 ∧ w ≠ 1 ∧ j * j = 1 ∧ j ≠ 1 ∧
    (w : G) * a.ub = a.ub * w ∧ (j : G) * a.ub = a.ub * j ∧ j * w * j⁻¹ = w⁻¹ := by
  obtain ⟨σ, ⟨p, q, hpq, rfl⟩, hι⟩ := a.ub_base
  obtain ⟨wt, jt, hsw, hsj, hw3, hw1, hj2, hj1, hwσ, hjσ, hjw⟩ := exists_wj_check p q hpq
  obtain ⟨w, hw⟩ := a.exists_phiK ⟨wt, Equiv.Perm.mem_alternatingGroup.2 hsw⟩
  obtain ⟨j, hj⟩ := a.exists_phiK ⟨jt, Equiv.Perm.mem_alternatingGroup.2 hsj⟩
  have hw' : a.phiK w = base wt 1 := hw
  have hj' : a.phiK j = base jt 1 := hj
  have hub : a.phi ⟨a.ub, a.ub_cy⟩ = base (Equiv.swap p q) (Equiv.swap p q) := hι
  have hw3' : wt * (wt * wt) = 1 := by rw [← pow_three]; exact hw3
  refine ⟨w, j, ?_, ?_, ?_, ?_, a.comm_ub_of_phi hub hw' hwσ, a.comm_ub_of_phi hub hj' hjσ, ?_⟩
  · apply a.phiK_injective
    rw [map_mul, map_mul, map_one, hw', base_mul_base, base_mul_base]
    simp only [hw3', mul_one, base_one]
  · intro h
    have := congrArg a.phiK h
    rw [map_one, hw'] at this
    exact hw1 (base_injective.1 (this.trans base_one.symm)).1
  · apply a.phiK_injective
    rw [map_mul, map_one, hj', base_mul_base]
    simp only [hj2, mul_one, base_one]
  · intro h
    have := congrArg a.phiK h
    rw [map_one, hj'] at this
    exact hj1 (base_injective.1 (this.trans base_one.symm)).1
  · apply a.phiK_injective
    rw [map_mul, map_mul, map_inv, map_inv, hj', hw', conj_base_base, base_inv, hjw]
    simp

end Phi

section U1

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {E : Subgroup G} {z : G}
  (a : PA11 L t E z)

theorem PA11.u₁_sq : a.u₁ * a.u₁ = 1 := by
  obtain ⟨o1, -⟩ := a.d8_props a.d8_case
  have := pow_orderOf_eq_one a.u₁
  rw [o1, pow_two] at this
  exact this

theorem PA11.u₁_conj_mem (h : a.FirstType) {k : G} (hk : k ∈ a.K₁) : a.u₁ * k * a.u₁⁻¹ ∈ a.K₁ := by
  obtain ⟨σ, -, hc, hι⟩ := h
  exact a.conj_mem_K₁ hc (s := σ) (s' := 1) hι hk

theorem PA11.u₁_norm (h : a.FirstType) : a.u₁ ∈ normalizer (a.K₁ : Set G) := by
  rw [mem_normalizer_iff]
  intro k
  refine ⟨fun hk => a.u₁_conj_mem h hk, fun hk => ?_⟩
  have h1 := a.u₁_conj_mem h hk
  have e : a.u₁ * (a.u₁ * k * a.u₁⁻¹) * a.u₁⁻¹ = k := by
    have : a.u₁ * (a.u₁ * k * a.u₁⁻¹) * a.u₁⁻¹ = (a.u₁ * a.u₁) * k * (a.u₁ * a.u₁)⁻¹ := by group
    rw [this, a.u₁_sq]
    group
  rwa [e] at h1

theorem PA11.comm_K₁_of {g : G} (hg : g ∈ Cen a.y) {s' : Equiv.Perm (Fin 5)}
    (hs : a.phi ⟨g, hg⟩ = base 1 s') {k : G} (hk : k ∈ a.K₁) : g * k = k * g := by
  have hmem := a.conj_mem_K₁ hg hs hk
  obtain ⟨σ, hσ⟩ := a.K₁_ι k hk
  have hσ' : a.phi ⟨k, a.K₁_le hk⟩ = base (σ : Equiv.Perm (Fin 5)) 1 := hσ
  have h1 : a.phi ⟨g * k * g⁻¹, a.K₁_le hmem⟩ = a.phi ⟨k, a.K₁_le hk⟩ := by
    have e : (⟨g * k * g⁻¹, a.K₁_le hmem⟩ : ↥(Cen a.y)) =
        ⟨g, hg⟩ * ⟨k, a.K₁_le hk⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hs, hσ', conj_base_base]
    have e1 : (1 : Equiv.Perm (Fin 5)) * σ * (1 : Equiv.Perm (Fin 5))⁻¹ = σ := by group
    have e2 : s' * 1 * s'⁻¹ = (1 : Equiv.Perm (Fin 5)) := by group
    rw [e1, e2]
  have h2 := a.K₁_inj hmem hk h1
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2

end U1

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
