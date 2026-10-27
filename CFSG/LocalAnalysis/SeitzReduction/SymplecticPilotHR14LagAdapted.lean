module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaO2

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def LagAdapted (Q : QuadraticForm K V) (s s' : V ≃ₗ[K] V) : Prop :=
  s' ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ s' * s' = 1 ∧
    omegaInvSpace s' ≤ omegaInvSpace s ∧
    ∀ v, omegaInvNil s v ∈ omegaInvSpace s' → omegaInvNil s' v = omegaInvNil s v

theorem lagAdapted_self {s : V ≃ₗ[K] V} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hss : s * s = 1) : LagAdapted Q s s :=
  ⟨hs, hss, le_rfl, fun _ _ => rfl⟩

theorem eq_one_of_finrank_omegaInvSpace_eq_zero [FiniteDimensional K V] {s' : V ≃ₗ[K] V}
    (h : finrank K (omegaInvSpace s') = 0) : s' = 1 := by
  rw [Submodule.finrank_eq_zero] at h
  apply eq_one_of_omegaInvNil_eq_zero
  intro x
  have hx := omegaInvNil_mem_omegaInvSpace s' x
  rwa [h, Submodule.mem_bot] at hx

variable [CharP K 2] {s : V ≃ₗ[K] V}

theorem omegaInvNil_eq_zero_of_lagAdapted (hQ : (polarBilin Q).Nondegenerate)
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {s' : V ≃ₗ[K] V}
    (h : LagAdapted Q s s') {w : V} (hw : w ∈ omegaInvSpace s) : omegaInvNil s' w = 0 :=
  (omegaInvNil_eq_zero_iff hQ h.1 h.2.1).2 fun _ hu =>
    polar_of_mem_omegaInvSpace hs hss hw (h.2.2.1 hu)

omit [CharP K 2] in
theorem exists_polar_ne_zero_of_lagAdapted (hQ : (polarBilin Q).Nondegenerate)
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {s' : V ≃ₗ[K] V}
    (h : LagAdapted Q s s') {u : V} (hu : u ∈ omegaInvSpace s') (hu0 : u ≠ 0) :
    ∃ b, omegaInvNil s b ∈ omegaInvSpace s' ∧ polar Q u b ≠ 0 := by
  obtain ⟨hs', hss', hle, had⟩ := h
  obtain ⟨v, hv⟩ := mem_omegaInvSpace_iff.1 (hle hu)
  have hv' : omegaInvNil s' v = u := (had v (by rw [hv]; exact hu)).trans hv
  obtain ⟨b', hb'⟩ := exists_polar_ne_zero hQ hu0
  obtain ⟨b, hb⟩ := mem_omegaInvSpace_iff.1 (hle (omegaInvNil_mem_omegaInvSpace s' b'))
  refine ⟨b, by rw [hb]; exact omegaInvNil_mem_omegaInvSpace s' b', ?_⟩
  rw [← hv, polar_omegaInvNil_left hs hss, hb, ← polar_omegaInvNil_left hs' hss', hv']
  exact hb'

theorem lagAdapted_mul [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {s' g : V ≃ₗ[K] V}
    (h : LagAdapted Q s s') (hg : LagAdapted Q s g) (hgs' : omegaInvSpace g ≤ omegaInvSpace s') :
    LagAdapted Q s (s' * g) ∧
      (∀ v, omegaInvNil (s' * g) v = omegaInvNil s' v + omegaInvNil g v) ∧
      (∀ u ∈ omegaInvSpace (s' * g), ∀ b, omegaInvNil s b ∈ omegaInvSpace g →
        polar Q u b = 0) ∧
      omegaInvSpace (s' * g) ≤ omegaInvSpace s' ∧
      finrank K (omegaInvSpace (s' * g)) + finrank K (omegaInvSpace g) =
        finrank K (omegaInvSpace s') ∧
      s' = (s' * g) * g := by
  have h2 : (2 : K) = 0 := omegaInv_two_eq_zero
  have hk' : ∀ w ∈ omegaInvSpace s, omegaInvNil s' w = 0 := fun w hw =>
    omegaInvNil_eq_zero_of_lagAdapted hQ hs hss h hw
  have hkg : ∀ w ∈ omegaInvSpace s, omegaInvNil g w = 0 := fun w hw =>
    omegaInvNil_eq_zero_of_lagAdapted hQ hs hss hg hw
  obtain ⟨hs', hss', hle', had'⟩ := h
  obtain ⟨hg', hgg, hleg, hadg⟩ := hg
  have hN : ∀ v, omegaInvNil (s' * g) v = omegaInvNil s' v + omegaInvNil g v := by
    intro v
    have e3 : s' (g v - v) = g v - v := omegaInvNil_eq_zero_iff_apply.1
      (hk' _ (hleg (omegaInvNil_mem_omegaInvSpace g v)))
    have e4 : s' (g v) = (g v - v) + s' v := by rw [← e3, ← map_add, sub_add_cancel]
    rw [omegaInvNil_apply, omegaInvNil_apply, omegaInvNil_apply, LinearEquiv.mul_apply, e4]
    abel
  have hcomm : s' * g = g * s' := by
    refine LinearEquiv.ext fun v => ?_
    have e3 : g (s' v - v) = s' v - v := omegaInvNil_eq_zero_iff_apply.1
      (hkg _ (hle' (omegaInvNil_mem_omegaInvSpace s' v)))
    have e4 : g (s' v) = (s' v - v) + g v := by rw [← e3, ← map_add, sub_add_cancel]
    have e5 := hN v
    rw [omegaInvNil_apply, omegaInvNil_apply, omegaInvNil_apply] at e5
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e4]
    rw [LinearEquiv.mul_apply] at e5
    linear_combination (norm := module) e5
  have hinv : (s' * g) * (s' * g) = 1 := by
    calc (s' * g) * (s' * g) = s' * (g * s') * g := by group
      _ = s' * (s' * g) * g := by rw [hcomm]
      _ = (s' * s') * (g * g) := by group
      _ = 1 := by rw [hss', hgg, one_mul]
  have hle : omegaInvSpace (s' * g) ≤ omegaInvSpace s' := by
    intro u hu
    obtain ⟨v, rfl⟩ := mem_omegaInvSpace_iff.1 hu
    rw [hN]
    exact (omegaInvSpace s').add_mem (omegaInvNil_mem_omegaInvSpace s' v)
      (hgs' (omegaInvNil_mem_omegaInvSpace g v))
  have horth : ∀ u ∈ omegaInvSpace (s' * g), ∀ b, omegaInvNil s b ∈ omegaInvSpace g →
      polar Q u b = 0 := by
    intro u hu b hb
    obtain ⟨v, rfl⟩ := mem_omegaInvSpace_iff.1 hu
    rw [hN, polar_add_left, polar_omegaInvNil_left hs' hss', polar_omegaInvNil_left hg' hgg,
      had' b (hgs' hb), hadg b hb]
    linear_combination polar Q v (omegaInvNil s b) * h2
  have had : ∀ v, omegaInvNil s v ∈ omegaInvSpace (s' * g) →
      omegaInvNil (s' * g) v = omegaInvNil s v := by
    intro v hv
    have hgv : omegaInvNil g v = 0 := by
      refine (omegaInvNil_eq_zero_iff hQ hg' hgg).2 fun w hw => ?_
      obtain ⟨c, hc⟩ := mem_omegaInvSpace_iff.1 (hleg hw)
      rw [← hc, ← polar_omegaInvNil_left hs hss]
      exact horth _ hv c (by rw [hc]; exact hw)
    rw [hN, hgv, add_zero, had' v (hle hv)]
  have hsup : omegaInvSpace (s' * g) ⊔ omegaInvSpace g = omegaInvSpace s' := by
    refine le_antisymm (sup_le hle hgs') fun u hu => ?_
    obtain ⟨v, rfl⟩ := mem_omegaInvSpace_iff.1 hu
    refine Submodule.mem_sup.2 ⟨_, omegaInvNil_mem_omegaInvSpace (s' * g) v, _,
      omegaInvNil_mem_omegaInvSpace g v, ?_⟩
    rw [hN, add_assoc, omegaInv_add_self K, add_zero]
  have hinf : omegaInvSpace (s' * g) ⊓ omegaInvSpace g = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨hu1, hu2⟩
    rw [Submodule.mem_bot]
    by_contra hu0
    obtain ⟨b, hb, hub⟩ := exists_polar_ne_zero_of_lagAdapted hQ hs hss
      ⟨hg', hgg, hleg, hadg⟩ hu2 hu0
    exact hub (horth u hu1 b hb)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (omegaInvSpace (s' * g)) (omegaInvSpace g)
  rw [hsup, hinf, finrank_bot, add_zero] at hdim
  refine ⟨⟨mul_mem hs' hg', hinv, hle.trans hle', had⟩, hN, horth, hle, hdim.symm, ?_⟩
  rw [mul_assoc, hgg, mul_one]

end CFSG.SeitzReduction.SymplecticPilot
