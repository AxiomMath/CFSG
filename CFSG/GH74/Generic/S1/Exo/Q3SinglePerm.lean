module

public import CFSG.GH74.Filter.ClassicalOdd.Basic
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltInv

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG.GH74.Filter.ClassicalOdd

section Q8Perm

variable {Ω : Type}

private theorem q8_ne_one (g : Q8) (hg : g ≠ 1) :
    g = QuaternionGroup.a 2 ∨ g * g = QuaternionGroup.a 2 := by
  revert g; decide

private theorem q8_sq_one (g : Q8) (hg : g * g = 1) : g = 1 ∨ g = QuaternionGroup.a 2 := by
  revert g; decide

private theorem q8_z_sq : (QuaternionGroup.a 2 : Q8) * QuaternionGroup.a 2 = 1 := by decide

private theorem q8_z_ne : (QuaternionGroup.a 2 : Q8) ≠ 1 := by decide

private theorem orbit_injective (B : Q8 →* Equiv.Perm Ω) {ω : Ω}
    (hω : B (QuaternionGroup.a 2) ω ≠ ω) : Function.Injective fun g : Q8 => B g ω := by
  intro g h hgh
  have hk : B (h⁻¹ * g) ω = ω := by
    have h1 : B g ω = B h ω := hgh
    calc B (h⁻¹ * g) ω = (B h)⁻¹ (B g ω) := by simp [map_mul, map_inv]
      _ = (B h)⁻¹ (B h ω) := by rw [h1]
      _ = ω := by simp
  by_contra hne
  have hk1 : h⁻¹ * g ≠ 1 := fun h1 => hne (inv_mul_eq_one.mp h1).symm
  rcases q8_ne_one _ hk1 with hz | hz
  · exact hω (hz ▸ hk)
  · apply hω
    have : B (h⁻¹ * g * (h⁻¹ * g)) ω = ω := by
      rw [map_mul, Equiv.Perm.mul_apply, hk, hk]
    rwa [hz] at this

private theorem comm_apply {B : Q8 →* Equiv.Perm Ω} {u : Equiv.Perm Ω}
    (huB : ∀ g, u * B g = B g * u) (g : Q8) (ω : Ω) : u (B g ω) = B g (u ω) := by
  have := congrArg (fun f : Equiv.Perm Ω => f ω) (huB g)
  simpa using this

private theorem eq_one_of_fix [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω))
    (hfix : ∀ g ∈ G, g * g = 1 → (∃ O : Finset Ω, O.card = 8 ∧ ∀ ω ∈ O, g ω = ω) → g = 1)
    (B : Q8 →* Equiv.Perm Ω) {ω : Ω} (hinj : Function.Injective fun g : Q8 => B g ω)
    {w : Equiv.Perm Ω} (hw : w ∈ G) (hw2 : w * w = 1) (hwB : ∀ g, w * B g = B g * w)
    (hwω : w ω = ω) : w = 1 := by
  refine hfix w hw hw2 ⟨Finset.univ.image fun g : Q8 => B g ω, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, QuaternionGroup.card]
  · intro p hp
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hp
    rw [comm_apply hwB, hwω]

private theorem apply_eq_of_involution [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω < 16)
    (G : Subgroup (Equiv.Perm Ω))
    (hfix : ∀ g ∈ G, g * g = 1 → (∃ O : Finset Ω, O.card = 8 ∧ ∀ ω ∈ O, g ω = ω) → g = 1)
    (B : Q8 →* Equiv.Perm Ω) {ω : Ω} (hω : B (QuaternionGroup.a 2) ω ≠ ω)
    {u : Equiv.Perm Ω} (hu : u ∈ G) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huB : ∀ g, u * B g = B g * u) : u ω = B (QuaternionGroup.a 2) ω := by
  have hinj := orbit_injective B hω
  have hcomm := comm_apply huB
  obtain ⟨g, h, hgh⟩ : ∃ g h : Q8, B g ω = B h (u ω) := by
    have hcard : Fintype.card Ω < Fintype.card (Q8 ⊕ Q8) := by
      rw [Fintype.card_sum, QuaternionGroup.card]
      omega
    obtain ⟨x, y, hxy, hfxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (Sum.elim (fun g : Q8 => B g ω) (fun h : Q8 => B h (u ω))) hcard
    rcases x with g | h <;> rcases y with g' | h'
    · exact absurd (congrArg Sum.inl (hinj hfxy)) hxy
    · exact ⟨g, h', hfxy⟩
    · exact ⟨g', h, hfxy.symm⟩
    · refine absurd (congrArg Sum.inr (hinj ?_)) hxy
      simp only [Sum.elim_inr] at hfxy
      rw [← hcomm, ← hcomm] at hfxy
      exact u.injective hfxy
  have huω : u ω = B (h⁻¹ * g) ω := by
    calc u ω = B h⁻¹ (B h (u ω)) := by simp
      _ = B h⁻¹ (B g ω) := by rw [hgh]
      _ = B (h⁻¹ * g) ω := by rw [map_mul]; rfl
  have hr : (h⁻¹ * g) * (h⁻¹ * g) = 1 := by
    apply hinj
    have h1 : u (u ω) = ω := by
      have := congrArg (fun f : Equiv.Perm Ω => f ω) hu2
      simpa using this
    calc B ((h⁻¹ * g) * (h⁻¹ * g)) ω = B (h⁻¹ * g) (B (h⁻¹ * g) ω) := by rw [map_mul]; rfl
      _ = B (h⁻¹ * g) (u ω) := by rw [huω]
      _ = u (B (h⁻¹ * g) ω) := (hcomm _ _).symm
      _ = u (u ω) := by rw [huω]
      _ = ω := h1
      _ = B 1 ω := by simp
  rcases q8_sq_one _ hr with h1 | h1
  · exfalso
    refine hu1 (eq_one_of_fix G hfix B hinj hu hu2 huB ?_)
    rw [huω, h1]
    simp
  · rw [huω, h1]

end Q8Perm

theorem perm_no_two_cent_q8 {Ω : Type} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω < 16)
    (G : Subgroup (Equiv.Perm Ω))
    (hfix : ∀ g ∈ G, g * g = 1 → (∃ O : Finset Ω, O.card = 8 ∧ ∀ ω ∈ O, g ω = ω) → g = 1)
    (B : Q8 →* Equiv.Perm Ω) (hBinj : Function.Injective B) (hBG : ∀ g, B g ∈ G)
    {u v : Equiv.Perm Ω} (hu : u ∈ G) (hv : v ∈ G) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hcomm : u * v = v * u)
    (huB : ∀ g, u * B g = B g * u) (hvB : ∀ g, v * B g = B g * v) : False := by
  have _ := hBG
  obtain ⟨ω, hω⟩ : ∃ ω, B (QuaternionGroup.a 2) ω ≠ ω := by
    by_contra h
    push Not at h
    refine q8_z_ne (hBinj ?_)
    rw [map_one]
    exact Equiv.ext h
  have hinj := orbit_injective B hω
  have hu' := apply_eq_of_involution hΩ G hfix B hω hu hu2 hu1 huB
  have hv' := apply_eq_of_involution hΩ G hfix B hω hv hv2 hv1 hvB
  have huv2 : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [hcomm]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu2, hv2, mul_one]
  have huvB : ∀ g, (u * v) * B g = B g * (u * v) := by
    intro g
    rw [mul_assoc, hvB, ← mul_assoc, huB, mul_assoc]
  have huvω : (u * v) ω = ω := by
    rw [Equiv.Perm.mul_apply, hv', comm_apply huB, hu', ← Equiv.Perm.mul_apply, ← map_mul, q8_z_sq,
      map_one]
    rfl
  have h1 : u * v = 1 := eq_one_of_fix G hfix B hinj (G.mul_mem hu hv) huv2 huvB huvω
  apply huv
  calc u = u * (v * v) := by rw [hv2, mul_one]
    _ = (u * v) * v := by rw [mul_assoc]
    _ = v := by rw [h1, one_mul]

theorem alt_fix_eight {n : ℕ} (hn : n ≤ 11) :
    ∀ g ∈ alternatingGroup (Fin n), g * g = 1 →
      (∃ O : Finset (Fin n), O.card = 8 ∧ ∀ ω ∈ O, g ω = ω) → g = 1 := by
  intro g hg hgg ⟨O, hO, hOfix⟩
  obtain ⟨hsupp, hsign⟩ := CFSG.GH74.GLS.IVK.GHInv.involution_cycle_data hgg
  rw [Equiv.Perm.mem_alternatingGroup, hsign] at hg
  have heven : Even g.cycleType.card := (neg_one_pow_eq_one_iff_even (by decide)).1 hg
  have hdisj : Disjoint g.support O := by
    rw [Finset.disjoint_right]
    intro ω hω hs
    exact (Equiv.Perm.mem_support.1 hs) (hOfix ω hω)
  have hcard : g.support.card + O.card ≤ n := by
    rw [← Finset.card_union_of_disjoint hdisj]
    simpa using Finset.card_le_univ (g.support ∪ O)
  obtain ⟨k, hk⟩ := heven
  have hsupp0 : g.support.card = 0 := by omega
  rwa [Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff] at hsupp0

end CFSG.GH74.Generic.S1.Exo
