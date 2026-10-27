module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

theorem map_le_normalizer_map {G Y : Type*} [Group G] [Group Y] (π : G →* Y)
    {Q Rad : Subgroup G} (hRQ : Rad ≤ Q) (hnorm : ∀ s ∈ Q, ∀ g ∈ Rad, s * g * s⁻¹ ∈ Rad) :
    Rad.map π ≤ Q.map π ∧ Q.map π ≤ normalizer (Rad.map π : Set Y) := by
  refine ⟨Subgroup.map_mono hRQ, ?_⟩
  have key : ∀ m ∈ Q.map π, ∀ h ∈ Rad.map π, m * h * m⁻¹ ∈ Rad.map π := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨g, hg, rfl⟩
    exact ⟨s * g * s⁻¹, hnorm s hs g hg, by simp [map_mul, map_inv]⟩
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key m hm h hh, fun hh => ?_⟩
  have := key m⁻¹ (inv_mem hm) _ hh
  simpa [mul_assoc] using this

theorem isPGroup_map_of_forall_pow {G Y : Type*} [Group G] [Group Y] (π : G →* Y)
    {R : Subgroup G} {r : ℕ} [Fact r.Prime] (h : ∀ g ∈ R, g ^ r = 1) :
    IsPGroup r (R.map π) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨_, g, hg, rfl⟩
  have h1 : (⟨π g, g, hg, rfl⟩ : R.map π) ^ r = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← map_pow, h g hg, map_one]
    rfl
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp h2 with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

theorem fix_conj_of_fix {Y : Type*} [Group Y] (x : Y) (b : MulAut Y) {R : Subgroup Y}
    (hb : ∀ y ∈ R.map (MulAut.conj x).toMonoidHom, b y = y) :
    ∀ y ∈ R, ((MulAut.conj x)⁻¹ * b * MulAut.conj x) y = y := by
  intro y hy
  have h1 := hb _ ⟨y, hy, rfl⟩
  rw [MulAut.mul_apply, MulAut.mul_apply]
  change (MulAut.conj x)⁻¹ (b ((MulAut.conj x) y)) = y
  have h2 : b ((MulAut.conj x) y) = (MulAut.conj x) y := h1
  rw [h2]
  simp only [MulAut.inv_apply, MulAut.conj_symm_apply, MulAut.conj_apply]
  group

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
