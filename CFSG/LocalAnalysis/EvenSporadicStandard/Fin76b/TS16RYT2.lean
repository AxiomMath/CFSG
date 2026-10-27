module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYT

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {z : G}

theorem ThetaData.le_normalizer (hTD : ThetaData G L z) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hTD.norm g hg h hh, fun hh => ?_⟩
  have := hTD.norm g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

@[expose] noncomputable def ThetaData.theta (hTD : ThetaData G L z) :
    ↥(centralizer ({z} : Set G)) →* MulAut ↥L :=
  L.normalizerMonoidHom.comp (Subgroup.inclusion hTD.le_normalizer)

theorem ThetaData.theta_apply (hTD : ThetaData G L z) (g : ↥(centralizer ({z} : Set G)))
    (ℓ : ↥L) : ((hTD.theta g ℓ : ↥L) : G) = (g : G) * ℓ * (g : G)⁻¹ := by
  simp [ThetaData.theta]

theorem ThetaData.theta_surj (hTD : ThetaData G L z) (r : MulAut ↥L) :
    ∃ g : ↥(centralizer ({z} : Set G)), hTD.theta g = r := by
  obtain ⟨g, hg, hr⟩ := hTD.surj r
  refine ⟨⟨g, hg⟩, ?_⟩
  ext ℓ
  rw [hTD.theta_apply]
  exact hr ℓ

theorem ThetaData.theta_eq_iff (hTD : ThetaData G L z) {g : ↥(centralizer ({z} : Set G))}
    {r : MulAut ↥L} : hTD.theta g = r ↔ ∀ ℓ : ↥L, (g : G) * ℓ * (g : G)⁻¹ = ((r ℓ : ↥L) : G) := by
  constructor
  · intro h ℓ
    rw [← h, hTD.theta_apply]
  · intro h
    ext ℓ
    rw [hTD.theta_apply]
    exact h ℓ

theorem ThetaData.theta_of_mem (hTD : ThetaData G L z) {ℓ : G} (hℓ : ℓ ∈ L)
    (hH : ℓ ∈ centralizer ({z} : Set G)) :
    hTD.theta ⟨ℓ, hH⟩ = MulAut.conj (⟨ℓ, hℓ⟩ : ↥L) := by
  rw [ThetaData.theta_eq_iff]
  intro x
  simp [MulAut.conj_apply]

theorem ThetaData.theta_eq_one (hTD : ThetaData G L z) {g : ↥(centralizer ({z} : Set G))}
    (h : hTD.theta g = 1) : (g : G) ∈ zpowers z := by
  apply hTD.ker g g.2
  intro ℓ hℓ
  have := (ThetaData.theta_eq_iff hTD).1 h ⟨ℓ, hℓ⟩
  simp only [MulAut.one_apply] at this
  calc (g : G) * ℓ = ((g : G) * ℓ * (g : G)⁻¹) * g := by group
    _ = ℓ * g := by rw [this]

theorem ThetaData.theta_z (hTD : ThetaData G L z) :
    hTD.theta ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ = 1 := by
  rw [ThetaData.theta_eq_iff]
  intro ℓ
  have := hTD.z_cent ℓ ℓ.2
  show z * (ℓ : G) * z⁻¹ = (((1 : MulAut ↥L) ℓ : ↥L) : G)
  simp only [MulAut.one_apply]
  calc z * (ℓ : G) * z⁻¹ = (z * ℓ) * z⁻¹ := rfl
    _ = (ℓ * z) * z⁻¹ := by rw [this]
    _ = ℓ := by group

end CFSG.EvenSporadicStandard.Fin76b
