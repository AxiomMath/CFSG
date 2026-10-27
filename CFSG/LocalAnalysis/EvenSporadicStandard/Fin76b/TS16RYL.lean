module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYT2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Defs

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup Pointwise

variable {G : Type} [Group G] {L : Subgroup G} {z : G}

theorem exists_mul_of_mem_sup_zpowers (hTD : ThetaData G L z) {x : G} (hx : x ∈ L ⊔ zpowers z) :
    ∃ ℓ ∈ L, ∃ w ∈ zpowers z, x = ℓ * w := by
  have hle : zpowers z ≤ centralizer (L : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 hTD.z_cent
  have hle' : L ≤ centralizer (zpowers z : Set G) := Subgroup.le_centralizer_iff.2 hle
  have h := Subgroup.coe_mul_of_left_le_normalizer_right L (zpowers z)
    (hle'.trans (centralizer_le_normalizer _))
  have hx' : x ∈ ((L : Set G) * (zpowers z : Set G)) := by
    rw [← h]; exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem ThetaData.exists_sigma (hTD : ThetaData G L z) (hz2 : z * z = 1) (hzL : z ∉ L)
    (hsq : ∀ y ∈ centralizer ({z} : Set G), y * y ∈ L) (r : MulAut ↥L) (hr2 : r * r = 1)
    (hrinn : ¬ IsInnerAut r) :
    ∃ g : ↥(centralizer ({z} : Set G)), hTD.theta g = r ∧ (g : G) * g = 1 ∧
      (g : G) ∉ L ⊔ zpowers z := by
  obtain ⟨g, hg⟩ := hTD.theta_surj r
  refine ⟨g, hg, ?_, ?_⟩
  · have h1 : hTD.theta (g * g) = 1 := by rw [map_mul, hg, hr2]
    have h2 : ((g * g : ↥(centralizer ({z} : Set G))) : G) ∈ zpowers z := hTD.theta_eq_one h1
    have h3 : (g : G) * g ∈ L := hsq g g.2
    rcases mem_zpowers_sq_eq_one hz2 h2 with h | h
    · exact h
    · exact absurd (h ▸ h3) hzL
  · intro hmem
    apply hrinn
    obtain ⟨ℓ, hℓ, w, hw, hgℓw⟩ := exists_mul_of_mem_sup_zpowers hTD hmem
    refine ⟨⟨ℓ, hℓ⟩, ?_⟩
    rw [← hg, ThetaData.theta_eq_iff]
    intro x
    have hwc : w * (x : G) = x * w := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
      exact (Commute.zpow_left (show Commute z x from (hTD.z_cent x x.2).symm) k).eq
    show ((g : G)) * x * (g : G)⁻¹ = ((MulAut.conj (⟨ℓ, hℓ⟩ : ↥L) x : ↥L) : G)
    rw [hgℓw]
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    calc ℓ * w * (x : G) * (ℓ * w)⁻¹ = ℓ * (w * x) * w⁻¹ * ℓ⁻¹ := by group
      _ = ℓ * (x * w) * w⁻¹ * ℓ⁻¹ := by rw [hwc]
      _ = ℓ * x * ℓ⁻¹ := by group

end CFSG.EvenSporadicStandard.Fin76b
