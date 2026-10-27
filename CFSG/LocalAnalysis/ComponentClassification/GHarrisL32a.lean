module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL31b

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G]

namespace GHSylow

variable (D : GHSylow G)

abbrev x : G := D.toG (SE.gen 6)

abbrev ay : G := D.toG (SE.gen 8 * SE.gen 7)

abbrev ya3 : G := D.toG (SE.gen 7 * SE.gen 4)

abbrev X : Subgroup G := (D.S : Subgroup G) ⊓ centralizer ({D.x} : Set G)

theorem conj_mem_Ct {s c : G} (hs : s ∈ (D.S : Subgroup G)) (hc : c ∈ D.Ct) :
    s⁻¹ * c * s ∈ D.Ct := by
  obtain ⟨hcS, hct⟩ := mem_inf.mp hc
  have hct' : c * D.t = D.t * c := mem_centralizer_singleton_iff.mp hct
  have hcz : c * D.z = D.z * c := mem_centralizer_singleton_iff.mp (D.S_le_centralizer_z hcS)
  refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hs) hcS) hs, mem_centralizer_singleton_iff.mpr ?_⟩
  have key : c * (s * D.t * s⁻¹) = (s * D.t * s⁻¹) * c := by
    have hs' := D.conj_t_S (inv_mem hs)
    rw [inv_inv] at hs'
    rcases hs' with h | h <;> rw [h]
    · exact hct'
    · rw [← mul_assoc, hct', mul_assoc, hcz, mul_assoc]
  calc s⁻¹ * c * s * D.t = s⁻¹ * (c * (s * D.t * s⁻¹)) * s := by group
    _ = s⁻¹ * ((s * D.t * s⁻¹) * c) * s := by rw [key]
    _ = D.t * (s⁻¹ * c * s) := by group

theorem card_inf_centralizer_conj {c : G} (hc : c ∈ (D.S : Subgroup G)) (u : G) :
    Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({c⁻¹ * u * c} : Set G)) =
      Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({u} : Set G)) := by
  have hmap : ((D.S : Subgroup G) ⊓ centralizer ({u} : Set G)).map
      (MulAut.conj c⁻¹).toMonoidHom = (D.S : Subgroup G) ⊓ centralizer ({c⁻¹ * u * c} : Set G) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hwS, hwu⟩ := mem_inf.mp hw
      have h := mem_centralizer_singleton_iff.mp hwu
      refine mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
      · change c⁻¹ * w * c⁻¹⁻¹ ∈ (D.S : Subgroup G)
        rw [inv_inv]
        exact mul_mem (mul_mem (inv_mem hc) hwS) hc
      · change c⁻¹ * w * c⁻¹⁻¹ * (c⁻¹ * u * c) = c⁻¹ * u * c * (c⁻¹ * w * c⁻¹⁻¹)
        rw [inv_inv]
        calc c⁻¹ * w * c * (c⁻¹ * u * c) = c⁻¹ * (w * u) * c := by group
          _ = c⁻¹ * (u * w) * c := by rw [h]
          _ = c⁻¹ * u * c * (c⁻¹ * w * c) := by group
    · intro hv
      obtain ⟨hvS, hvu⟩ := mem_inf.mp hv
      have h := mem_centralizer_singleton_iff.mp hvu
      refine ⟨c * v * c⁻¹, mem_inf.mpr ⟨mul_mem (mul_mem hc hvS) (inv_mem hc),
        mem_centralizer_singleton_iff.mpr ?_⟩, ?_⟩
      · calc c * v * c⁻¹ * u = c * (v * (c⁻¹ * u * c)) * c⁻¹ := by group
          _ = c * ((c⁻¹ * u * c) * v) * c⁻¹ := by rw [h]
          _ = u * (c * v * c⁻¹) := by group
      · change c⁻¹ * (c * v * c⁻¹) * c⁻¹⁻¹ = v
        group
  rw [← hmap, card_map_of_injective (MulAut.conj c⁻¹).injective]

end GHSylow

end CFSG.ComponentClassification.GHarris
