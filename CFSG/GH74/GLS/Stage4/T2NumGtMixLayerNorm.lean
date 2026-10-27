module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixCtx
public import CFSG.GH74.GLS.Stage4.T2P56Glue

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank

section Norm

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2Ctx_all_normKW
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hLoc : Ch6Loc5W N u) (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁)
    (hq₂ : N.q₂ = q₂) {c : G} (hc : c * z = z * c) :
    (∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁) ∧ (∀ x ∈ K₂, c * x * c⁻¹ ∈ K₂) := by
  have ctx := t2Ctx_ofW hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  obtain ⟨a, b, hab, -, ha2, hbodd, haz, hbz⟩ := exists_two_odd_decomp c
  have hcomm : ∀ w : G, w ∈ Subgroup.zpowers c → w * z = z * w := by
    intro w hw
    obtain ⟨r, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact ((Commute.zpow_left (show Commute c z from hc) r)).eq
  have haz' : a * z = z * a := hcomm a haz
  have hbz' : b * z = z * b := hcomm b hbz
  have haC : a ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := twoElt_mem_residual haz' ha2
  obtain ⟨hn₁, hn₂⟩ := t2C_C₁_normalizes hRem hSet.comm
  obtain ⟨hb₁, hb₂⟩ := t2Ctx_odd_normK ctx hbz' hbodd
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have : c * x * c⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by rw [hab]; group
    rw [this]; exact hn₁ a haC _ (hb₁ x hx)
  · have : c * x * c⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by rw [hab]; group
    rw [this]; exact hn₂ a haC _ (hb₂ x hx)

end Norm

end CFSG.GH74.GLS.Stage4.Rest
