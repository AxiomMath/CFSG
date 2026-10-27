module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL32a
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL32Facts
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSFacts

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G]

namespace GHSylow

variable (D : GHSylow G)

theorem ay_mem_X : D.ay ∈ D.X :=
  mem_inf.mpr ⟨D.toG_mem _, mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul, SE.ay_comm_x])⟩

theorem ay_pow_four : D.ay ^ 4 = D.z := by rw [← map_pow, SE.ay_pow_four]

theorem false_of_conj_X_Ct {h : G}
    (hX : ∀ c ∈ D.X, h⁻¹ * c * h ∈ D.Ct) (hz : h⁻¹ * D.z * h = D.z) : False := by
  classical
  set w := h⁻¹ * D.ay * h with hw
  have hwC : w ∈ D.Ct := hX _ D.ay_mem_X
  have hw4 : w ^ 4 = D.z := by
    rw [hw, conj_pow_inv, D.ay_pow_four, hz]
  obtain ⟨hwS, hwt⟩ := mem_inf.mp hwC
  obtain ⟨w₀, hw₀⟩ := D.exists_toG hwS
  have hw₀t : w₀ * SE.invRep 1 = SE.invRep 1 * w₀ := by
    have h1 := mem_centralizer_singleton_iff.mp hwt
    rw [← hw₀, ← map_mul, ← map_mul] at h1
    exact D.toG_injective h1
  have hw₀4 : w₀ ^ 4 = SE.gen 0 := by
    apply D.toG_injective
    rw [map_pow, hw₀, hw4]
  obtain ⟨s₀, hs₀⟩ := SE.exists_conj_ya3 w₀ hw₀t hw₀4
  set s := D.toG s₀
  have hsS : s ∈ (D.S : Subgroup G) := D.toG_mem _
  have hsw : s⁻¹ * D.ya3 * s = w := by
    rw [← hw₀, ← hs₀, map_mul, map_mul, map_inv]
  have hmem : ∀ c₀ : {c : SE // c * SE.gen 6 = SE.gen 6 * c},
      s * (h⁻¹ * D.toG c₀.1 * h) * s⁻¹ ∈ (D.S : Subgroup G) := by
    intro c₀
    have hc : D.toG c₀.1 ∈ D.X := mem_inf.mpr ⟨D.toG_mem _, mem_centralizer_singleton_iff.mpr (by
      rw [← map_mul, ← map_mul, c₀.2])⟩
    have := D.conj_mem_Ct (inv_mem hsS) (hX _ hc)
    rw [inv_inv] at this
    exact (mem_inf.mp this).1
  choose f hf using fun c₀ => D.exists_toG (hmem c₀)
  have hfC : ∀ c₀, f c₀ * SE.invRep 1 = SE.invRep 1 * f c₀ := by
    intro c₀
    have hc : D.toG c₀.1 ∈ D.X := mem_inf.mpr ⟨D.toG_mem _, mem_centralizer_singleton_iff.mpr (by
      rw [← map_mul, ← map_mul, c₀.2])⟩
    have h1 := D.conj_mem_Ct (inv_mem hsS) (hX _ hc)
    rw [inv_inv, ← hf c₀] at h1
    have h2 := mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2
    rw [← map_mul, ← map_mul] at h2
    exact D.toG_injective h2
  have hfN : ∀ c₀, ∃ k : Fin 8, (f c₀)⁻¹ * (SE.gen 7 * SE.gen 4) * f c₀ =
      (SE.gen 7 * SE.gen 4) ^ (k : ℕ) := by
    intro c₀
    obtain ⟨k, hk⟩ := SE.normalizes_ay c₀.1 c₀.2
    refine ⟨k, D.toG_injective ?_⟩
    have hk' : (D.toG c₀.1)⁻¹ * D.ay * D.toG c₀.1 = D.ay ^ (k : ℕ) := by
      rw [← map_inv, ← map_mul, ← map_mul, hk, map_pow]
    rw [map_mul, map_mul, map_inv, hf c₀, map_pow]
    change (s * (h⁻¹ * D.toG c₀.1 * h) * s⁻¹)⁻¹ * D.ya3 * (s * (h⁻¹ * D.toG c₀.1 * h) * s⁻¹) =
      D.ya3 ^ (k : ℕ)
    have hya3 : D.ya3 = s * w * s⁻¹ := by rw [← hsw]; group
    rw [hya3, hw]
    calc (s * (h⁻¹ * D.toG c₀.1 * h) * s⁻¹)⁻¹ * (s * (h⁻¹ * D.ay * h) * s⁻¹) *
          (s * (h⁻¹ * D.toG c₀.1 * h) * s⁻¹) =
        s * (h⁻¹ * ((D.toG c₀.1)⁻¹ * D.ay * D.toG c₀.1) * h) * s⁻¹ := by group
      _ = s * (h⁻¹ * D.ay ^ (k : ℕ) * h) * s⁻¹ := by rw [hk']
      _ = (s * (h⁻¹ * D.ay * h) * s⁻¹) ^ (k : ℕ) := by rw [conj_pow, conj_pow_inv]
  let F : {c : SE // c * SE.gen 6 = SE.gen 6 * c} →
      {c : SE // c * SE.invRep 1 = SE.invRep 1 * c ∧
        ∃ k : Fin 8, c⁻¹ * (SE.gen 7 * SE.gen 4) * c = (SE.gen 7 * SE.gen 4) ^ (k : ℕ)} :=
    fun c₀ => ⟨f c₀, hfC c₀, hfN c₀⟩
  have hF : Function.Injective F := by
    intro c₁ c₂ h12
    have h1 : f c₁ = f c₂ := congrArg Subtype.val h12
    have h2 := congrArg D.toG h1
    rw [hf, hf] at h2
    have h3 : D.toG c₁.1 = D.toG c₂.1 := by
      have := congrArg (fun y => h * (s⁻¹ * y * s) * h⁻¹) h2
      simpa [mul_assoc] using this
    exact Subtype.ext (D.toG_injective h3)
  have hcard := Fintype.card_le_of_injective F hF
  rw [Fintype.card_subtype, Fintype.card_subtype, SE.card_normalizer_ya3,
    show (Finset.univ.filter fun c : SE => c * SE.gen 6 = SE.gen 6 * c).card = 64 from
      SE.card_filter_comm_invRep 5] at hcard
  omega

end GHSylow

end CFSG.ComponentClassification.GHarris
