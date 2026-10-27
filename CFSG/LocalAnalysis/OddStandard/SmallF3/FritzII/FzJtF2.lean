module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtDict
public import Certificates.Data.FzJtCheck

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup Certificates.FzJ36 Certificates.FzFus Certificates.FzJt

variable {G : Type} [Group G]

theorem fzJt_FzJ_inv {T : Subgroup G} {a : G} (ha : a ^ 2 * a ^ 2 = 1) (h : FzJ T a) :
    FzJ T a⁻¹ := by
  have hsq : a⁻¹ ^ 2 = a ^ 2 := by
    rw [inv_pow]
    exact inv_eq_of_mul_eq_one_right ha
  have hC : ∀ c ∈ T ⊓ centralizer ({a} : Set G), c ∈ T ⊓ centralizer ({a⁻¹} : Set G) := by
    intro c hc
    refine ⟨hc.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact Commute.inv_right_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hc.2)
  obtain ⟨y, hy, v, hv, w, hw, hy1, hyu, hv2, hw2, hwv, hyv, hyw⟩ := h
  exact ⟨y, hC y hy, v, hC v hv, w, hC w hw, hy1, by rwa [hsq], by rwa [hsq], by rwa [hsq],
    hwv, hyv, hyw⟩

theorem fzJt_notJ_of_notMJ {π : Model →* G} {T₂ : Subgroup G} (hrange : π.range = T₂)
    (hker : ∀ g h : Model, π g = π h ↔ KEq g h) {m : Model} (hm : ¬ MJ m) :
    ¬ FzJ T₂ (π m) := by
  rintro ⟨y, hy, v, hv, w, hw, hy1, hyu, hv2, hw2, hwv, hyv, hyw⟩
  have hyc : y * π m = π m * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
  have hvc : v * π m = π m * v := Subgroup.mem_centralizer_singleton_iff.mp hv.2
  have hwc : w * π m = π m * w := Subgroup.mem_centralizer_singleton_iff.mp hw.2
  obtain ⟨ny, hπy⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hy.1)
  obtain ⟨nv, hπv⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hv.1)
  obtain ⟨nw, hπw⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hw.1)
  refine hm ⟨ny, nv, nw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (hker _ _).mp
    rw [map_mul, map_mul, hπy]
    exact hyc
  · apply (hker _ _).mp
    rw [map_mul, map_mul, hπv]
    exact hvc
  · apply (hker _ _).mp
    rw [map_mul, map_mul, hπw]
    exact hwc
  · intro hk
    apply hy1
    simpa only [map_mul, map_one, hπy, pow_two] using (hker (ny * ny) 1).mpr hk
  · intro hk
    apply hyu
    simpa only [map_mul, hπy, pow_two] using (hker (ny * ny) (m * m)).mpr hk
  · apply (hker (nv * nv) (m * m)).mp
    simpa only [map_mul, hπv, pow_two] using hv2
  · apply (hker (nw * nw) (m * m)).mp
    simpa only [map_mul, hπw, pow_two] using hw2
  · apply (hker (nw * nv * nw⁻¹) (nv⁻¹)).mp
    simpa only [map_mul, map_inv, hπw, hπv] using hwv
  · apply (hker (ny * nv) (nv * ny)).mp
    simpa only [map_mul, hπy, hπv] using hyv
  · apply (hker (ny * nw) (nw * ny)).mp
    simpa only [map_mul, hπy, hπw] using hyw

theorem fzJFailsR3_of_model (h : F2Fact) : FzJFailsR3 := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hset a ha ha2
  obtain ⟨ht2, h1, h2, -⟩ := fzFus_rels hset
  obtain ⟨π, hd, hπ3⟩ := fzJt_dict hset.shape ht2 h1 h2
  obtain ⟨q, rfl⟩ := (fzJt_mem_fzR3_iff hset.shape hπ3).mp ha
  have hq : q * q = QuaternionGroup.a 2 := fzJt_R3_sq hd ha2
  have hnot : ∀ r : Q8, (r = QuaternionGroup.a 1 ∨ r = QuaternionGroup.xa 0 ∨
      r = QuaternionGroup.xa 3) → ¬ FzJ T₂ (π (mkE 1 1 r)) := fun r hr =>
    fzJt_notJ_of_notMJ hd.range_eq hd.eq_iff (h r hr)
  rcases fzJt_q_cases q hq with hr | hr
  · exact hnot q hr
  · intro hJ
    have hinv : π (mkE 1 1 q⁻¹) = (π (mkE 1 1 q))⁻¹ := by
      rw [← fzJt_mkE_inv, map_inv]
    have ha4 : π (mkE 1 1 q) ^ 2 * π (mkE 1 1 q) ^ 2 = 1 := by
      rw [ha2]
      exact fzJt_z3_mul_self hd
    have hJ' := fzJt_FzJ_inv ha4 hJ
    rw [← hinv] at hJ'
    exact hnot q⁻¹ hr hJ'

end CFSG.OddStandard.SmallF3.FritzII
