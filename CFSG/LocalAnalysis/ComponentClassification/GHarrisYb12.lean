module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb5

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem SCert.SE.conj_l_cases : ∀ u : SE, u⁻¹ * gen 1 * u = gen 1 ∨
    u⁻¹ * gen 1 * u = gen 1 * gen 0 := by
  decide +kernel

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

theorem a_not_mem_Y1 (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    D.a ∉ D.Y1 := by
  have h := D.a_not_mem_M1
  rwa [D.M1_eq hO hz] at h

theorem normal_of_Y1_S (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    {K : Subgroup Y} (hY1 : ∀ g ∈ D.Y1, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hS : ∀ s ∈ (D.S : Subgroup Y), ∀ k ∈ K, s * k * s⁻¹ ∈ K) : K.Normal := by
  refine ⟨fun k hk g => ?_⟩
  by_cases hg : g ∈ D.Y1
  · exact hY1 g hg k hk
  · have haY := D.a_not_mem_Y1 hO hz
    have hga : g * D.a⁻¹ ∈ D.Y1 := by
      rw [mul_mem_iff_of_index_two (D.index_centralizer_l hO hz), inv_mem_iff]
      exact iff_of_false hg haY
    have h := hY1 _ hga _ (hS D.a (D.toG_mem _) k hk)
    rwa [show g * D.a⁻¹ * (D.a * k * D.a⁻¹) * (g * D.a⁻¹)⁻¹ = g * k * g⁻¹ by group] at h

theorem E_normal_of (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    (hE : D.Et.Normal) : D.E.Normal := by
  refine D.normal_of_Y1_S hO hz (fun g hg e he => ?_) (fun s hs e he => ?_)
  · have h1 : D.piX ⟨e, D.E_le_Y1 he⟩ ∈ D.Et := (D.piX_mem_Et_iff _).mpr he
    have h2 := hE.conj_mem _ h1 (D.piX ⟨g, hg⟩)
    rw [← map_inv D.piX, ← map_mul D.piX, ← map_mul D.piX] at h2
    exact (D.piX_mem_Et_iff _).mp h2
  · have h := D.conj_mem_E (inv_mem hs) he
    rwa [inv_inv] at h

theorem F_normal_of (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    (hF : D.Ft.Normal) : D.F.Normal := by
  refine D.normal_of_Y1_S hO hz (fun g hg f hf => ?_) (fun s hs f hf => ?_)
  · have h1 : D.piX ⟨f, D.F_le_Y1 hf⟩ ∈ D.Ft := (D.piX_mem_Ft_iff _).mpr hf
    have h2 := hF.conj_mem _ h1 (D.piX ⟨g, hg⟩)
    rw [← map_inv D.piX, ← map_mul D.piX, ← map_mul D.piX] at h2
    exact (D.piX_mem_Ft_iff _).mp h2
  · have h := D.conj_mem_F (inv_mem hs) hf
    rwa [inv_inv] at h

theorem centralizer_E_le_of (hCE : centralizer (D.Et : Set D.Xt) ≤ D.Et) :
    centralizer (D.E : Set Y) ≤ D.E := by
  intro c hc
  have hcY : c ∈ D.Y1 :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc D.l D.l_mem_E).symm
  have h : D.piX ⟨c, hcY⟩ ∈ D.Et := hCE (mem_centralizer_iff.mpr fun w hw => by
    obtain ⟨e, he, rfl⟩ := hw
    rw [← map_mul D.piX, ← map_mul D.piX]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp hc (e : Y) (mem_subgroupOf.mp he)))
  exact (D.piX_mem_Et_iff _).mp h

theorem piX_mem_sylowXt_iff (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    (y : D.Y1) :
    D.piX y ∈ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) ↔ (y : Y) ∈ D.S1 := by
  constructor
  · intro h
    rw [D.coe_sylowXt hO hz] at h
    obtain ⟨s, hs, hsy⟩ := h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      D.mem_zpowers_l_iff] at hsy
    have hl : ((s⁻¹ * y : D.Y1) : Y) ∈ D.S1 := by
      rcases hsy with h | h | h | h <;> rw [h]
      · exact one_mem _
      · exact D.toG_mem_S1 (by decide)
      · exact D.toG_mem_S1 (by decide)
      · exact mul_mem (D.toG_mem_S1 (by decide)) (D.toG_mem_S1 (by decide))
    have h2 := mul_mem (mem_subgroupOf.mp hs) hl
    rwa [← Subgroup.coe_mul, mul_inv_cancel_left] at h2
  · intro h
    exact D.mem_sylowXt hO hz ⟨y, mem_subgroupOf.mpr h⟩

theorem S1_normal_of (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    (hT : ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt).Normal) : D.S1.Normal := by
  refine D.normal_of_Y1_S hO hz (fun g hg s hs => ?_) (fun u hu s hs => ?_)
  · have h1 := (D.piX_mem_sylowXt_iff hO hz ⟨s, D.S1_le_Y1 hs⟩).mpr hs
    have h2 := hT.conj_mem _ h1 (D.piX ⟨g, hg⟩)
    rw [← map_inv D.piX, ← map_mul D.piX, ← map_mul D.piX] at h2
    exact (D.piX_mem_sylowXt_iff hO hz _).mp h2
  · refine mem_inf.mpr ⟨mul_mem (mul_mem hu (mem_inf.mp hs).1) (inv_mem hu), ?_⟩
    have hl : u⁻¹ * D.l * u = D.l ∨ u⁻¹ * D.l * u = D.l * D.z := by
      obtain ⟨u₀, rfl⟩ := D.exists_toG hu
      rcases SE.conj_l_cases u₀ with h | h
      · left
        rw [← map_inv, ← map_mul, ← map_mul, h]
      · right
        rw [← map_inv, ← map_mul, ← map_mul, h, map_mul]
    have hsl := mem_centralizer_singleton_iff.mp (mem_inf.mp hs).2
    have hsz : s * D.z = D.z * s :=
      mem_centralizer_singleton_iff.mp (D.S_le_centralizer_z (mem_inf.mp hs).1)
    have hslz : s * (D.l * D.z) = D.l * D.z * s := by
      rw [← mul_assoc, hsl, mul_assoc, hsz, ← mul_assoc]
    rw [mem_centralizer_singleton_iff]
    rcases hl with h | h
    · calc u * s * u⁻¹ * D.l = u * (s * (u⁻¹ * D.l * u)) * u⁻¹ := by group
        _ = u * ((u⁻¹ * D.l * u) * s) * u⁻¹ := by rw [h, hsl]
        _ = D.l * (u * s * u⁻¹) := by group
    · calc u * s * u⁻¹ * D.l = u * (s * (u⁻¹ * D.l * u)) * u⁻¹ := by group
        _ = u * ((u⁻¹ * D.l * u) * s) * u⁻¹ := by rw [h, hslz]
        _ = D.l * (u * s * u⁻¹) := by group

theorem centralizer_S1_le_of (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    (hCT : centralizer (((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) : Set D.Xt) ≤
      ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) :
    centralizer (D.S1 : Set Y) ≤ D.S1 := by
  intro c hc
  have hlS : D.l ∈ D.S1 := D.toG_mem_S1 (by decide)
  have hcY : c ∈ D.Y1 := mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc D.l hlS).symm
  refine (D.piX_mem_sylowXt_iff hO hz ⟨c, hcY⟩).mp (hCT (mem_centralizer_iff.mpr fun w hw => ?_))
  obtain ⟨s, rfl⟩ := D.exists_S1Y_of_mem hO hz hw
  rw [← map_mul D.piX, ← map_mul D.piX]
  congr 1
  exact Subtype.ext (mem_centralizer_iff.mp hc ((s : D.Y1) : Y) (mem_subgroupOf.mp s.2))

theorem relIndex_S1_Y1 (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    D.S1.relIndex D.Y1 = ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt).index := by
  have hker : (zpowers D.lY) ≤ D.S1.subgroupOf D.Y1 := by
    rw [zpowers_le, mem_subgroupOf]
    exact D.toG_mem_S1 (by decide)
  rw [D.coe_sylowXt hO hz, Subgroup.relIndex]
  refine (index_map_eq (D.S1.subgroupOf D.Y1) (QuotientGroup.mk'_surjective _) ?_).symm
  rw [QuotientGroup.ker_mk']
  exact hker

end GHSylow

end CFSG.ComponentClassification.GHarris
