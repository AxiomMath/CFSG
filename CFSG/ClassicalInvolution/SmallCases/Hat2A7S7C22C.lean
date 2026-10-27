module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7C22A
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Frame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance

section Layer


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {K₁ K₂ K₃ R₁ R₂ R₃ : Subgroup G} {u₁ u₂ u₃ : G}
  (F : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃) (hΩ : HypOmegaGen Ω)
include F hΩ

theorem Frame3.le_N₁₂ : K₁ ≤ Subgroup.normalizer (K₂ : Set G) :=
  Sec6Gen.le_normalizer_of_twin hΩ F.mem₁ F.mem₂ F.ne₁₂.symm F.hz₁ F.hz₂

theorem Frame3.le_N₁₃ : K₁ ≤ Subgroup.normalizer (K₃ : Set G) :=
  Sec6Gen.le_normalizer_of_twin hΩ F.mem₁ F.mem₃ F.ne₁₃.symm F.hz₁ F.hz₃

theorem Frame3.le_N₂₁ : K₂ ≤ Subgroup.normalizer (K₁ : Set G) :=
  Sec6Gen.le_normalizer_of_twin hΩ F.mem₂ F.mem₁ F.ne₁₂ F.hz₂ F.hz₁

theorem Frame3.le_N₂₃ : K₂ ≤ Subgroup.normalizer (K₃ : Set G) :=
  Sec6Gen.le_normalizer_of_twin hΩ F.mem₂ F.mem₃ F.ne₂₃.symm F.hz₂ F.hz₃

theorem Frame3.le_N₃₁ : K₃ ≤ Subgroup.normalizer (K₁ : Set G) :=
  Sec6Gen.le_normalizer_of_twin hΩ F.mem₃ F.mem₁ F.ne₁₃ F.hz₃ F.hz₁

theorem Frame3.le_N₃₂ : K₃ ≤ Subgroup.normalizer (K₂ : Set G) :=
  Sec6Gen.le_normalizer_of_twin hΩ F.mem₃ F.mem₂ F.ne₂₃ F.hz₃ F.hz₂

theorem Frame3.xMem₃ {c : G} (hc : ∃ a ∈ R₁, ∃ b ∈ R₂, c = a * b) : T8.XMem Ω c K₃ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hc
  refine ⟨F.mem₃, ?_, R₃, F.syl₃, fun r hr => ?_⟩
  · exact (Subgroup.normalizer (K₃ : Set G)).mul_mem (F.le_N₁₃ hΩ (F.syl₁.1 ha))
      (F.le_N₂₃ hΩ (F.syl₂.1 hb))
  · have h1 : a * r = r * a := F.comm₁₃ a ha r hr
    have h2 : b * r = r * b := F.comm₂₃ b hb r hr
    calc r * (a * b) = (r * a) * b := by group
      _ = (a * r) * b := by rw [h1]
      _ = a * (r * b) := by group
      _ = a * (b * r) := by rw [h2]
      _ = a * b * r := by group

theorem Frame3.xMem₁ {c : G} (hc : ∃ a ∈ R₂, ∃ b ∈ R₃, c = a * b) : T8.XMem Ω c K₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hc
  refine ⟨F.mem₁, ?_, R₁, F.syl₁, fun r hr => ?_⟩
  · exact (Subgroup.normalizer (K₁ : Set G)).mul_mem (F.le_N₂₁ hΩ (F.syl₂.1 ha))
      (F.le_N₃₁ hΩ (F.syl₃.1 hb))
  · have h1 : r * a = a * r := F.comm₁₂ r hr a ha
    have h2 : r * b = b * r := F.comm₁₃ r hr b hb
    calc r * (a * b) = (r * a) * b := by group
      _ = (a * r) * b := by rw [h1]
      _ = a * (r * b) := by group
      _ = a * (b * r) := by rw [h2]
      _ = a * b * r := by group

theorem Frame3.xMem₂ {c : G} (hc : ∃ a ∈ R₁, ∃ b ∈ R₃, c = a * b) : T8.XMem Ω c K₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hc
  refine ⟨F.mem₂, ?_, R₂, F.syl₂, fun r hr => ?_⟩
  · exact (Subgroup.normalizer (K₂ : Set G)).mul_mem (F.le_N₁₂ hΩ (F.syl₁.1 ha))
      (F.le_N₃₂ hΩ (F.syl₃.1 hb))
  · have h1 : a * r = r * a := F.comm₁₂ a ha r hr
    have h2 : r * b = b * r := F.comm₂₃ r hr b hb
    calc r * (a * b) = (r * a) * b := by group
      _ = (a * r) * b := by rw [h1]
      _ = a * (r * b) := by group
      _ = a * (b * r) := by rw [h2]
      _ = a * b * r := by group

end Layer

section Hyp51Ne


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G} {z : G}

theorem zStar_of_xMem (hs : Pre2A7 Ω K₀) {c : G} {K : Subgroup G} (hK : T8.XMem Ω c K)
    (hz : IsUniqueInvolution K z) (hc2 : c * c = 1) (hc1 : c ≠ 1) :
    z ∈ T8.layerJoin Ω c ∧
      ∀ y ∈ T8.layerJoin Ω c, z * y * z⁻¹ * y⁻¹ ∈ oddCoreOf (T8.layerJoin Ω c) := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hL : Hat2A7S8.Asc77.T8.LayerHyp Ω c := Hat2A7S8.layerHyp_of_pre hs hc2 hc1
  have hF := Hat2A7S8.Asc77.T8.LayerFam.layerSet hΩ hK
  have hLΛ : T8.layerRes c K ∈ T8.layerSet Ω c := ⟨K, hK, rfl⟩
  have huL : z ∈ T8.layerRes c K :=
    (Hat2A7S8.Asc77.T8.XMem.isUniqueInvolution_layerRes hΩ hs.classical hc2 hK hz).mem
  have hu : ∀ a ∈ T8.layerRes c K, a * z = z * a := fun a ha =>
    Hat2A7S8.comm_of_mem_isUniqueInvolution hz (T8.layerRes_le c K ha)
  exact ⟨T8.le_layerJoin hLΛ huL, fun y hy => hF.commutator_mem_oddCoreOf hL hLΛ huL hu hy⟩

variable {K₁ K₂ K₃ R₁ R₂ R₃ : Subgroup G} {u₁ u₂ u₃ : G}

theorem Frame3.hyp51At_ne (hs : Pre2A7 Ω K₀) (F : Frame3 Ω z K₁ K₂ K₃ R₁ R₂ R₃ u₁ u₂ u₃) {c : G}
    (hcB : c ∈ Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)) (hc1 : c ≠ 1) (hcz : c ≠ z) :
    Hyp51At (Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G)) c := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hB := F.isElemAbelian_B hΩ
  have hB2 : ∀ x ∈ Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G), x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hB.2 x hx
  have hc2 : c * c = 1 := hB2 c hcB
  have hcord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
  obtain ⟨K, hKx, hzK⟩ : ∃ K, T8.XMem Ω c K ∧ IsUniqueInvolution K z := by
    rcases F.mem_B_cases hΩ hcB with h | h | h | h | h
    · exact absurd h hc1
    · exact absurd h hcz
    · exact ⟨K₃, F.xMem₃ hΩ h, F.hz₃⟩
    · exact ⟨K₁, F.xMem₁ hΩ h, F.hz₁⟩
    · exact ⟨K₂, F.xMem₂ hΩ h, F.hz₂⟩
  obtain ⟨hbY, hZ⟩ := zStar_of_xMem hs hKx hzK hc2 hc1
  have hF := Hat2A7S8.Asc77.T8.LayerFam.layerSet hΩ hKx
  have hzB : z ∈ Subgroup.closure ({z, u₁ * u₂, u₂ * u₃} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hzc : z ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (DeltaClosure.comm_of_mem_elemAbelian hB hzB hcB)
  refine Hat2A7S8.hyp51At_of_zStar hB2 hcB hzB ?_ hzc ?_ ?_ hbY hZ
  · intro h
    rcases T7A.eq_one_or_eq_of_mem_zpowers hcord h with h1 | h1
    · exact F.z_ne_one h1
    · exact hcz h1.symm
  · rw [← T8.cenZ_eq_centralizer]
    exact T8.layerJoin_le_cenZ c
  · intro n hn
    have hn' : n ∈ T8.cenZ c := by
      rw [T8.cenZ_eq_centralizer]
      exact hn
    exact hF.conjSub_famJoin hn'

end Hyp51Ne

end CFSG.ClassicalInvolution.Hat2A7S
