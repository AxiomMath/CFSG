module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Central
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.FusionInterface
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Step3b

public section

namespace CFSG.EvenSporadicStandard.J4Std.EgawaApply

open Subgroup

variable {G : Type} [Group G] {L U T0 : Subgroup G} {z : G} {Y : Subgroup G}

theorem centralizer_eq_Vsub (hS : Setting L z) : centralizer ({z} : Set G) = Vsub L z := by
  ext g
  rw [mem_centralizer_singleton_iff, mem_Vsub_iff hS le_rfl]
  constructor
  · intro hg
    obtain ⟨l, hl, hgl⟩ := hS.centralizer_z g hg.symm
    refine ⟨l, hl, ?_⟩
    rcases hgl with hgl | hgl
    · exact Or.inl hgl
    · exact Or.inr (hgl.trans (hS.z_comm l hl).symm)
  · rintro ⟨u, hu, hgu | hgu⟩
    · rw [hgu]
      exact (hS.z_comm u hu).symm
    · rw [hgu]
      calc z * u * z = z * (u * z) := by group
        _ = z * (z * u) := by rw [hS.z_comm u hu]

theorem normalizer_inf_centralizer (hS : Setting L z) (hD : LocalData L U T0)
    (hF : FusionData L U z Y) :
    normalizer (Y : Set G) ⊓ centralizer ({z} : Set G) = Vsub (Hloc L U) z := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  rw [← N_inf_centralizer_eq hS hUL]
  apply le_antisymm
  · rintro g hg
    obtain ⟨hgM, hgC⟩ := mem_inf.1 hg
    refine mem_inf.2 ⟨hF.cent_le_N g hgM 1 (one_mem Y) ?_, hgC⟩
    have := mem_centralizer_singleton_iff.1 hgC
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [this]
      _ = z * 1 := by group
  · exact inf_le_inf_right _ hF.N_le_M

theorem relIndex_normalizer_eq [Finite G] (hS : Setting L z) (hD : LocalData L U T0)
    (hF : FusionData L U z Y) :
    (normalizer (Y : Set G)).relIndex (centralizer ({z} : Set G)) = (Hloc L U).relIndex L := by
  have h1 := relIndex_mul_card (normalizer (Y : Set G)) (centralizer ({z} : Set G))
  have h2 := relIndex_mul_card (Hloc L U) L
  have hC : Nat.card (centralizer ({z} : Set G)) = 2 * Nat.card L := by
    rw [centralizer_eq_Vsub hS]
    exact card_Vsub hS le_rfl
  have hA : Nat.card (normalizer (Y : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) =
      2 * Nat.card (Hloc L U) := by
    rw [normalizer_inf_centralizer hS hD hF]
    exact card_Vsub hS Hloc_le_L
  rw [hA, hC, mul_left_comm] at h1
  rw [inf_eq_left.2 Hloc_le_L] at h2
  have hpos : 0 < Nat.card (Hloc L U) := Nat.card_pos
  have : (normalizer (Y : Set G)).relIndex (centralizer ({z} : Set G)) * Nat.card (Hloc L U) =
      (Hloc L U).relIndex L * Nat.card (Hloc L U) := by omega
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem not_two_dvd_relIndex [Finite G] (hS : Setting L z) (hD : LocalData L U T0)
    (hF : FusionData L U z Y) :
    ¬ 2 ∣ (normalizer (Y : Set G)).relIndex (centralizer ({z} : Set G)) := by
  rw [relIndex_normalizer_eq hS hD hF]
  intro h2
  have h3 := relIndex_mul_relIndex T0 (Hloc L U) L (T0_le_Hloc hD) Hloc_le_L
  exact hD.T0_index_odd (h3 ▸ Dvd.dvd.mul_left h2 _)

end CFSG.EvenSporadicStandard.J4Std.EgawaApply
