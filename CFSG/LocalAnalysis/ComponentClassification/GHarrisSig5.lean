module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisNX4
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSigZ

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

theorem fusN_10_20 (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a) :
    D.FusN 1 0 ∧ D.FusN 2 0 := by
  by_cases hB : D.caseB
  · obtain ⟨hP, -⟩ := D.fusion_B hC hidx hxa hB
    exact ⟨hP 1 (by decide), hP 2 (by decide)⟩
  · obtain ⟨hP, -⟩ := D.fusion_A hC hidx hxa hB
    exact ⟨hP 1 (by decide), hP 2 (by decide)⟩

theorem sigW_V_eq_bot (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hOG : pPrimeCore 2 G = ⊥) : sigW D.V = ⊥ := by
  obtain ⟨h10, h20⟩ := D.fusN_10_20 hC hidx hxa
  have htop : normalizer (sigW D.V : Set G) = ⊤ := by
    by_cases hB : D.caseB
    · exact D.H_eq_top_B' hC hidx hxa hB
    · exact D.H_eq_top_A' hC hidx hxa hB
  have hn : (sigW D.V).Normal := normalizer_eq_top_iff.mp htop
  have hle : sigW D.V ≤ pPrimeCore 2 G := le_sSup ⟨hn, (D.sigW_V_spec hC h10 h20).1.1⟩
  rw [hOG] at hle
  exact eq_bot_iff.mpr hle

theorem oddCore_M_eq_bot (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hOG : pPrimeCore 2 G = ⊥) : pPrimeCore 2 ↥D.M = ⊥ := by
  have h := D.OM_le_W
  rw [D.sigW_V_eq_bot hC hidx hxa hOG, le_bot_iff] at h
  exact (map_eq_bot_iff_of_injective _ D.M.subtype_injective).mp h

theorem oddCent_eq_bot (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hOG : pPrimeCore 2 G = ⊥) {u : G} (hu : u * u = 1) (huz : u * D.z = D.z * u)
    (hut : u * D.t = D.t * u) : oddCent (zpowers u) = ⊥ := by
  obtain ⟨h10, h20⟩ := D.fusN_10_20 hC hidx hxa
  have h := D.oddCent_le_W hC h10 h20 hu huz hut
  rwa [D.sigW_V_eq_bot hC hidx hxa hOG, le_bot_iff] at h

end GHSylow

end CFSG.ComponentClassification.GHarris
