module

public import CFSG.GF2Type.AschbacherFSmith1977
public import CFSG.GF2Type.ModelPSU
public import CFSG.GF2Type.Entry
public import CFSG.LargeExtraspecial.AS35Holds

public section

namespace CFSG.GF2Type

open CFSG CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.LargeExtraspecial.Bridge

theorem ofFStar_QG {G : Type} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    (hext : timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({z} : Set G)))) :
    (Setting.ofFStar z hz hext).QG =
      inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G)) := by
  rw [Setting.QG, Setting.ofFStar_Q, inSubgroup, generalizedFitting_eq_timmesfeldFStar]
  rfl

theorem aschbacherFSmith1977Statement_holds :
    AschbacherFSmith1977Statement := by
  intro G _ _ _ _ z hz hext w hw h3 hW
  obtain ⟨hext', hcard'⟩ := timmesfeld_hypotheses hext hw
  have hwS : (Setting.ofFStar z hz hext').width = w := width_ofFStar hz hext' hcard'
  have hQ := ofFStar_QG hz hext'
  have hWS : ∀ g : G, g * (Setting.ofFStar z hz hext').z * g⁻¹ ∈
      (Setting.ofFStar z hz hext').QG →
      g * (Setting.ofFStar z hz hext').z * g⁻¹ = (Setting.ofFStar z hz hext').z := by
    intro g hg
    rw [Setting.ofFStar_z] at hg ⊢
    rw [hQ] at hg
    have h := hW g⁻¹ (by simpa only [inv_inv] using hg)
    simpa only [inv_inv] using h
  rcases S14.aschbacherSmith35Input_holds G (Setting.ofFStar z hz hext') (by omega) hWS with
    hU | ⟨h4, hC⟩
  · rw [hwS] at hU
    obtain ⟨e⟩ := hU
    exact Or.inl (lieModel_psu_two_of_mulEquiv (by omega) e)
  · exact Or.inr ⟨hwS ▸ h4, hC⟩

end CFSG.GF2Type
