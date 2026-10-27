module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.Open.FusionDefs

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem holds_two_of_stronglyEmbedded
    (h : ∀ Q : Sylow 2 G, fusionStronglyEmbedded (Subgroup.normalizer ((Q : Subgroup G) : Set G))) :
    Holds G 2 := by
  intro U hU hU2
  obtain ⟨Q, hUQ⟩ := hU2.exists_le_sylow
  set B := Subgroup.normalizer ((Q : Subgroup G) : Set G) with hB
  obtain ⟨hBtop, -, hodd⟩ := h Q
  have hQB : (Q : Subgroup G) ≤ B := Subgroup.le_normalizer
  have hQcore : (Q : Subgroup G) ≤ pCoreOf 2 B :=
    le_pCoreOf_of_le_normalizer 2 hQB le_rfl Q.isPGroup'
  have hsub : ∀ T : Subgroup G, T ≤ B → IsPGroup 2 T → T ≤ Q := by
    intro T hTB hT2
    have hsup : IsPGroup 2 (T ⊔ (Q : Subgroup G) : Subgroup G) :=
      hT2.to_sup_of_normal_right' Q.isPGroup' hTB
    have := Q.is_maximal' hsup le_sup_right
    exact le_sup_left.trans this.le
  have hNU : Subgroup.normalizer (U : Set G) ≤ B := by
    intro g hg
    by_contra hgB
    have hgodd := hodd g hgB
    have hUle : U ≤ B ⊓ B.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro u hu
      refine ⟨hQB (hUQ hu), Subgroup.mem_map.mpr ⟨g * u * g⁻¹, ?_, ?_⟩⟩
      · exact hQB (hUQ ((Subgroup.mem_normalizer_iff.mp hg u).mp hu))
      · simp [mul_assoc]
    have hne : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hU
    obtain ⟨n, hn, hcard⟩ := hU2.nontrivial_iff_card.mp hne
    have hdvd : 2 ∣ Nat.card (B ⊓ B.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) :=
      (dvd_pow_self 2 hn.ne').trans (hcard ▸ Subgroup.card_dvd_of_le hUle)
    exact (Nat.not_even_iff_odd.mpr hgodd) (even_iff_two_dvd.mpr hdvd)
  refine conclusion_of_core 2 U hU2 Q B hBtop hNU ?_ le_rfl
  exact (hsub _ ((pCoreOf_le 2 _).trans hNU) (pCoreOf_isPGroup 2 _)).trans hQcore

end CFSG.LieType.BorelTits
