module

public import CFSG.HardMathSupport.Foote.E27.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCent

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralCensus Subgroup

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem false_of_perfect_in_K (h : E27Config X K R T z) (hz : z ∈ K)
    (hV : ∃ V : Subgroup K, V ≤ centralizer ({(⟨z, hz⟩ : K)} : Set K) ∧ ⁅V, V⁆ = V ∧
      3 ∣ Nat.card V) : False := by
  obtain ⟨V, hVc, hVp, hV3⟩ := hV
  refine h.perfect (V.map K.subtype) ?_ ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.1 (hVc hv)
    exact congrArg Subtype.val this
  · rw [← Subgroup.map_commutator, hVp]
  · rwa [Subgroup.card_map_of_injective K.subtype_injective]

theorem false_of_centNoncycThree (h : E27Config X K R T z) (hz : z ∈ K)
    (hK : CentNoncycThreeGroup K) : False := by
  have h3 : (⟨z, hz⟩ : K) ^ 3 = 1 := Subtype.ext (h.elem.2 z h.z_mem)
  have h1 : (⟨z, hz⟩ : K) ≠ 1 := by
    intro h1
    apply h.z_not_mem
    have : z = 1 := congrArg Subtype.val h1
    rw [this]
    exact one_mem _
  obtain ⟨V, hVc, hVp, Q, hQV, hQ3, hQnc⟩ := hK _ h3 h1
  refine false_of_perfect_in_K h hz ⟨V, hVc, hVp, ?_⟩
  obtain ⟨n, hn⟩ := hQ3.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hQnc
    have : Subsingleton Q := (Nat.card_eq_one_iff_unique.1 (by simpa using hn)).1
    infer_instance
  exact (dvd_pow_self 3 hn0).trans (hn ▸ Subgroup.card_dvd_of_le hQV)

theorem false_of_even_classical (h : E27Config X K R T z) (hz : z ∈ K)
    (d : TauCeti.ValidLieTypeIndex)
    (hd : IdxBCent d.1 ∨ IdxDCent d.1 ∨ IdxTwistedDCent d.1)
    (e : Nonempty (↥K ≃* (TauCeti.CFSGIndex.lie d).Group)) : False := by
  refine false_of_centNoncycThree h hz ?_
  rcases hd with hd | hd | hd
  · exact centNoncycThreeGroup_of_isLieOf_b ⟨d, hd, e⟩
  · exact centNoncycThreeGroup_of_isLieOf_d ⟨d, hd, e⟩
  · exact centNoncycThreeGroup_of_isLieOf_twistedD ⟨d, hd, e⟩

end CFSG.HardMathSupport.Malle.E27Lie
