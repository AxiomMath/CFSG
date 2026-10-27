module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2Open
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE2Tools
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4D0
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCommon

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ComponentClassification.RankTwoExceptional.D4

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem d4_not_isPGroup_of_orbit
    [CharP K 2] (hσ : σ ^ 3 = 1) (a : Fin TwistTag.D4.foldedTag.rank) {x : ↥(d4C K σ)}
    (hx : ∀ s, orbitRankOneHom TwistTag.D4 K σ.toRingHom a s * (x : ModGL TwistTag.D4.tag K) =
      (x : ModGL TwistTag.D4.tag K) * orbitRankOneHom TwistTag.D4 K σ.toRingHom a s) :
    ¬ IsPGroup 2 ↥(centralizer ({x} : Set ↥(d4C K σ))) := by
  have H := (triality_all_characteristic_faithful_torus_coordinates K σ hσ).2.2.2.2.1 a
  have : CharP (orbitField TwistTag.D4 K σ.toRingHom a) 2 :=
    (orbitField TwistTag.D4 K σ.toRingHom a).subtype.charP Subtype.val_injective 2
  exact not_isPGroup_of_sl2 ((orbitRankOneHom TwistTag.D4 K σ.toRingHom a).codRestrict
    (d4C K σ) fun s => H.1 ⟨s, rfl⟩) (fun s s' h => H.2 (congrArg Subtype.val h))
    fun s => Subtype.ext (hx s)

theorem d4t_centralizer_not_isPGroup
    [CharP K 2] (hσ : σ ^ 3 = 1) {t : ↥(d4C K σ)}
    (ht : (t : ModGL TwistTag.D4.tag K) = d4t K σ) :
    ¬ IsPGroup 2 ↥(centralizer ({t} : Set ↥(d4C K σ))) := by
  refine d4_not_isPGroup_of_orbit σ hσ ⟨1, by decide⟩ fun s => ?_
  have hs : orbitRankOneHom TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ s ∈ d4Ma K σ := by
    rw [d4Ma, orbitRankOneGroup, ← orbitRankOneHom_range]
    exact ⟨s, rfl⟩
  rw [ht]
  exact (d4Ma_commute_d4x₄ σ _ hs 1).symm

theorem d4z_centralizer_not_isPGroup
    [Finite K] [CharP K 2] (h3 : ∀ c, σ (σ (σ c)) = c) {z : ↥(d4C K σ)}
    (hz : (z : ModGL TwistTag.D4.tag K) = d4z K) :
    ¬ IsPGroup 2 ↥(centralizer ({z} : Set ↥(d4C K σ))) := by
  refine d4_not_isPGroup_of_orbit σ (ringEquiv_cube_d4 σ h3) ⟨0, by decide⟩ fun s => ?_
  have hs : orbitRankOneHom TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ s ∈ d4Mr K σ := by
    rw [d4Mr, orbitRankOneGroup, ← orbitRankOneHom_range]
    exact ⟨s, rfl⟩
  rw [hz]
  exact mem_centralizer_singleton_iff.mp
    (d4Vr_sup_d4Mr_le_centralizer σ h3 (Subgroup.mem_sup_right hs))

theorem d4_centralizer_not_isPGroup
    [Finite K] [CharP K 2] (h3 : ∀ c, σ (σ (σ c)) = c) {c : ↥(d4C K σ)}
    (hc : orderOf c = 2) :
    ¬ IsPGroup 2 ↥(centralizer ({c} : Set ↥(d4C K σ))) := by
  have hz : d4z K ∈ d4C K σ := (d4x_long_mem σ (map_one σ)).2.2
  have ht : d4t K σ ∈ d4C K σ := (d4x_short_mem σ (toRingHom_pow_three_d4 σ h3) 1).2.2
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc
    exact absurd hc (by decide)
  obtain ⟨y, hy, hyc⟩ :=
    d4_classesCover σ h3 (z := ⟨_, hz⟩) (t := ⟨_, ht⟩) rfl rfl c hc2 hc1
  refine not_isPGroup_centralizer_of_isConj hyc ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · exact d4z_centralizer_not_isPGroup σ h3 rfl
  · exact d4t_centralizer_not_isPGroup σ (ringEquiv_cube_d4 σ h3) rfl

end CFSG.ComponentClassification.HarrisLit.L33.SR.E2

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ComponentClassification.RankTwoExceptional.D4

theorem involutionCentralizerNotTwoGroup_trialityD4
    : InvolutionCentralizerNotTwoGroup .trialityD4 := by
  intro Y _ _ f hY _ c hc
  obtain ⟨⟨-, hf, -⟩, hm⟩ := hY
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hm
  have hK3 : Nat.card K = (2 ^ f) ^ 3 := hK
  have : CharP K 2 := charP_two_of_card_d4 hK3
  exact SR.E2.not_isPGroup_of_mulEquiv e c (SR.E2.d4_centralizer_not_isPGroup σ
    (sigma_cube_of_card_d4 σ hK3 hσ) (by rw [MulEquiv.orderOf_eq]; exact hc))

end CFSG.ComponentClassification.HarrisLit.L33.E2
