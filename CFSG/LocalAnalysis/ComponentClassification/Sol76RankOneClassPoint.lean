module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Tools

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

namespace RankOneClass

theorem exists_involution {K H : Subgroup G} (hK : IsTwoComponentIn K H) :
    ∃ b ∈ K, orderOf b = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card K := by
    by_contra h
    exact UnbalancedCorr.not_le_of_isPComponent_of_coprime hK.1 hK.2
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h) le_rfl
  obtain ⟨⟨b, hbK⟩, hb⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact ⟨b, hbK, by rwa [Subgroup.orderOf_mk] at hb⟩

theorem exists_central_involution {T : Subgroup G} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) :
    ∃ t ∈ T, orderOf t = 2 ∧ ∀ s ∈ T, s * t = t * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT
  have hZ : Nontrivial (center T) := hT2.center_nontrivial
  obtain ⟨n, hn0, hn⟩ := ((hT2.to_subgroup (center T)).nontrivial_iff_card).mp hZ
  have h2 : 2 ∣ Nat.card (center T) := hn ▸ dvd_pow_self 2 hn0.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center T) 2 h2
  refine ⟨((z : T) : G), (z : T).2, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  · exact congrArg Subtype.val (mem_center_iff.mp z.2 ⟨s, hs⟩)

theorem solomonLt_witness {K T : Subgroup G} (hK : IsSolomonMember K) (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hTQ : T ≤ coreActionKernel K)
    (hKT : IsTwoComponentIn (oddResidualIn (oddCoreIn (centralizer (T : Set G)) ⊔
      (K ⊓ centralizer (T : Set G)))) (centralizer (T : Set G))) :
    SolomonLt K (oddResidualIn (oddCoreIn (centralizer (T : Set G)) ⊔
      (K ⊓ centralizer (T : Set G)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKq := isQuasisimple_coreQuot_of_isSolomonMember hK
  obtain ⟨hRY, hLY, -, -⟩ :=
    cover_facts hKq inf_le_left (inf_centralizer_sup_oddCoreIn_eq hT2 hTQ)
  have hRL := twoLayer_inf_centralizer_le_of_witness hKq hT2 hTQ hKT
  have hRKT : twoLayerIn (K ⊓ centralizer (T : Set G)) ≤
      oddResidualIn (oddCoreIn (centralizer (T : Set G)) ⊔ (K ⊓ centralizer (T : Set G))) := by
    rw [hLY]
    exact oddResidualIn_mono le_sup_right
  have hRperf : ⁅twoLayerIn (K ⊓ centralizer (T : Set G)),
      twoLayerIn (K ⊓ centralizer (T : Set G))⁆ = twoLayerIn (K ⊓ centralizer (T : Set G)) := by
    rw [hLY]
    exact UnbalancedCorr.commutator_eq_of_isPComponent hRY.1 hRY.2
  have hRinv : ∃ b ∈ twoLayerIn (K ⊓ centralizer (T : Set G)), orderOf b = 2 := by
    rw [hLY]
    exact exists_involution hRY
  exact ⟨hK, isSolomonMember_of_isTwoComponentIn hT hT2 hKT, T, hT2, hTQ,
    isTwoComponentIn_conjClosure_of_not_le hKT hRL
      (not_le_coreActionKernel_of_le hRKT hRperf hRinv)⟩

end RankOneClass

theorem exists_twoComponent_centralizer_of_isSolomonMaximal {K : Subgroup G}
    (hK : IsSolomonMaximal K) :
    ∃ t : G, orderOf t = 2 ∧ ∃ M : Subgroup G,
      IsTwoComponentIn M (centralizer ({t} : Set G)) ∧ SolomonEquiv K M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, T, hT, hT2, hTQ, hKT⟩ := hK.1
  have hlt := RankOneClass.solomonLt_witness hK.1 hT hT2 hTQ hKT
  set C := centralizer (T : Set G) with hC
  set KT := oddResidualIn (oddCoreIn C ⊔ (K ⊓ C)) with hKTdef
  have hKKT : SolomonEquiv K KT := hK.2 K KT ⟨hK.1, Relation.ReflTransGen.refl⟩ hlt
  have hKTmax : IsSolomonMaximal KT := isSolomonMaximal_of_solomonEquiv hK hKKT
  obtain ⟨t, htT, ht, htc⟩ := RankOneClass.exists_central_involution hT hT2
  have hCt : C ≤ centralizer ({t} : Set G) := centralizer_le (Set.singleton_subset_iff.mpr htT)
  have hTt : T ≤ centralizer ({t} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (htc s hs)
  have hLL : twoLayerIn C ≤ twoLayerIn (centralizer ({t} : Set G)) := by
    have h := GrSLit.pLayer_inf_centralizer_le_of_normalizes (Q := centralizer ({t} : Set G)) hT2
      (hTt.trans le_normalizer)
    rw [inf_eq_right.mpr hCt] at h
    exact h
  have hKTL : KT ≤ twoLayerIn (centralizer ({t} : Set G)) :=
    (le_twoLayerIn_of_isTwoComponentIn hKT).trans hLL
  have hKTt : KT ≤ centralizer ({t} : Set G) := hKT.1.trans hCt
  obtain ⟨M, hM, hKTM⟩ := Sol76T13.exists_not_le_coreActionKernel_of_le_twoLayerIn
    (UnbalancedCorr.commutator_eq_of_isPComponent hKT.1 hKT.2) hKTL
    (RankOneClass.exists_involution hKT)
  exact ⟨t, ht, M, hM, ⟨hK.1, hKKT.2.trans
    (solomonEquiv_of_not_le_coreActionKernel ht hKT hKTmax hKTt hKTL hM hKTM).2⟩⟩

end CFSG.ComponentClassification.Sol76
