module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2
import CFSG.ClassicalInvolution.Asc77.AscFusionR10
import CFSG.ClassicalInvolution.Q3.Q3CPSix67
import CFSG.ClassicalInvolution.AschTight.S1916Omega

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

theorem HypOmegaGen.commutes_sylow2In_inf {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (S : Sylow 2 G) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hKS : IsSylow2In ((S : Subgroup G) ⊓ K) K)
    (hJS : IsSylow2In ((S : Subgroup G) ⊓ J) J) :
    Commutes ((S : Subgroup G) ⊓ K) ((S : Subgroup G) ⊓ J) := by
  have hR : ((S : Subgroup G) ⊓ K) ∈ RSet Ω := mem_RSet_of_isSylow2In hK hKS
  have hR' : ((S : Subgroup G) ⊓ J) ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hJS
  have h8 : 8 ≤ Nat.card ↥((S : Subgroup G) ⊓ K) := Sec6Gen.eight_le_of_mem_RSet hΩ hR
  have hne : ((S : Subgroup G) ⊓ K) ≠ ((S : Subgroup G) ⊓ J) := by
    intro heq
    have hle : ((S : Subgroup G) ⊓ K) ≤ J := by
      rw [heq]
      exact inf_le_right
    have hle' := Sec6Gen.card_le_two_of_le_inf hΩ hK hJ hKJ hKS.2.1 inf_le_right hle
    omega
  exact CFSG.ClassicalInvolution.Q3.Q3CP.l67Gen G Ω hΩ S _ hR _ hR' inf_le_left inf_le_left hne

theorem HypOmegaGen.commutes_sylow2In_inf_of_not_twin {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (S : Sylow 2 G) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z t : G}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hJnt : J ∉ twinSet Ω K)
    (hKS : IsSylow2In ((S : Subgroup G) ⊓ K) K)
    (hJS : IsSylow2In ((S : Subgroup G) ⊓ J) J) (hOK : oddCoreOf K = ⊥) :
    Commutes ((S : Subgroup G) ⊓ J) K := by
  have hR' : ((S : Subgroup G) ⊓ J) ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hJS
  have hcomm : Commutes ((S : Subgroup G) ⊓ K) ((S : Subgroup G) ⊓ J) :=
    HypOmegaGen.commutes_sylow2In_inf hΩ S hK hJ hKJ hKS hJS
  have hzK : z ∈ ((S : Subgroup G) ⊓ K) := Sec6Gen.mem_of_isSylow2In hz hKS
  have htJ : t ∈ ((S : Subgroup G) ⊓ J) := Sec6Gen.mem_of_isSylow2In ht hJS
  have hcen : ((S : Subgroup G) ⊓ J) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm z hzK x hx).symm
  have hV : IsSylow2In ((S : Subgroup G) ⊓ J) (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    S1916.IsSylow2In.of_le hJS (le_inf hJS.1 hcen) inf_le_left
  have hnotcyc : ¬ IsCyclic ↥((S : Subgroup G) ⊓ J) := by
    intro hcyc
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR').exists_not_commute
    exact hxy (congrArg Subtype.val (IsMulCommutative.is_comm.comm
      (⟨x, hx⟩ : ↥((S : Subgroup G) ⊓ J)) ⟨y, hy⟩))
  rcases Sec6Gen.l6_2Gen G Ω hΩ K hK z hz J hJ hJnt t ht
    ((S : Subgroup G) ⊓ J) hV htJ with
    ⟨hVeq, -⟩ | ⟨hVeq, -⟩ | ⟨hVU, -⟩ | ⟨-, hcommVK⟩
  · exact absurd (hVeq.symm ▸ Subgroup.isCyclic_zpowers t) hnotcyc
  · exact absurd (hVeq.symm ▸ Subgroup.isCyclic_zpowers t) hnotcyc
  · obtain ⟨-, -, -, hcyc, -⟩ := hVU
    exact absurd hcyc hnotcyc
  · have hbot : ⁅((S : Subgroup G) ⊓ J), K⁆ = ⊥ := by
      rw [hOK] at hcommVK
      exact le_bot_iff.mp hcommVK
    exact commutes_iff_le_centralizer.mpr
      ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot)

theorem HypOmegaGen.le_normalizer_of_commutes_isSylow2In {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {K J R : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylow2In R K) (hcomm : Commutes R J) :
    J ≤ Subgroup.normalizer (K : Set G) := by
  intro j hj
  rw [mem_normalizer_iff_conjSub_eq]
  by_contra hne
  have hconj : conjSub j K ∈ Ω := hΩ.conjInvariant j K hK
  have hle : R ≤ conjSub j K := by
    have hRj : conjSub j R = R := conjSub_eq_of_mem_of_commutes hj hcomm.symm
    intro r hr
    rw [mem_conjSub_iff]
    have hr' : j⁻¹ * r * j ∈ R := by
      have hmem : r ∈ conjSub j R := hRj.symm ▸ hr
      exact mem_conjSub_iff.mp hmem
    exact hR.1 hr'
  have h8 : 8 ≤ Nat.card R :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR)
  have hle' := Sec6Gen.card_le_two_of_le_inf hΩ hK hconj (fun h => hne h.symm) hR.2.1 hR.1 hle
  omega

theorem HypOmegaGen.commutator_eq_bot_of_isSylow2In_inf {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (S : Sylow 2 G) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) (hOK : oddCoreOf K = ⊥) (hOJ : oddCoreOf J = ⊥)
    (hKS : IsSylow2In ((S : Subgroup G) ⊓ K) K) (hJS : IsSylow2In ((S : Subgroup G) ⊓ J) J) :
    ⁅K, J⁆ = ⊥ := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  by_cases hJt : J ∈ twinSet Ω K
  · obtain ⟨-, z', hzK', hzJ'⟩ := hJt
    have hzJ : IsUniqueInvolution J z := (hz.eq hzK').symm ▸ hzJ'
    have hle := Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ hKJ hz hzJ
    exact le_bot_iff.mp (by simpa [hOK, hOJ] using hle)
  · have hzt : z ≠ t := by
      intro h
      exact hJt ⟨hJ, z, hz, h.symm ▸ ht⟩
    have hKt : K ∉ twinSet Ω J := Sec6Gen.not_mem_twinSet ht hz hzt.symm
    have hcommJK : Commutes ((S : Subgroup G) ⊓ K) J :=
      HypOmegaGen.commutes_sylow2In_inf_of_not_twin hΩ S hJ hK hKJ.symm ht hz hKt hJS hKS hOJ
    have hcommKJ : Commutes ((S : Subgroup G) ⊓ J) K :=
      HypOmegaGen.commutes_sylow2In_inf_of_not_twin hΩ S hK hJ hKJ hz ht hJt hKS hJS hOK
    have hJK : J ≤ Subgroup.normalizer (K : Set G) :=
      HypOmegaGen.le_normalizer_of_commutes_isSylow2In hΩ hK hKS hcommJK
    have hKJ' : K ≤ Subgroup.normalizer (J : Set G) :=
      HypOmegaGen.le_normalizer_of_commutes_isSylow2In hΩ hJ hJS hcommKJ
    have hleK : ⁅K, J⁆ ≤ K :=
      (Subgroup.le_normalizer_iff_commutator_le_left (H := J)).mp hJK
    have hleJ : ⁅K, J⁆ ≤ J :=
      (Subgroup.le_normalizer_iff_commutator_le_right (H := K)).mp hKJ'
    have hle : ⁅K, J⁆ ≤ K ⊓ J := le_inf hleK hleJ
    obtain ⟨hpadic_le, hpadic_eq⟩ := hΩ.omega4 K hK J hJ hKJ
    by_cases hpadic : padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1
    · exact le_bot_iff.mp (by simpa [hOK, hOJ] using hpadic_eq hpadic)
    · have hpadic0 : padicValNat 2 (Nat.card ↥(K ⊓ J)) = 0 := by omega
      have hodd : Odd (Nat.card ↥(K ⊓ J)) := by
        rw [← Nat.not_even_iff_odd]
        intro hev
        have hdvd : 2 ∣ Nat.card ↥(K ⊓ J) := even_iff_two_dvd.mp hev
        have h1 := one_le_padicValNat_of_dvd Nat.card_pos.ne' hdvd
        omega
      have hnorm : K ≤ Subgroup.normalizer ((K ⊓ J : Subgroup G) : Set G) := by
        refine (le_inf (Subgroup.le_normalizer (H := K)) hKJ').trans ?_
        exact Subgroup.inf_normalizer_le_normalizer_inf (H := K) (K := J)
      have hleO : (K ⊓ J : Subgroup G) ≤ oddCoreOf K :=
        CFSG.ClassicalInvolution.Asc77.AscFusion.le_oddCoreOf_of_normal_odd inf_le_left hnorm hodd
      have hbot : K ⊓ J = ⊥ := le_bot_iff.mp (by simpa [hOK] using hleO)
      exact le_bot_iff.mp (by simpa [hbot] using hle)

end CFSG.ClassicalInvolution.Disconnected.AschTight
