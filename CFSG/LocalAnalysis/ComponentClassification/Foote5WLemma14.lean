module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76R12Sp4
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Measure

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.Sol76 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem isKBalanced_of_central_of_rank {N M M' : Subgroup G} {t : G} (htN : t ∈ N)
    (hcent : ∀ n ∈ N, n * t = t * n) (ht : orderOf t = 2) (hM : M ∈ kStarComponents N)
    (hM' : M' ∈ kStarComponents N) (hMM' : M ≠ M')
    (h3 : 3 ≤ CFSG.pRank 2 ↥((FooteLit.oddTwoCoreIn N ⊔ FooteLit.twoLayerIn N) ⊓
      UnbalancedLayer.coreActionKernel M')) :
    FooteLit.IsKBalanced N := by
  classical
  have h2 : 2 ≤ (kStarComponents N).ncard := by
    rw [← Set.ncard_pair hMM']
    exact Set.ncard_le_ncard (Set.insert_subset hM (Set.singleton_subset_iff.mpr hM'))
  obtain ⟨Kf, hinj, hiff⟩ := Sol76T13.exists_enum_kStarComponents N
  have hKf : ∀ i, Kf i ∈ kStarComponents N := fun i => (hiff (Kf i)).mpr ⟨i, rfl⟩
  obtain ⟨i₀, hi₀⟩ := (hiff M').mp hM'
  refine ⟨_, Kf, hinj, hiff, h2, fun i j hij => ?_, ⟨i₀, ?_⟩, Or.inr (Or.inl ?_)⟩
  · exact FooteLit.commutator_le_oddCoreIn_of_ne (hKf i).1 (hKf j).1 fun h => hij (hinj h)
  · rw [hi₀]
    exact h3
  · have htY : t ∈ (FooteLit.oddTwoCoreIn N ⊔ FooteLit.twoLayerIn N) ⊓
        UnbalancedLayer.coreActionKernel (FooteLit.solomonKStarOf N) :=
      mem_inf.mpr ⟨mem_sup_left (FooteLit.mem_oddTwoCoreIn_of_central htN hcent ht),
        FooteLit.mem_coreActionKernel_of_le_centralizer fun x hx =>
          mem_centralizer_singleton_iff.mpr (hcent x (solomonKStarOf_le N hx))⟩
    exact FooteLit.one_le_pRank_of_orderOf_eq_two (g := ⟨t, htY⟩)
      (by rw [Subgroup.orderOf_mk]; exact ht)

theorem isKBalanced_or_psp4_of_centralizer
    (hS : Sol76T13.R12.QuasisimpleRankTwoSymplecticInput) [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog G) {t : G}
    (ht : orderOf t = 2) {M M' : Subgroup G}
    (hM : M ∈ kStarComponents (centralizer ({t} : Set G)))
    (hM' : M' ∈ kStarComponents (centralizer ({t} : Set G))) (hMM' : M ≠ M') :
    FooteLit.IsKBalanced (centralizer ({t} : Set G)) ∨
      ∃ (k : Type) (_ : Field k) (_ : Finite k), Odd (Nat.card k) ∧
        Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* StatedProj (StatedSp 2 k)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := centralizer ({t} : Set G) with hN
  set X := (FooteLit.oddTwoCoreIn N ⊔ FooteLit.twoLayerIn N) ⊓
    UnbalancedLayer.coreActionKernel M' with hX
  have htN : t ∈ N := mem_centralizer_singleton_iff.mpr rfl
  have hcent : ∀ n ∈ N, n * t = t * n := fun n hn => mem_centralizer_singleton_iff.mp hn
  by_cases h3 : 3 ≤ CFSG.pRank 2 ↥X
  · exact Or.inl (isKBalanced_of_central_of_rank htN hcent ht hM hM' hMM' h3)
  right
  rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h3
  have hMX : M ≤ X := le_inf
    ((FooteLit.le_twoLayerIn_of_isTwoComponentIn hM.1).trans le_sup_right)
    (GSThmB.B5a.le_coreActionKernel_of_ne hM'.1.1 hM.1.1 hM'.1.2 hM.1.2 (Ne.symm hMM'))
  have hwide : 2 ≤ CFSG.pRank 2 ↥M := hM.2.2.2 M ⟨hM.2.2.1, Relation.ReflTransGen.refl⟩
  rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at hwide
  have hrM : CFSG.Open.pRank 2 M = 2 := by
    have h1 := SectionRank.pRank_mono (by norm_num : 1 < 2) hMX
    omega
  have htM : t ∈ M := by
    by_contra htM
    obtain ⟨E, hEM, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two M
    rw [hrM] at hEcard
    have htX : t ∈ X := mem_inf.mpr ⟨mem_sup_left (FooteLit.mem_oddTwoCoreIn_of_central htN hcent
      ht), FooteLit.mem_coreActionKernel_of_le_centralizer hM'.1.1⟩
    have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    have h4 := FooteLit.succ_le_open_pRank_of_commute Nat.prime_two hE hEcard
      (fun e he => hcent e (hM.1.1 (hEM he))) ht2 (fun h => htM (hEM h)) (hEM.trans hMX) htX
    omega
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    FooteLit.isQuasisimple_quotient_of_isPComponent hM.1.1 hM.1.2
  have hMO : pPrimeCore 2 (↥M ⧸ pPrimeCore 2 ↥M) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥M) 2
  have hMcat := Sol76T13.catalog_coreQuotient_of_mem_solomonKStar
    (Sol76T13.kStarKProper_of_simple hnab hKP) hM.1 hM.2
  have hMr : CFSG.pRank 2 (↥M ⧸ pPrimeCore 2 ↥M) = 2 := by
    rw [FooteLit.pRank_quotient_pPrimeCore, SectionRank.pRank_eq_open_pRank_top,
      ← SectionRank.pRank_eq_pRank_top_subgroup]
    exact hrM
  have ht' : orderOf (⟨t, htM⟩ : ↥M) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have ht2' : (⟨t, htM⟩ : ↥M) ^ 2 = 1 := by rw [← ht']; exact pow_orderOf_eq_one _
  set z : ↥M ⧸ pPrimeCore 2 ↥M := QuotientGroup.mk ⟨t, htM⟩ with hz
  have hzc : z ∈ center (↥M ⧸ pPrimeCore 2 ↥M) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hz, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hcent m (hM.1.1 m.2))
  have hz2 : orderOf z = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hz, ← QuotientGroup.mk_pow, ht2', QuotientGroup.mk_one]
    · intro h
      exact FooteLit.not_mem_pPrimeCore_two_of_orderOf ht'
        ((QuotientGroup.eq_one_iff (⟨t, htM⟩ : ↥M)).mp h)
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := hS _ hMq hMO hMcat hMr ⟨z, hzc, hz2⟩
  obtain ⟨e₀⟩ := FooteLit.nonempty_fusionZStar_quotient_equiv ↥M
  have : Fintype k := Fintype.ofFinite k
  refine ⟨k, inferInstance, inferInstance, ?_, ⟨e₀.trans e⟩⟩
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  exact FiniteField.odd_card_of_char_ne_two hk

end CFSG.ComponentClassification.Foote5.SolMax
