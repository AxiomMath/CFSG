module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13HNPrime

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem le_of_coprime_of_pRank {X M O : Subgroup G} (hX : 2 ≤ CFSG.Open.pRank 2 X)
    (hCb : ∀ s ∈ X, orderOf s = 2 → centralizer ({s} : Set G) ≤ M)
    (hO : Nat.Coprime 2 (Nat.card O)) (hXO : X ≤ normalizer (O : Set G)) : O ≤ M := by
  obtain ⟨E, hEX, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) X
  have hlarge : 2 ^ (1 + 1) ≤ Nat.card E := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) hX
  have hgen := SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two E O hE hlarge (hEX.trans hXO) hO
  rw [← hgen]
  refine iSup₂_le fun S hS => ?_
  obtain ⟨hSE, hScard⟩ := hS
  have : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hScard]; norm_num)
  obtain ⟨⟨v, hvS⟩, hv1⟩ := exists_ne (1 : S)
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hv2 : orderOf v = 2 := orderOf_eq_prime (hE.2 v (hSE hvS)) hv1'
  exact inf_le_right.trans ((centralizer_le (Set.singleton_subset_iff.mpr hvS)).trans
    (hCb v (hEX (hSE hvS)) hv2))

theorem le_sup_coreActionKernel_of_card_fusionZStar {J K : Subgroup G}
    (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) (hKres : oddResidualIn K = K)
    (hJQ : J ≤ normalizer (coreActionKernel J : Set G))
    (hKQ : K ≤ normalizer (coreActionKernel J : Set G))
    (hKJQ : K ≤ J ⊔ coreActionKernel J) (hmove : ¬ K ≤ coreActionKernel J)
    (hcard : Nat.card (↥J ⧸ Open.fusionZStar ↥J) = Nat.card (↥K ⧸ Open.fusionZStar ↥K)) :
    J ≤ K ⊔ coreActionKernel J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := coreActionKernel J with hQ
  have hle : K ⊔ Q ≤ J ⊔ Q := sup_le hKJQ le_sup_right
  have hKZ : Q.subgroupOf K ≤ Open.fusionZStar ↥K := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ :=
      inf_le_fusionZStar_of_not_le hKq hKres hKQ hmove ⟨x.2, mem_subgroupOf.mp hx⟩
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  have hZJ : Open.fusionZStar ↥J ≤ Q.subgroupOf J := by
    intro z hz
    rw [mem_fusionZStar_iff_forall] at hz
    refine mem_subgroupOf.mpr ⟨le_normalizer z.2, fun j hj => ?_⟩
    have h1 := hz ⟨j⁻¹, inv_mem hj⟩
    have h2 : (j⁻¹ * (z : G))⁻¹ * ((z : G) * j⁻¹) ∈ oddCoreIn J := mem_map_of_mem J.subtype h1
    have h3 : j⁻¹ * ((j⁻¹ * (z : G))⁻¹ * ((z : G) * j⁻¹)) * j⁻¹⁻¹ ∈ oddCoreIn J :=
      (mem_normalizer_iff.mp (le_normalizer_oddCoreIn J (inv_mem hj)) _).mp h2
    rw [show j⁻¹ * ((j⁻¹ * (z : G))⁻¹ * ((z : G) * j⁻¹)) * j⁻¹⁻¹ = j⁻¹ * (z : G)⁻¹ * j * z by
      group] at h3
    exact h3
  have hcardsup : ∀ {X : Subgroup G}, X ≤ normalizer (Q : Set G) →
      Nat.card ↥(X ⊔ Q) = Nat.card ↥Q * (Q.subgroupOf X).index := by
    intro X hX
    have := Subgroup.normal_subgroupOf_of_le_normalizer hX
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hX
    have h1 := Subgroup.card_mul_index (Q.subgroupOf (X ⊔ Q))
    have h2 : Nat.card ↥(Q.subgroupOf (X ⊔ Q)) = Nat.card ↥Q :=
      Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
    have h3 : (Q.subgroupOf (X ⊔ Q)).index = (Q.subgroupOf X).index :=
      (Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient X Q hX).toEquiv).symm
    rw [← h1, h2, h3]
  have hidx1 : (Q.subgroupOf J).index ≤ (Open.fusionZStar ↥J).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hZJ)
  have hidx2 : (Open.fusionZStar ↥K).index ≤ (Q.subgroupOf K).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hKZ)
  have hidx3 : (Open.fusionZStar ↥J).index = (Open.fusionZStar ↥K).index := hcard
  have heq : K ⊔ Q = J ⊔ Q := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardsup hKQ, hcardsup hJQ]
    exact Nat.mul_le_mul_left _ (hidx1.trans (hidx3.le.trans hidx2))
  rw [heq]
  exact le_sup_left

theorem mem_coreActionKernel_of_commutator_mem_oddCoreIn {N K : Subgroup G}
    (hK : K ∈ kStarComponents N) {t : G} (htM : t ∈ normalizer (solomonKStarOf N : Set G))
    (htK : ∀ a ∈ K, t⁻¹ * a⁻¹ * t * a ∈ oddCoreIn (solomonKStarOf N)) :
    t ∈ coreActionKernel K := by
  set D := solomonKStarOf N with hD
  have hKD : K ≤ D := le_iSup₂_of_le K hK le_rfl
  have hKDc : IsTwoComponentIn K D := isTwoComponentIn_of_le hK.1 hKD (solomonKStarOf_le N)
  set K' := K.map (MulAut.conj t⁻¹).toMonoidHom with hK'
  have hK'c : IsTwoComponentIn K' D := Sol76.isTwoComponentIn_map_conj hKDc (inv_mem htM)
  have hK'le : K' ≤ oddCoreIn D ⊔ K := by
    rintro _ ⟨a, ha, rfl⟩
    have e : (MulAut.conj t⁻¹).toMonoidHom a = t⁻¹ * a * t * a⁻¹ * a := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [e]
    refine mul_mem (mem_sup_left ?_) (mem_sup_right ha)
    have h := htK a⁻¹ (inv_mem ha)
    rwa [inv_inv] at h
  have hinv : ∃ b ∈ K', orderOf b = 2 := by
    obtain ⟨b, hb, hb2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hK.2
    refine ⟨(MulAut.conj t⁻¹).toMonoidHom b, mem_map_of_mem _ hb, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
    exact hb2
  have hK'K : K' = K := Sol76.eq_of_le_oddCoreIn_sup hK'c hKDc hK'le hinv
  have htN' : t⁻¹ ∈ normalizer (K : Set G) := mem_normalizer_iff_map_conj_eq.mpr hK'K
  have htN : t ∈ normalizer (K : Set G) := by simpa using inv_mem htN'
  refine ⟨htN, fun j hj => ?_⟩
  have h1 : j⁻¹ * t⁻¹ * j * t ∈ oddCoreIn D := by
    have h := inv_mem (htK j hj)
    rwa [show (t⁻¹ * j⁻¹ * t * j)⁻¹ = j⁻¹ * t⁻¹ * j * t by group] at h
  have h2 : j⁻¹ * t⁻¹ * j * t ∈ K := by
    have h3 : t⁻¹ * j * t⁻¹⁻¹ ∈ K := (mem_normalizer_iff.mp htN' j).mp hj
    rw [inv_inv] at h3
    rw [show j⁻¹ * t⁻¹ * j * t = j⁻¹ * (t⁻¹ * j * t) by group]
    exact mul_mem (inv_mem hj) h3
  exact inf_le_oddCoreIn (coprime_card_oddCoreIn D) (hKD.trans (le_normalizer_oddCoreIn D))
    ⟨h1, h2⟩

theorem kStarComponents_normalizer_eq_of_solomonKStarOf_eq {N : Subgroup G}
    (hKH : solomonKStarOf (normalizer (solomonKStarOf N : Set G)) = solomonKStarOf N) :
    kStarComponents (normalizer (solomonKStarOf N : Set G)) = kStarComponents N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := solomonKStarOf N with hD
  set M := normalizer (D : Set G) with hM
  ext J
  refine ⟨fun hJ => ?_, fun hJ => mem_kStarComponents_normalizer hJ⟩
  have hJD : J ≤ D := by
    have h : J ≤ solomonKStarOf M := le_iSup₂_of_le J hJ le_rfl
    rwa [hKH] at h
  have hJDc : IsTwoComponentIn J D := isTwoComponentIn_of_le hJ.1 hJD le_normalizer
  have hDN : D ≤ N := solomonKStarOf_le N
  have hDn : (D.subgroupOf N).IsSubnormal :=
    Normal.isSubnormal ((normal_subgroupOf_iff_le_normalizer hDN).mpr
      (le_normalizer_solomonKStarOf N))
  exact ⟨⟨hJD.trans hDN, GrSLit.isPComponent_subgroupOf_of_isSubnormal hJD hDN hDn hJDc.2⟩, hJ.2⟩

theorem isTwoComponentIn_inf_of_isTwoComponentIn {Y K M C : Subgroup G}
    (hKM : IsTwoComponentIn K M) (hY : IsTwoComponentIn Y (K ⊓ C)) :
    IsTwoComponentIn Y (M ⊓ C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : K ⊓ C ≤ M ⊓ C := inf_le_inf_right C hKM.1
  have hKs : (K.subgroupOf M).IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K M hKM.1).mp hKM.2).1
  have h1 := hKs.comap (Subgroup.inclusion (inf_le_left : M ⊓ C ≤ M))
  have h2 : (K.subgroupOf M).comap (Subgroup.inclusion (inf_le_left : M ⊓ C ≤ M)) =
      (K ⊓ C).subgroupOf (M ⊓ C) := by
    ext x
    simp only [mem_comap, mem_subgroupOf, coe_inclusion, mem_inf]
    exact ⟨fun h => ⟨h, (mem_inf.mp x.2).2⟩, fun h => h.1⟩
  rw [h2] at h1
  exact ⟨hY.1.trans hle, GrSLit.isPComponent_subgroupOf_of_isSubnormal hY.1 hle h1 hY.2⟩

omit [Finite G] in
theorem exists_mem_ne_of_two {𝒮 : Set (Subgroup G)} (h : ∃ K₁ ∈ 𝒮, ∃ K₂ ∈ 𝒮, K₁ ≠ K₂)
    (K : Subgroup G) : ∃ K' ∈ 𝒮, K' ≠ K := by
  obtain ⟨K₁, h₁, K₂, h₂, hne⟩ := h
  by_cases hK : K₁ = K
  · exact ⟨K₂, h₂, fun h' => hne (hK.trans h'.symm)⟩
  · exact ⟨K₁, h₁, hK⟩

theorem exists_two_mem_kStarComponents {N : Subgroup G} (hN : IsSolomonChoice N) :
    ∃ K₁ ∈ kStarComponents N, ∃ K₂ ∈ kStarComponents N, K₁ ≠ K₂ := by
  obtain ⟨K₁, h₁, -⟩ := exists_mem_kStarComponents_ne hN ⊥
  obtain ⟨K₂, h₂, hne⟩ := exists_mem_kStarComponents_ne hN K₁
  exact ⟨K₁, h₁, K₂, h₂, Ne.symm hne⟩

end CFSG.ComponentClassification.Sol76T13
