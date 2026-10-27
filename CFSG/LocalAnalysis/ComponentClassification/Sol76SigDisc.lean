module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigSpC
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourQuotientOddKernel

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatFactsSp4

@[expose] def InvolutionsFourCover (Q : Type) [Group Q] : Prop :=
  ∀ E : Subgroup Q, IsKleinFour E → ∀ x : Q, orderOf x = 2 → ∃ g : Q, g⁻¹ * x * g ∈ E

@[expose] def C1Rank2 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → pPrimeCore 2 Q = ⊥ →
    Blueprint.Catalog (Q ⧸ center Q) → CFSG.pRank 2 Q = 2 → InvolutionsFourCover Q

@[expose] def C1Rank2Simple : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → pPrimeCore 2 Q = ⊥ →
    Blueprint.Catalog (Q ⧸ center Q) → CFSG.pRank 2 Q = 2 → center Q = ⊥ →
      InvolutionsFourCover Q

theorem involutionsFourCover_of_center_ne_bot (hS : R12.QuasisimpleRankTwoSymplecticInput)
    (hGA : TBLit.GriessMultipliersAllModels) {Q : Type} [Group Q] [Finite Q]
    (hQq : IsQuasisimple Q) (hQO : pPrimeCore 2 Q = ⊥)
    (hQcat : Blueprint.Catalog (Q ⧸ center Q)) (hQr : CFSG.pRank 2 Q = 2)
    (hZ : center Q ≠ ⊥) : InvolutionsFourCover Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hz2⟩ : ∃ z ∈ center Q, orderOf z = 2 := by
    have hZ2 : IsPGroup 2 (center Q) := R12.isPGroup_center_of_pPrimeCore_eq_bot hQO
    have hnt : Nontrivial (center Q) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZ
    obtain ⟨n, hn, hcard⟩ := hZ2.nontrivial_iff_card.mp hnt
    have hdvd : 2 ∣ Nat.card (center Q) := by
      rw [hcard]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    exact ⟨c, c.2, by rw [Subgroup.orderOf_coe, hc]⟩
  obtain ⟨F, _, _, hF, ⟨ι⟩⟩ :=
    exists_mulEquiv_statedSp_of_symplectic hS hGA hQq hQO hQcat hQr hz hz2
  intro E hE x hx2
  have hE' : IsKleinFour (E.map ι.toMonoidHom) := by
    refine FooteLit.isKleinFour_of_card_eq_four ?_ ?_
    · rw [card_map_of_injective ι.injective, hE.card_four]
    · rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, Sig.sq_eq_one_of_isKleinFour hE hy, map_one]
  have hx' : ι x * ι x = 1 := by
    rw [← map_mul, ← sq, Sig.sq_eq_one_of_orderOf_eq_two hx2, map_one]
  have hx1 : ι x ≠ 1 := fun h => by
    have h1 : x = 1 := ι.injective (h.trans (map_one ι).symm)
    rw [h1, orderOf_one] at hx2
    norm_num at hx2
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isKleinFour hF hE' hx' hx1
  obtain ⟨y, hyE, hy⟩ := Subgroup.mem_map.mp hg
  refine ⟨ι.symm g, ?_⟩
  have e : (ι.symm g)⁻¹ * x * ι.symm g = y := ι.injective (by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hy.symm)
  rw [e]
  exact hyE

theorem c1Rank2_of_simple (hS : R12.QuasisimpleRankTwoSymplecticInput)
    (hGA : TBLit.GriessMultipliersAllModels) (h : C1Rank2Simple) : C1Rank2 := by
  intro Q _ _ hQq hQO hQcat hQr
  by_cases hZ : center Q = ⊥
  · exact h Q hQq hQO hQcat hQr hZ
  · exact involutionsFourCover_of_center_ne_bot hS hGA hQq hQO hQcat hQr hZ

variable {G : Type} [Group G] [Finite G] {N K : Subgroup G}

theorem involutionsFourCover_coreQuot (hC : C1Rank2) (hKK : KStarKProper G)
    (hK : K ∈ kStarComponents N) (h2K : CFSG.Open.pRank 2 K ≤ 2) :
    InvolutionsFourCover (coreQuot K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hC _ (isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2)
    (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) 2)
    (catalog_coreQuotient_of_mem_solomonKStar hKK hK.1 hK.2) ?_
  rw [FooteLit.pRank_quotient_pPrimeCore, pRank_coe_eq]
  have := two_le_pRank_of_mem_solomonKStar hK.2
  omega

theorem exists_conj_mem_of_cover (hC : InvolutionsFourCover (coreQuot K)) {E : Subgroup G}
    (hE : IsKleinFour E) (hEK : E ≤ K) {x : G} (hxK : x ∈ K) (hx2 : orderOf x = 2) :
    ∃ g ∈ K, g⁻¹ * x * g ∈ E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥K))
  have hV : IsKleinFour (E.subgroupOf K) := by
    refine FooteLit.isKleinFour_of_card_eq_four ?_ fun y hy => Subtype.ext ?_
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hE.card_four]
    · rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact Sig.sq_eq_one_of_isKleinFour hE hy
  have hVbar : IsKleinFour ((E.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K))) :=
    GorensteinWalter.isKleinFour_map_quotient_of_odd_kernel _ _ hodd hV
  have hx2' : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥K) (⟨x, hxK⟩ : ↥K)) = 2 :=
    Sig.orderOf_mk_eq_two (by rw [Subgroup.orderOf_mk]; exact hx2)
  obtain ⟨gbar, hg⟩ := hC _ hVbar _ hx2'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ gbar
  obtain ⟨v, hvV, hv⟩ := Subgroup.mem_map.mp hg
  have hvE : (v : G) ∈ E := hvV
  set y : G := (g : G)⁻¹ * x * g with hy
  have hyK : y ∈ K := mul_mem (mul_mem (inv_mem g.2) hxK) g.2
  have hvy : QuotientGroup.mk' (pPrimeCore 2 ↥K) v =
      QuotientGroup.mk' (pPrimeCore 2 ↥K) (⟨y, hyK⟩ : ↥K) := by
    rw [hv]
    have e : (⟨y, hyK⟩ : ↥K) = g⁻¹ * ⟨x, hxK⟩ * g := rfl
    rw [e, map_mul, map_mul, map_inv]
  have hvy' : (v : G)⁻¹ * y ∈ oddCoreIn K := (mk_eq_mk_iff (N := K)).mp hvy
  have hy2 : orderOf y = 2 := by
    have h := orderOf_injective (MulAut.conj (g : G)⁻¹).toMonoidHom
      (MulAut.conj (g : G)⁻¹).injective x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
    rw [hy, h, hx2]
  have hOK : Odd (Nat.card (oddCoreIn K)) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn K)
  have hvO : zpowers (v : G) ≤ normalizer (oddCoreIn K : Set G) :=
    zpowers_le.mpr (le_normalizer_oddCoreIn K v.2)
  have hyM : zpowers y ≤ zpowers (v : G) ⊔ oddCoreIn K := zpowers_le.mpr (by
    have e : y = v * ((v : G)⁻¹ * y) := by group
    rw [e]
    exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right hvy'))
  have hy2' : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
  obtain ⟨m, hmM, hm⟩ := exists_conj_le_of_sup_odd le_sup_left hvO hOK rfl hyM hy2'
  have hmK : m ∈ K := sup_le (zpowers_le.mpr v.2) (map_subtype_le _) hmM
  have hmy : m * y * m⁻¹ ∈ E := by
    have h := hm ⟨y, mem_zpowers y, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    exact (zpowers_le.mpr hvE) h
  refine ⟨(g : G) * m⁻¹, mul_mem g.2 (inv_mem hmK), ?_⟩
  have e : ((g : G) * m⁻¹)⁻¹ * x * ((g : G) * m⁻¹) = m * y * m⁻¹ := by
    rw [hy]
    group
  rw [e]
  exact hmy

theorem not_disc_of_cover {K' V B H : Subgroup G} (hP : SigPair N K K' V B)
    (hC : InvolutionsFourCover (coreQuot K)) (hKH : K ≤ H) {x : G} (hxK : x ∈ K)
    (hx2 : orderOf x = 2)
    (hdisc : ∀ g ∈ H, ∀ U E F : Subgroup G, IsKleinFour U →
      U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E → E ≤ B → E ≤ K → IsKleinFour F →
      F ≤ K ⊓ centralizer (U : Set G) → g⁻¹ * x * g ∈ F →
      ¬ Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) : False := by
  obtain ⟨-, hK', -, -, -, hBQ, -, hB, -, -, E, hE, hEB, hEK⟩ := hP
  obtain ⟨g, hgK, hgE⟩ := exists_conj_mem_of_cover hC hE hEK hxK hx2
  have hB2 : IsPGroup 2 B := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 B hB
  obtain ⟨U, hU, hUY⟩ := exists_isKleinFour_inf_centralizer hK' hB2 hBQ
  have hEU : E ≤ K ⊓ centralizer (U : Set G) := le_inf hEK fun e he =>
    mem_centralizer_iff.mpr fun u hu => ((mem_centralizer_iff.mp (hUY hu).2) e (hEB he)).symm
  exact hdisc g (hKH hgK) U E E hU hUY hE hEB hEK hE hEU hgE Relation.ReflTransGen.refl

@[expose] def GoodInvolutionsLeftDiscThreeFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      3 ≤ CFSG.Open.pRank 2 K → ¬ InvolutionsFourCover (coreQuot K) →
      (∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G)) →
      ∀ x ∈ K, orderOf x = 2 →
        (∀ g ∈ normalizer (wGroup B V : Set G), ∀ U E F : Subgroup G, IsKleinFour U →
          U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E → E ≤ B → E ≤ K → IsKleinFour F →
          F ≤ K ⊓ centralizer (U : Set G) → g⁻¹ * x * g ∈ F →
          ¬ Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        ∃ g ∈ normalizer (wGroup B V : Set G), IsGoodFor N (wGroup B V) (g⁻¹ * x * g)

@[expose] def GoodInvolutionsLeftDiscThreeAt (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → R G N K K' → wGroup B V ≠ ⊥ →
      3 ≤ CFSG.Open.pRank 2 K → ¬ InvolutionsFourCover (coreQuot K) →
      (∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G)) →
      ∀ x ∈ K, orderOf x = 2 →
        (∀ g ∈ normalizer (wGroup B V : Set G), ∀ U E F : Subgroup G, IsKleinFour U →
          U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E → E ≤ B → E ≤ K → IsKleinFour F →
          F ≤ K ⊓ centralizer (U : Set G) → g⁻¹ * x * g ∈ F →
          ¬ Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        ∃ g ∈ normalizer (wGroup B V : Set G), IsGoodFor N (wGroup B V) (g⁻¹ * x * g)

theorem goodInvolutionsLeftDiscFor_of_rank2 (hC : C1Rank2)
    (h3 : GoodInvolutionsLeftDiscThreeFor) : GoodInvolutionsLeftDiscFor := by
  intro G _ _ hG N hN h2 K K' V B hP hW hKH x hx hx2 hdisc
  by_cases hcov : InvolutionsFourCover (coreQuot K)
  · exact (not_disc_of_cover hP hcov (hKH K hP.1) hx hx2 hdisc).elim
  by_cases hr : 3 ≤ CFSG.Open.pRank 2 K
  · exact h3 G hG N hN h2 K K' V B hP hW hr hcov hKH x hx hx2 hdisc
  · exact (hcov (involutionsFourCover_coreQuot hC (kStarKProper_of_simpleAmbient hG) hP.1
      (by omega))).elim

theorem goodInvolutionsLeftDiscAt_of_rank2 (hC : C1Rank2) {R : SigOrientation}
    (h3 : GoodInvolutionsLeftDiscThreeAt R) : GoodInvolutionsLeftDiscAt R := by
  intro G _ _ hG N hN h2 K K' V B hP hR hW hKH x hx hx2 hdisc
  by_cases hcov : InvolutionsFourCover (coreQuot K)
  · exact (not_disc_of_cover hP hcov (hKH K hP.1) hx hx2 hdisc).elim
  by_cases hr : 3 ≤ CFSG.Open.pRank 2 K
  · exact h3 G hG N hN h2 K K' V B hP hR hW hr hcov hKH x hx hx2 hdisc
  · exact (hcov (involutionsFourCover_coreQuot hC (kStarKProper_of_simpleAmbient hG) hP.1
      (by omega))).elim

end CFSG.ComponentClassification.Sol76.Sig
