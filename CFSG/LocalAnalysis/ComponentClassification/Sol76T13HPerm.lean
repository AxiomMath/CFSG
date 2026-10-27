module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L313Narrow

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

@[expose] def Lemma313NarrowNPrimeInputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    solomonKStarOf (normalizer (solomonKStarOf N : Set G)) = solomonKStarOf N →
    (∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N : Set G)) →
    ∀ K ∈ kStarComponents N, ∀ g : G,
      K ≤ conjugate (normalizer (solomonKStarOf N : Set G)) g →
      (∀ K' ∈ kStarComponents N, ∀ s ∈ K', orderOf s = 2 → ∀ L ∈ kStarComponents N,
        ¬ conjugate L g ≤ centralizer ({s} : Set G)) →
      (∀ L ∈ kStarComponents N, ∀ s ∈ conjugate L g, orderOf s = 2 →
        ∀ K' ∈ kStarComponents N, ¬ K' ≤ centralizer ({s} : Set G)) →
      (∀ L ∈ kStarComponents N, K ≤ normalizer (conjugate L g : Set G) ∧
          ¬ K ≤ coreActionKernel (conjugate L g) ∧
          (K ≤ conjugate L g ⊔ coreActionKernel (conjugate L g) →
            ¬ conjugate L g ≤ K ⊔ coreActionKernel (conjugate L g))) →
      g ∈ normalizer (solomonKStarOf N : Set G)

end CFSG.ComponentClassification.Sol76

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] {𝒜 : Thm13Ambient}

theorem map_conj_mul_eq (H : Subgroup G) (g h : G) :
    H.map (MulAut.conj (g * h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_subtype_map_conj_eq {M : Subgroup G} (A : Subgroup ↥M) (c : ↥M) :
    (A.map (MulAut.conj c).toMonoidHom).map M.subtype =
      (A.map M.subtype).map (MulAut.conj (c : G)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1

theorem exists_involution_not_mem_normalizer [Finite G] {K : Subgroup G}
    {𝒮 : Set (Subgroup G)}
    (hperm : ∀ k ∈ K, ∀ J ∈ 𝒮, J.map (MulAut.conj k).toMonoidHom ∈ 𝒮)
    (hKres : oddResidualIn K = K) (hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (hnc : ∃ q : ↥K ⧸ pPrimeCore 2 ↥K, orderOf q = 2 ∧ q ∉ center (↥K ⧸ pPrimeCore 2 ↥K))
    (hP : ∃ J ∈ 𝒮, ¬ K ≤ normalizer (J : Set G)) :
    ∃ u ∈ K, orderOf u = 2 ∧ ∃ J ∈ 𝒮, u ∉ normalizer (J : Set G) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨J₀, hJ₀, hKJ₀⟩ := hP
  set H₀ : Subgroup G := ⨅ J ∈ 𝒮, normalizer (J : Set G) with hH₀
  have hmem : ∀ x, x ∈ H₀ ↔ ∀ J ∈ 𝒮, x ∈ normalizer (J : Set G) := fun x => by
    simp only [hH₀, mem_iInf]
  have hconj : ∀ k ∈ K, ∀ x ∈ H₀, k * x * k⁻¹ ∈ H₀ := by
    intro k hk x hx
    rw [hmem] at hx ⊢
    intro J hJ
    have hx' := hx _ (hperm k⁻¹ (inv_mem hk) J hJ)
    rw [mem_normalizer_iff_map_conj_eq] at hx' ⊢
    change (J.map (MulAut.conj k⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      J.map (MulAut.conj k⁻¹).toMonoidHom at hx'
    change J.map (MulAut.conj (k * x * k⁻¹)).toMonoidHom = J
    rw [mul_assoc, map_conj_mul_eq, map_conj_mul_eq, hx', ← map_conj_mul_eq, mul_inv_cancel]
    ext y
    simp
  have hKH : K ≤ normalizer (H₀ : Set G) := fun k hk => mem_normalizer_iff.mpr fun x =>
    ⟨fun hx => hconj k hk x hx, fun hx => by
      have h := hconj k⁻¹ (inv_mem hk) _ hx
      rwa [show k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x by group] at h⟩
  have hKH₀ : K ≤ H₀ := le_of_forall_involution le_rfl (sup_eq_left.mpr (map_subtype_le _))
    hKres hKq hnc hKH fun x hx hx2 => (hmem x).mpr (hcon x hx hx2)
  exact hKJ₀ fun k hk => (hmem k).mp (hKH₀ hk) J₀ hJ₀

theorem exists_central_involution_of_ne_bot [Finite G] {S : Subgroup G} (hS1 : S ≠ ⊥)
    (hS2 : IsPGroup 2 S) : ∃ z ∈ S, orderOf z = 2 ∧ ∀ s ∈ S, s * z = z * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥S := (nontrivial_iff_ne_bot S).mpr hS1
  have hZ := hS2.center_nontrivial
  have := Fintype.ofFinite ↥(center ↥S)
  have h2 : 2 ∣ Fintype.card ↥(center ↥S) := by
    have hZ2 : IsPGroup 2 ↥(center ↥S) := hS2.to_subgroup _
    obtain ⟨k, hk⟩ := hZ2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      have := Finite.one_lt_card_iff_nontrivial.mpr hZ
      omega
    rw [← Nat.card_eq_fintype_card, hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card 2 h2
  refine ⟨((z₀ : ↥S) : G), (z₀ : ↥S).2, ?_, fun s hs => ?_⟩
  · rw [orderOf_coe, orderOf_coe, hz₀]
  · exact congrArg Subtype.val ((mem_center_iff.mp z₀.2) ⟨s, hs⟩)

theorem exists_commuting_involution_ne [Finite G] {K : Subgroup G}
    (hK : 2 ≤ CFSG.Open.pRank 2 K) {u : G} (huK : u ∈ K) (hu : orderOf u = 2) :
    ∃ v ∈ K, orderOf v = 2 ∧ v ≠ u ∧ u * v = v * u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set u' : ↥K := ⟨u, huK⟩ with hu'def
  have hu' : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hu'1 : u' ≠ 1 := fun h => by rw [h, orderOf_one] at hu'; omega
  have hu'2 : IsPGroup 2 (zpowers u') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu', pow_one])
  obtain ⟨S, hS⟩ := hu'2.exists_le_sylow
  have huS : u' ∈ (S : Subgroup ↥K) := hS (mem_zpowers u')
  have hS1 : (S : Subgroup ↥K) ≠ ⊥ := fun h => hu'1 (by rw [h] at huS; exact mem_bot.mp huS)
  obtain ⟨z, hzS, hz2, hzc⟩ := exists_central_involution_of_ne_bot hS1 S.isPGroup'
  by_cases hzu : z = u'
  · have hrank : 2 ≤ CFSG.Open.pRank 2 (S : Subgroup ↥K) := by
      rw [(SectionRank.pRank_sylow S).1, ← SectionRank.pRank_eq_pRank_top_subgroup]
      exact hK
    obtain ⟨E, hES, hE, hcard⟩ :=
      SectionRank.exists_pRank (p := 2) (by norm_num) (S : Subgroup ↥K)
    have hE4 : 4 ≤ Nat.card E := by
      rw [hcard]
      exact le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hrank)
    obtain ⟨e, heE, he⟩ : ∃ e ∈ E, e ∉ ({1, u'} : Finset ↥K) := by
      by_contra h
      push Not at h
      have h1 : Nat.card E ≤ ({1, u'} : Finset ↥K).card := by
        rw [← Nat.card_eq_finsetCard]
        exact Nat.card_le_card_of_injective (fun x : E => (⟨x, h x x.2⟩ : ({1, u'} : Finset ↥K)))
          fun x y hxy => Subtype.ext (congrArg (fun w : ({1, u'} : Finset ↥K) => (w : ↥K)) hxy)
      have h2 : ({1, u'} : Finset ↥K).card ≤ 2 := Finset.card_le_two
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    have heo : orderOf e = 2 := orderOf_eq_prime (hE.2 e heE) he.1
    refine ⟨(e : G), e.2, by rw [Subgroup.orderOf_coe]; exact heo, fun h => he.2 (Subtype.ext h),
      ?_⟩
    have h1 := hzc e (hES heE)
    rw [hzu] at h1
    exact (congrArg Subtype.val h1).symm
  · exact ⟨(z : G), z.2, by rw [Subgroup.orderOf_coe]; exact hz2, fun h => hzu (Subtype.ext h),
      congrArg Subtype.val (hzc u' huS)⟩

variable [Finite G]

theorem le_of_moved_twoComponent {M₁ M₂ K L : Subgroup G} (hKM : K ≤ M₂)
    (hKs : K ∈ solomonKStar G)
    (hCb : ∀ s ∈ K, orderOf s = 2 → centralizer ({s} : Set G) ≤ M₁)
    (hL : IsTwoComponentIn L M₂) {u v : G} (huK : u ∈ K) (hvK : v ∈ K) (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : u ≠ v) (hc : u * v = v * u)
    (hmove : u ∉ normalizer (L : Set G)) : L ≤ M₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNodd : Odd (Nat.card (pPrimeCore 2 ↥M₂)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  set u' : ↥M₂ := ⟨u, hKM huK⟩ with hu'def
  set v' : ↥M₂ := ⟨v, hKM hvK⟩ with hv'def
  have hu2 : u' ^ 2 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hu]
    exact pow_orderOf_eq_one u)
  have hv2 : v' ^ 2 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hv]
    exact pow_orderOf_eq_one v)
  have hc' : u' * v' = v' * u' := Subtype.ext hc
  set U : Subgroup ↥M₂ := zpowers u' ⊔ zpowers v' with hU
  have hUsq : ∀ w ∈ U, w ^ 2 = 1 :=
    FooteLit.sq_eq_one_of_mem_sup (fun x hx => FooteLit.sq_eq_one_of_mem_zpowers hu2 hx)
      (fun x hx => FooteLit.sq_eq_one_of_mem_zpowers hv2 hx) fun x hx y hy => by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
        exact (Commute.zpow_zpow hc' i j).eq
  have hU2 : IsPGroup 2 U := fun w => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hUsq w w.2)⟩
  have hUK : U ≤ K.subgroupOf M₂ :=
    sup_le (zpowers_le.mpr (show u' ∈ K.subgroupOf M₂ from huK))
      (zpowers_le.mpr (show v' ∈ K.subgroupOf M₂ from hvK))
  have hL₀c : IsPComponent 2 (L.subgroupOf M₂) := hL.2
  have hLbar : CFSG.Open.IsComponentOf
      ((L.subgroupOf M₂).map (QuotientGroup.mk' (pPrimeCore 2 ↥M₂))) ⊤ :=
    ((CatalogueBAlternating.pComponent_iff_minimal_image 2 (L.subgroupOf M₂)).mp hL₀c).2.1
  have hinj : ∀ {x y : ↥M₂}, x ∈ U → y ∈ U →
      QuotientGroup.mk' (pPrimeCore 2 ↥M₂) x = QuotientGroup.mk' (pPrimeCore 2 ↥M₂) y →
        x = y := fun hx hy h =>
    AschbacherToolkit.quotient_injective_on_of_isPGroup _ hNodd hU2 hx hy h
  have huU : u' ∈ U := mem_sup_left (mem_zpowers u')
  have hvU : v' ∈ U := mem_sup_right (mem_zpowers v')
  have hu1 : u' ≠ 1 := fun h => by
    have h1 : u = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hu
    omega
  have hv1 : v' ≠ 1 := fun h => by
    have h1 : v = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hv
    omega
  have hub1 : QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u' ≠ 1 := fun h =>
    hu1 (hinj huU U.one_mem (h.trans (map_one _).symm))
  have hvb1 : QuotientGroup.mk' (pPrimeCore 2 ↥M₂) v' ≠ 1 := fun h =>
    hv1 (hinj hvU U.one_mem (h.trans (map_one _).symm))
  have hubvb : QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u' ≠ QuotientGroup.mk' (pPrimeCore 2 ↥M₂) v' :=
    fun h => huv (congrArg Subtype.val (hinj huU hvU h))
  have hubub : QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u' * QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u' =
      1 := by rw [← map_mul, ← sq, hu2, map_one]
  have hvbvb : QuotientGroup.mk' (pPrimeCore 2 ↥M₂) v' * QuotientGroup.mk' (pPrimeCore 2 ↥M₂) v' =
      1 := by rw [← map_mul, ← sq, hv2, map_one]
  have hcomm : Commute (QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u')
      (QuotientGroup.mk' (pPrimeCore 2 ↥M₂) v') := by
    change QuotientGroup.mk' _ u' * QuotientGroup.mk' _ v' =
      QuotientGroup.mk' _ v' * QuotientGroup.mk' _ u'
    rw [← map_mul, ← map_mul, hc']
  have hmoved : AschbacherComponentAction.rightComponent
      ((L.subgroupOf M₂).map (QuotientGroup.mk' (pPrimeCore 2 ↥M₂)))
      (QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u') ≠
        (L.subgroupOf M₂).map (QuotientGroup.mk' (pPrimeCore 2 ↥M₂)) := by
    intro h
    have h2 : u' ∈ normalizer ((L.subgroupOf M₂ : Subgroup ↥M₂) : Set ↥M₂) :=
      UnbalancedLayer.mem_normalizer_of_map hL₀c
        ((AschbacherComponentAction.rightComponent_eq_iff_normalizer _ _).mp h)
    apply hmove
    rw [mem_normalizer_iff_map_conj_eq] at h2 ⊢
    change (L.subgroupOf M₂).map (MulAut.conj u').toMonoidHom = L.subgroupOf M₂ at h2
    change L.map (MulAut.conj u).toMonoidHom = L
    have h3 := map_subtype_map_conj_eq (L.subgroupOf M₂) u'
    rw [h2, map_subgroupOf_eq_of_le hL.1] at h3
    exact h3.symm
  have hle := AschbacherToolkit.moved_component_le_centralizerJoin
    (U.map (QuotientGroup.mk' (pPrimeCore 2 ↥M₂)))
    ((L.subgroupOf M₂).map (QuotientGroup.mk' (pPrimeCore 2 ↥M₂)))
    (QuotientGroup.mk' (pPrimeCore 2 ↥M₂) u') (QuotientGroup.mk' (pPrimeCore 2 ↥M₂) v') hLbar
    (mem_map_of_mem _ huU) (mem_map_of_mem _ hvU) hubub hvbvb hub1 hvb1 hubvb hcomm hmoved
  rw [AschbacherToolkit.centralizerJoin_quotient_of_isPGroup _ hNodd hU2] at hle
  have hL₀le : L.subgroupOf M₂ ≤ AschbacherToolkit.centralizerJoin U ⊔ pPrimeCore 2 ↥M₂ := by
    have h1 := map_le_iff_le_comap.mp hle
    rwa [comap_map_eq, QuotientGroup.ker_mk'] at h1
  have hCJ : AschbacherToolkit.centralizerJoin U ≤ M₁.subgroupOf M₂ := by
    apply iSup₂_le
    intro w hw y hy
    have hw2 : ((w : ↥M₂) : G) ^ 2 = 1 := by
      rw [← SubgroupClass.coe_pow, hUsq w w.2, OneMemClass.coe_one]
    have hwo : orderOf ((w : ↥M₂) : G) = 2 := orderOf_eq_prime hw2 fun h => hw (Subtype.ext h)
    exact hCb ((w : ↥M₂) : G) (hUK w.2) hwo (mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)))
  have hO : oddCoreIn M₂ ≤ M₁ := le_of_coprime_of_centralizer hKs hCb
    (coprime_card_oddCoreIn M₂) (hKM.trans (le_normalizer_map_subtype' (pPrimeCore 2 ↥M₂)))
  calc L = (L.subgroupOf M₂).map M₂.subtype := (map_subgroupOf_eq_of_le hL.1).symm
    _ ≤ (AschbacherToolkit.centralizerJoin U ⊔ pPrimeCore 2 ↥M₂).map M₂.subtype := map_mono hL₀le
    _ = (AschbacherToolkit.centralizerJoin U).map M₂.subtype ⊔ oddCoreIn M₂ := map_sup _ _ _
    _ ≤ M₁ := sup_le (map_le_iff_le_comap.mpr hCJ) hO

theorem false_of_moved_twoComponent {M₁ M₂ K L : Subgroup G} (hK : IsTwoComponentIn K M₁)
    (hKM₂ : K ≤ M₂) (hL : IsTwoComponentIn L M₂) (hLM₁ : L ≤ M₁) {u : G} (huK : u ∈ K)
    (hmove : u ∉ normalizer (L : Set G)) : False := by
  have hKC : IsTwoComponentIn K (M₁ ⊓ M₂) := ⟨le_inf hK.1 hKM₂,
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hK.1 hKM₂) inf_le_left hK.2⟩
  have hLC : IsTwoComponentIn L (M₁ ⊓ M₂) := ⟨le_inf hLM₁ hL.1,
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hLM₁ hL.1) inf_le_right hL.2⟩
  have hne : L ≠ K := by
    rintro rfl
    exact hmove (le_normalizer huK)
  exact hmove (GSThmB.B5a.le_coreActionKernel_of_ne hLC.1 hKC.1 hLC.2 hKC.2 hne huK).1

theorem le_normalizer_of_permutes (hq : QuasisimpleTwoPartInput) (hG : KStarKProper G)
    {M₁ M₂ K : Subgroup G} (hK : IsTwoComponentIn K M₁) (hKs : K ∈ solomonKStar G)
    (hKM₂ : K ≤ M₂) (hCb : ∀ s ∈ K, orderOf s = 2 → centralizer ({s} : Set G) ≤ M₁)
    {𝒮 : Set (Subgroup G)} (h𝒮 : ∀ J ∈ 𝒮, IsTwoComponentIn J M₂)
    (hperm : ∀ k ∈ K, ∀ J ∈ 𝒮, J.map (MulAut.conj k).toMonoidHom ∈ 𝒮) :
    ∀ J ∈ 𝒮, K ≤ normalizer (J : Set G) := by
  by_contra hP
  push Not at hP
  have hKq := isQuasisimple_quotient_of_isPComponent hK.1 hK.2
  have hnc := exists_noncentral_involution_coreQuot hq hG hK hKs
  have hKres := oddResidualIn_eq_self_of_isPComponent hK.1 hK.2
  obtain ⟨u, huK, hu, J, hJ, hmove⟩ :=
    exists_involution_not_mem_normalizer hperm hKres hKq hnc hP
  obtain ⟨v, hvK, hv, hvu, huv⟩ :=
    exists_commuting_involution_ne (two_le_pRank_of_mem_solomonKStar hKs) huK hu
  exact false_of_moved_twoComponent hK hKM₂ (h𝒮 J hJ)
    (le_of_moved_twoComponent hKM₂ hKs hCb (h𝒮 J hJ) huK hvK hu hv (Ne.symm hvu) huv hmove)
    huK hmove

theorem map_conj_mem_kStarComponents {M J : Subgroup G} (hJ : J ∈ kStarComponents M) {k : G}
    (hk : k ∈ M) : J.map (MulAut.conj k).toMonoidHom ∈ kStarComponents M :=
  ⟨Sol76.isTwoComponentIn_map_conj hJ.1 (le_normalizer hk),
    Sol76.map_mem_solomonKStar (MulAut.conj k) hJ.2⟩

end CFSG.ComponentClassification.Sol76T13
