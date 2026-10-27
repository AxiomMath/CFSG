module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma316
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

@[expose] def QuasisimpleTwoPartInput : Prop :=
  (∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → Blueprint.Catalog (Q ⧸ center Q) →
    ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u ≠ v → u ∈ center Q → v ∈ center Q →
      ∃ x : Q, orderOf x = 2 ∧ x ∉ center Q) ∧
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → Blueprint.Catalog (Q ⧸ center Q) →
    ∀ x : Q, orderOf x = 2 → x ∉ center Q →
      (Nat.card ↥(center Q)).factorization 2 + 2 ≤
        (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2

@[expose] def KStarKProper (G : Type) [Group G] : Prop :=
  Assembly.KProper Blueprint.Catalog G ∧ ∀ K ∈ solomonKStar G, K ≠ ⊤

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient}

theorem ne_top_of_isSolomonMember_of_fStar
    (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) {L : Subgroup G}
    (hL : IsSolomonMember L) : L ≠ ⊤ := by
  rintro rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GeneralizedFitting.subgroup G with hF
  have hO := pPrimeCore_eq_bot_of_fStar hsF hnF
  have hZF : center F = ⊥ := center_eq_bot_of_simple_nonab hnF
  obtain ⟨-, T, hT, -, hTC, -⟩ := hL
  have hOT : pPrimeCore 2 ↥(⊤ : Subgroup G) = ⊥ := by
    have h1 := Walter.map_pPrimeCore_le_of_isSubnormal
      (Subgroup.IsSubnormal.top : (⊤ : Subgroup G).IsSubnormal)
    rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (⊤ : Subgroup G).subtype_injective]
      at h1
    exact h1
  apply hT
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨-, hxK⟩ := hTC hx
  have hxc : x ∈ centralizer (F : Set G) := by
    rw [mem_centralizer_iff]
    intro f _
    have h1 := hxK f (mem_top f)
    rw [hOT, Subgroup.map_bot, mem_bot] at h1
    calc f * x = x * (f * (f⁻¹ * x⁻¹ * f * x)) := by group
      _ = x * f := by rw [h1, mul_one]
  have hxF : x ∈ F :=
    ((GeneralizedFitting.centralizer_le_fitting G).trans le_sup_left) hxc
  have hxZ : (⟨x, hxF⟩ : F) ∈ center F := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.mp hxc) g g.2)
  rw [hZF, mem_bot] at hxZ
  exact mem_bot.mpr (congrArg Subtype.val hxZ)

theorem kStarKProper_of_fStar (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog G) : KStarKProper G :=
  ⟨hKP, fun _ hK => ne_top_of_isSolomonMember_of_fStar hsF hnF hK.1.1⟩

omit [Finite G] in
theorem fStar_simple_of_simple [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a) :
    IsSimpleGroup (GeneralizedFitting.subgroup G) ∧
      ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a := by
  have htop := (SmallLocal.simple_generalized_fitting_self_local G hna).2.2.2.2
  refine ⟨?_, ?_⟩
  · rw [htop]
    exact (Subgroup.topEquiv (G := G)).isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ GeneralizedFitting.subgroup G := by rw [htop]; exact mem_top a
    have hb : b ∈ GeneralizedFitting.subgroup G := by rw [htop]; exact mem_top b
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun e => hab (congrArg Subtype.val e)⟩

theorem kStarKProper_of_simple [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog G) : KStarKProper G :=
  kStarKProper_of_fStar (fStar_simple_of_simple hna).1 (fStar_simple_of_simple hna).2 hKP

omit [Finite G] in
theorem catalog_of_mem_solomonKStar (hG : KStarKProper G) {K : Subgroup G}
    (hK : K ∈ solomonKStar G) (S : Type) [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) (φ : ↥K →* S) (hφ : Function.Surjective φ) :
    Blueprint.Catalog S :=
  QuasithinUnique.catalog_of_kProper_of_surjective hG.1 K (hG.2 K hK) S hnab φ hφ

omit [Finite G] in
theorem catalog_center_of_mem_solomonKStar (hG : KStarKProper G) {K : Subgroup G}
    (hK : K ∈ solomonKStar G) (hKq : IsQuasisimple ↥K) :
    Blueprint.Catalog (↥K ⧸ center ↥K) := by
  have : IsSimpleGroup (↥K ⧸ center ↥K) := hKq.2.1
  exact catalog_of_mem_solomonKStar hG hK _ hKq.2.2 (QuotientGroup.mk' (center ↥K))
    (QuotientGroup.mk'_surjective _)

theorem catalog_coreQuotient_of_mem_solomonKStar (hG : KStarKProper G) {H K : Subgroup G}
    (hKH : IsTwoComponentIn K H) (hK : K ∈ solomonKStar G) :
    Blueprint.Catalog ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := by
  have hQq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    isQuasisimple_quotient_of_isPComponent hKH.1 hKH.2
  have : IsSimpleGroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := hQq.2.1
  exact catalog_of_mem_solomonKStar hG hK _ hQq.2.2
    ((QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K))).comp
      (QuotientGroup.mk' (pPrimeCore 2 ↥K)))
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))

theorem three_le_pRank_sup_of_commute {A B : Subgroup G} (hAB : ⁅A, B⁆ = ⊥) {t : G}
    (htA : t ∈ A) (ht2 : orderOf t = 2) (htc : t ∉ centralizer (A : Set G))
    (hB : 2 ≤ CFSG.Open.pRank 2 B) : 3 ≤ CFSG.Open.pRank 2 (A ⊔ B) := by
  classical
  obtain ⟨E, hEB, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) B
  have hAC : A ≤ centralizer (B : Set G) := commutator_eq_bot_iff_le_centralizer.mp hAB
  have htB : ∀ y ∈ B, y * t = t * y := fun y hy => (mem_centralizer_iff.mp (hAC htA)) y hy
  have htnB : t ∉ B := by
    intro htB'
    apply htc
    rw [mem_centralizer_iff]
    intro a ha
    exact ((mem_centralizer_iff.mp (hAC ha)) t htB').symm
  have hzt : ∀ y ∈ zpowers t, y = 1 ∨ y = t := by
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [← zpow_mod_orderOf, ht2]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
  have ht1 : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have hEt : E ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyt⟩
    rcases hzt y hyt with h | h
    · exact h ▸ one_mem _
    · exact absurd (h ▸ hEB hyE) htnB
  have hEc := hE.1
  have hc : ∀ (x : E) (y : zpowers t), Commute (E.subtype x) ((zpowers t).subtype y) := by
    intro x y
    rcases hzt y y.2 with h | h
    · change Commute (x : G) (y : G)
      rw [h]
      exact Commute.one_right _
    · change Commute (x : G) (y : G)
      rw [h]
      exact htB x (hEB x.2)
  let f : E × zpowers t →* G := MonoidHom.noncommCoprod E.subtype (zpowers t).subtype hc
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : G) * y = 1 := hxy
    have hyE : (y : G) ∈ E := by
      rw [eq_inv_of_mul_eq_one_right hxy']
      exact E.inv_mem x.2
    have hy1 : (y : G) = 1 := by
      have : (y : G) ∈ E ⊓ zpowers t := ⟨hyE, y.2⟩
      rw [hEt, mem_bot] at this
      exact this
    rw [hy1, mul_one] at hxy'
    have hx1 : x = 1 := Subtype.ext hxy'
    have hy1' : y = 1 := Subtype.ext hy1
    rw [hx1, hy1']
    rfl
  have key : CFSG.Open.pRank 2 B + 1 ≤ CFSG.Open.pRank 2 (A ⊔ B) := by
    refine SectionRank.le_pRank_of_injective (A := E × zpowers t) (by norm_num) ?_ ?_ ?_ f hf ?_
    · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
      refine Prod.ext (mul_comm' x₁ x₂) (Subtype.ext ?_)
      change (y₁ : G) * y₂ = y₂ * y₁
      rcases hzt y₁ y₁.2 with h | h <;> rcases hzt y₂ y₂.2 with h' | h' <;> simp [h, h']
    · rintro ⟨x, y⟩
      refine Prod.ext (Subtype.ext (hE.2 x x.2)) (Subtype.ext ?_)
      change (y : G) ^ 2 = 1
      rcases hzt y y.2 with h | h
      · rw [h, one_pow]
      · rw [h, ht1]
    · rw [Nat.card_prod, hcard, Nat.card_zpowers, ht2, pow_succ]
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      exact mul_mem (mem_sup_right (hEB x.2)) (mem_sup_left (zpowers_le.mpr htA y.2))
  omega

theorem exists_noncentral_involution (hq : QuasisimpleTwoPartInput) (hG : KStarKProper G)
    {K : Subgroup G} (hKs : K ∈ solomonKStar G) (hKq : IsQuasisimple ↥K) :
    ∃ t ∈ K, orderOf t = 2 ∧ t ∉ centralizer (K : Set G) := by
  classical
  by_contra hall
  push Not at hall
  obtain ⟨E, hEK, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) K
  have h2 := two_le_pRank_of_mem_solomonKStar hKs
  have := Fintype.ofFinite ↥E
  have h4 : 4 ≤ Fintype.card ↥E := by
    rw [← Nat.card_eq_fintype_card, hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 K := Nat.pow_le_pow_right (by norm_num) h2
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_ne (s := Finset.univ)
    (by rw [Finset.card_univ]; omega) (1 : ↥E)
  obtain ⟨v, hv, hvu⟩ := Finset.exists_mem_ne (s := Finset.univ.erase (1 : ↥E))
    (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega) u
  have hv1 : v ≠ 1 := Finset.ne_of_mem_erase hv
  have hord : ∀ w : ↥E, w ≠ 1 → orderOf (w : G) = 2 := fun w hw =>
    orderOf_eq_prime (hE.2 w w.2) fun h => hw (Subtype.ext h)
  have huK : (u : G) ∈ K := hEK u.2
  have hvK : (v : G) ∈ K := hEK v.2
  have huv : (u : G) ≠ v := fun h => hvu (Subtype.ext h).symm
  have hcen : ∀ {w : G} (hwK : w ∈ K), w ∈ centralizer (K : Set G) →
      (⟨w, hwK⟩ : ↥K) ∈ center ↥K := fun hwK hw => by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext ((mem_centralizer_iff.mp hw) y y.2)
  obtain ⟨x, hx2, hxc⟩ := hq.1 ↥K hKq (catalog_center_of_mem_solomonKStar hG hKs hKq)
    ⟨u, huK⟩ ⟨v, hvK⟩
    (by rw [Subgroup.orderOf_mk]; exact hord u hu) (by rw [Subgroup.orderOf_mk]; exact hord v hv1)
    (fun h => huv (congrArg (fun w : ↥K => (w : G)) h)) (hcen huK (hall u huK (hord u hu)))
    (hcen hvK (hall v hvK (hord v hv1)))
  apply hxc
  have hx2' : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx2
  exact hcen x.2 (hall x x.2 hx2')

theorem isKBalanced_of_ssubset (h315a : Lemma315aInputFor 𝒜)
    (hq : QuasisimpleTwoPartInput) (hKK : KStarKProper G) (hG : 𝒜 G) {N : Subgroup G}
    (hN : IsSolomonChoice N) {N' : Subgroup G}
    (hsub : kStarComponents N ⊂ kStarComponents N') : IsKBalanced N' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hXN', hXN⟩ := Set.exists_of_ssubset hsub
  obtain ⟨K₁, hK₁, -⟩ := exists_mem_kStarComponents_ne hN ⊥
  obtain ⟨K₂, hK₂, hK₂₁⟩ := exists_mem_kStarComponents_ne hN K₁
  have hK₁' : K₁ ∈ kStarComponents N' := hsub.1 hK₁
  have hK₂' : K₂ ∈ kStarComponents N' := hsub.1 hK₂
  have hX₁ : X ≠ K₁ := fun h => hXN (h ▸ hK₁)
  have hX₂ : X ≠ K₂ := fun h => hXN (h ▸ hK₂)
  set S := kStarComponents N' with hS
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin ↥S
  set Kf : Fin r → Subgroup G := fun i => (e.symm i : Subgroup G) with hKfdef
  have hKf : ∀ i, Kf i ∈ S := fun i => (e.symm i).2
  have hinj : Function.Injective Kf := fun i j h => e.symm.injective (Subtype.ext h)
  have hiff : ∀ J : Subgroup G, (IsTwoComponentIn J N' ∧ J ∈ solomonKStar G) ↔ ∃ i, Kf i = J := by
    intro J
    constructor
    · intro hJ
      refine ⟨e ⟨J, hJ⟩, ?_⟩
      simp only [hKfdef, Equiv.symm_apply_apply]
    · rintro ⟨i, rfl⟩
      exact hKf i
  have hr : S.ncard = r := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fin]
  have h2 : 2 ≤ (kStarComponents N).ncard := by
    rw [← Set.ncard_pair (Ne.symm hK₂₁)]
    exact Set.ncard_le_ncard (Set.insert_subset hK₁ (Set.singleton_subset_iff.mpr hK₂))
  have h3 : 3 ≤ r := by
    have := Set.ncard_lt_ncard hsub
    omega
  refine ⟨r, Kf, hinj, hiff, by omega, ?_, ?_, Or.inl h3⟩
  · intro i j hij
    exact FooteLit.commutator_le_oddCoreIn_of_ne (hKf i).1 (hKf j).1 fun h => hij (hinj h)
  ·
    obtain ⟨i, hi⟩ := (hiff X).mp hXN'
    refine ⟨i, ?_⟩
    rw [hi, SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup]
    have hle : K₁ ⊔ K₂ ≤ (oddTwoCoreIn N' ⊔ twoLayerIn N') ⊓ coreActionKernel X := by
      refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
      · exact (le_twoLayerIn_of_isTwoComponentIn hK₁'.1).trans le_sup_right
      · exact GSThmB.B5a.le_coreActionKernel_of_ne hXN'.1.1 hK₁'.1.1 hXN'.1.2 hK₁'.1.2 hX₁
      · exact (le_twoLayerIn_of_isTwoComponentIn hK₂'.1).trans le_sup_right
      · exact GSThmB.B5a.le_coreActionKernel_of_ne hXN'.1.1 hK₂'.1.1 hXN'.1.2 hK₂'.1.2 hX₂
    obtain ⟨t, htK, ht2, htc⟩ := exists_noncentral_involution hq hKK hK₁.2
      (isQuasisimple_of_mem_kStarComponents h315a hG hN hK₁)
    have hcomm := commutator_eq_bot_of_mem_kStarComponents h315a hG hN hK₁ hK₂ (Ne.symm hK₂₁)
    exact (three_le_pRank_sup_of_commute hcomm htK ht2 htc
      (two_le_pRank_of_mem_solomonKStar hK₂.2)).trans (SectionRank.pRank_mono (by norm_num) hle)

theorem kStarComponents_eq_of_subset (h315a : Lemma315aInputFor 𝒜)
    (hq : QuasisimpleTwoPartInput) (hKK : KStarKProper G) (hG : 𝒜 G) {N : Subgroup G}
    (hN : IsSolomonChoice N) {N' : Subgroup G} (hsub : kStarComponents N ⊆ kStarComponents N') :
    kStarComponents N' = kStarComponents N := by
  by_contra hne
  have hss : kStarComponents N ⊂ kStarComponents N' := hsub.ssubset_of_ne fun h => hne h.symm
  exact hne (kStarComponents_eq_of_isKBalanced hN
    (isKBalanced_of_ssubset h315a hq hKK hG hN hss) hsub)

theorem lemma316BalancedInputFor_of_noncentral (h32 : Lemma32InputFor 𝒜)
    (h315a : Lemma315aInputFor 𝒜) (h315c : Lemma315cInputFor 𝒜)
    (hq : QuasisimpleTwoPartInput)
    (h𝒜 : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → KStarKProper G) :
    Lemma316BalancedInputFor 𝒜 :=
  fun G _ _ hG _ hN _ h𝒮 hne => kStarComponents_eq_of_subset h315a hq (h𝒜 G hG) hG hN
    (kStarComponents_subset_normalizer h32 h315a h315c hG hN h𝒮 hne)

end CFSG.ComponentClassification.Sol76T13
