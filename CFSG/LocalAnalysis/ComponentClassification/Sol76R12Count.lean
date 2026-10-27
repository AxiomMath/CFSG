module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Reduce
public import CFSG.LocalAnalysis.ComponentClassification.Sol76R12Rank

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def Lemma32RankTwoKernelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (A₁ A₂ : Subgroup G), orderOf b = 2 →
    IsTwoComponentIn A₁ (centralizer ({b} : Set G)) →
    IsTwoComponentIn A₂ (centralizer ({b} : Set G)) → A₁ ≠ A₂ → b ∈ A₂ →
    CFSG.pRank 2 ↥A₂ = 2 →
    Blueprint.Catalog ((↥A₂ ⧸ pPrimeCore 2 ↥A₂) ⧸ center (↥A₂ ⧸ pPrimeCore 2 ↥A₂)) →
    CFSG.pRank 2 ↥((oddTwoCoreIn (centralizer ({b} : Set G)) ⊔
      twoLayerIn (centralizer ({b} : Set G))) ⊓ coreActionKernel A₁) ≤ 2 →
    ∀ T : Subgroup G, IsPGroup 2 T → T ≤ centralizer ({b} : Set G) →
      T ≤ coreActionKernel A₁ → T ≤ coreActionKernel A₂ → Nat.card T ≤ 2

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_of_odd_kStarKernel {N K : Subgroup G} (hN : IsKBalanced N)
    (hr : (kStarComponents N).ncard = 2) (hK : K ∈ kStarComponents N)
    (hD : ¬ 2 ∣ Nat.card ↥(kStarKernel N)) : 3 ≤ CFSG.pRank 2 ↥K := by
  classical
  obtain ⟨r, Kf, hinj, hiff, h2r, -, -, hc3⟩ := hN
  have hmem : ∀ i, Kf i ∈ kStarComponents N := fun i => (hiff (Kf i)).mpr ⟨i, rfl⟩
  have hr2 : r = 2 := by
    by_contra hne
    have h3 : 3 ≤ r := by omega
    have hlt : 2 < (kStarComponents N).ncard := by
      refine (Set.two_lt_ncard (Set.toFinite _)).mpr ⟨Kf ⟨0, by omega⟩, hmem _,
        Kf ⟨1, by omega⟩, hmem _, Kf ⟨2, by omega⟩, hmem _, ?_, ?_, ?_⟩ <;>
      · intro h
        have := hinj h
        simp at this
    omega
  subst hr2
  obtain ⟨i, hi⟩ := (hiff K).mp hK
  rcases hc3 with h3 | h3b | ⟨h0, h1, -⟩
  · omega
  · exfalso
    apply hD
    have hY : (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N) ≤
        kStarKernel N :=
      inf_le_inf_right _ (sup_le (map_subtype_le _) (map_subtype_le _))
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h3b
    obtain ⟨x, hx, hx2⟩ := exists_orderOf_eq_two_of_pRank h3b
    have h := orderOf_dvd_natCard (⟨x, hY hx⟩ : ↥(kStarKernel N))
    rwa [Subgroup.orderOf_mk, hx2] at h
  · fin_cases i
    · rw [← hi]
      exact h0
    · rw [← hi]
      exact h1

theorem lemma32ConditionTwoRankTwoInputFor_of_kernel {𝒜 : Thm13Ambient}
    (hq : QuasisimpleTwoPartInput)
    (h𝒜 : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → KStarKProper G)
    (hR : Lemma32RankTwoKernelInput) : Lemma32ConditionTwoRankTwoInputFor 𝒜 := by
  classical
  intro G _ _ hG N hN hr K hK K₀ hK₀ hKK₀ b hbK hb2 hbQ hCr hall
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKK := h𝒜 G hG
  by_contra hcon
  push Not at hcon
  obtain ⟨A₁, A₂, hA, hpair⟩ := Set.ncard_eq_two.mp hCr
  have hA₁ : A₁ ∈ kStarComponents (centralizer ({b} : Set G)) := by
    rw [hpair]
    simp
  have hA₂ : A₂ ∈ kStarComponents (centralizer ({b} : Set G)) := by
    rw [hpair]
    simp
  have hbQ₀ : b ∈ coreActionKernel K₀ := mem_coreActionKernel_of_ne hK hK₀ hKK₀ hbK
  have hres := hR G b A₁ A₂ hb2 hA₁.1 hA₂.1 hA (hall A₂ hA₂).2.1 (hall A₂ hA₂).2.2
    (catalog_coreQuotient_of_mem_solomonKStar hKK hA₂.1 hA₂.2) (by
      have := hcon A₁ hA₁
      omega)
  have hbKC : b ∈ K ⊓ centralizer ({b} : Set G) :=
    mem_inf.mpr ⟨hbK, mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨S, hSKC, hbS, hS2, hScard⟩ : ∃ S : Subgroup G,
      S ≤ K ⊓ centralizer ({b} : Set G) ∧ b ∈ S ∧ IsPGroup 2 S ∧
      Nat.card S = 2 ^ (Nat.card ↥(K ⊓ centralizer ({b} : Set G))).factorization 2 := by
    have hbz : IsPGroup 2 (zpowers (⟨b, hbKC⟩ : ↥(K ⊓ centralizer ({b} : Set G)))) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hb2, pow_one])
    obtain ⟨Sy, hSy⟩ := hbz.exists_le_sylow
    refine ⟨(Sy : Subgroup ↥(K ⊓ centralizer ({b} : Set G))).map
      (K ⊓ centralizer ({b} : Set G)).subtype, map_subtype_le _,
      ⟨⟨b, hbKC⟩, hSy (mem_zpowers _), rfl⟩, Sy.isPGroup'.map _, ?_⟩
    rw [card_map_of_injective (Subgroup.subtype_injective _), Sy.card_eq_multiplicity]
  have hSK : S ≤ K := hSKC.trans inf_le_left
  have hSN : S ≤ normalizer (kStarKernel N : Set G) := fun s hs =>
    le_normalizer_kStarKernel N (hK.1.1 (hSK hs))
  obtain ⟨P, hPD, hP2, hPcard, hPS⟩ : ∃ P : Subgroup G, P ≤ kStarKernel N ∧
      IsPGroup 2 P ∧ Nat.card P = 2 ^ (Nat.card ↥(kStarKernel N)).factorization 2 ∧
      S ≤ normalizer (P : Set G) := by
    obtain ⟨Py, hPy⟩ := exists_sylow_normalized hSN hS2
    refine ⟨(Py : Subgroup ↥(kStarKernel N)).map (kStarKernel N).subtype, map_subtype_le _,
      Py.isPGroup'.map _, ?_, hPy⟩
    rw [card_map_of_injective (Subgroup.subtype_injective _), Py.card_eq_multiplicity]
  have hPScomm : ∀ p ∈ P, ∀ s ∈ S, p * s = s * p := by
    intro p hp s hs
    have hKD : K ≤ solomonKStarOf N := le_iSup₂_of_le K hK le_rfl
    have h1 : s⁻¹ * p⁻¹ * s * p ∈ oddCoreIn (solomonKStarOf N) :=
      (mem_inf.mp (hPD hp)).2.2 s (hKD (hSK hs))
    have h2 : s⁻¹ * p⁻¹ * s * p ∈ P := by
      have h3 : s⁻¹ * p⁻¹ * s⁻¹⁻¹ ∈ P :=
        (mem_normalizer_iff.mp (hPS (inv_mem hs)) p⁻¹).mp (inv_mem hp)
      rw [inv_inv] at h3
      exact mul_mem h3 hp
    have h4 := eq_one_of_mem_of_isPGroup hP2 (coprime_card_oddCoreIn _) h2 h1
    have h5 : p * s = p * s * (s⁻¹ * p⁻¹ * s * p) := by rw [h4, mul_one]
    rw [h5]
    group
  have hPC : P ≤ centralizer ({b} : Set G) := fun p hp =>
    mem_centralizer_singleton_iff.mpr (hPScomm p hp b hbS)
  have hYC : P ⊔ S ≤ centralizer ({b} : Set G) := sup_le hPC (hSKC.trans inf_le_right)
  have hYp : IsPGroup 2 ↥(P ⊔ S) := hP2.to_sup_of_normal_left' hS2 hPS
  have hYQ₀ : P ⊔ S ≤ coreActionKernel K₀ :=
    sup_le (hPD.trans (kStarKernel_le_coreActionKernel hK₀))
      fun s hs => mem_coreActionKernel_of_ne hK hK₀ hKK₀ (hSK hs)
  obtain ⟨hY2, -, ⟨e⟩, h212, -⟩ := pump_facts hK₀ hbQ₀ hb2
  have hodd : ∀ R : Subgroup G, R ≤ P ⊔ S →
      ¬ 2 ∣ Nat.card ↥⁅R, twoLayerIn (K₀ ⊓ centralizer ({b} : Set G))⁆ := by
    intro R hRY h
    have hle : ⁅R, twoLayerIn (K₀ ⊓ centralizer ({b} : Set G))⁆ ≤ oddCoreIn K₀ := by
      refine commutator_le.mpr fun r hr k hk => ?_
      have hkK₀ : k ∈ K₀ := (hY2.1.trans inf_le_left) hk
      have h1 : (k⁻¹)⁻¹ * (r⁻¹)⁻¹ * k⁻¹ * r⁻¹ ∈ oddCoreIn K₀ :=
        (inv_mem (hYQ₀ (hRY hr))).2 k⁻¹ (inv_mem hkK₀)
      have h2 : ⁅r, k⁆ = ((k⁻¹)⁻¹ * (r⁻¹)⁻¹ * k⁻¹ * r⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [h2]
      exact inv_mem h1
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (coprime_card_oddCoreIn K₀)
      (h.trans (card_dvd_of_le hle))
  have hYA : ∀ g ∈ P ⊔ S, ∀ A : Subgroup G, (A = A₁ ∨ A = A₂) →
      (A.map (MulAut.conj g).toMonoidHom = A₁ ∨ A.map (MulAut.conj g).toMonoidHom = A₂) := by
    intro g hg A hA'
    have hAm : A ∈ kStarComponents (centralizer ({b} : Set G)) := by
      rcases hA' with rfl | rfl
      · exact hA₁
      · exact hA₂
    have hC' : (centralizer ({b} : Set G)).map (MulAut.conj g).toMonoidHom =
        centralizer ({b} : Set G) := mem_normalizer_iff_map_conj_eq.mp (le_normalizer (hYC hg))
    have h1 : A.map (MulAut.conj g).toMonoidHom ∈ kStarComponents (centralizer ({b} : Set G)) := by
      have h := isTwoComponentIn_map (MulAut.conj g) hAm.1
      rw [hC'] at h
      exact ⟨h, map_mem_solomonKStar _ hAm.2⟩
    rw [hpair] at h1
    simpa using h1
  have hidx : (normalizer (A₁ : Set G)).relIndex (P ⊔ S) ≤ 2 := relIndex_normalizer_le_two hA hYA
  have hXN : ∀ M ∈ kStarComponents (centralizer ({b} : Set G)),
      (P ⊔ S) ⊓ normalizer (A₁ : Set G) ≤ normalizer (M : Set G) := by
    intro M hM x hx
    obtain ⟨hxY, hxA⟩ := mem_inf.mp hx
    rw [hpair] at hM
    rcases hM with rfl | hM2
    · exact hxA
    rw [Set.mem_singleton_iff] at hM2
    subst hM2
    have hxA' : A₁.map (MulAut.conj x).toMonoidHom = A₁ := mem_normalizer_iff_map_conj_eq.mp hxA
    rcases hYA x hxY _ (Or.inr rfl) with h | h
    · exact absurd (Subgroup.map_injective (MulAut.conj x).injective (h.trans hxA'.symm))
        (Ne.symm hA)
    · exact mem_normalizer_iff_map_conj_eq.mpr h
  have hYL : twoLayerIn (K₀ ⊓ centralizer ({b} : Set G)) ≤
      twoLayerIn (centralizer ({b} : Set G)) :=
    h212.trans (solomonKStarOf_le_twoLayerIn _)
  have hXcak : ∀ M ∈ kStarComponents (centralizer ({b} : Set G)),
      (P ⊔ S) ⊓ normalizer (A₁ : Set G) ≤ coreActionKernel M := by
    intro M hM
    have hMK : M ∈ pumpSet K₀ (centralizer ({b} : Set G)) := ⟨hM, (hall M hM).1⟩
    have ht : Nat.card (↥M ⧸ Open.fusionZStar ↥M) =
        Nat.card (↥(twoLayerIn (K₀ ⊓ centralizer ({b} : Set G))) ⧸
          Open.fusionZStar ↥(twoLayerIn (K₀ ⊓ centralizer ({b} : Set G)))) := by
      rw [card_fusionZStar_of_mem_pumpSet hK₀ hbQ₀ hb2 hMK, Nat.card_congr e.toEquiv]
    exact le_coreActionKernel_of_odd_commutator hM.1 hYL
      (UnbalancedCorr.commutator_eq_of_isPComponent hY2.1 hY2.2)
      (isQuasisimple_quotient_of_isPComponent hY2.1 hY2.2) hMK.2 ht
      (inf_le_left.trans hYC) (hXN M hM) (hodd _ inf_le_left)
  have hXcard : Nat.card ↥((P ⊔ S) ⊓ normalizer (A₁ : Set G)) ≤ 2 :=
    hres _ (hYp.to_le inf_le_left) (inf_le_left.trans hYC) (hXcak A₁ hA₁) (hXcak A₂ hA₂)
  have hYX : Nat.card ↥(P ⊔ S) ≤ 2 * Nat.card ↥((P ⊔ S) ⊓ normalizer (A₁ : Set G)) := by
    have h := relIndex_mul_card (normalizer (A₁ : Set G)) (P ⊔ S)
    rw [inf_comm] at h
    rw [← h]
    exact Nat.mul_le_mul_right _ hidx
  have hR2 := four_mul_card_inf_coreActionKernel_le hq hK.1
    (catalog_coreQuotient_of_mem_solomonKStar hKK hK.1 hK.2) hbK hb2 hbQ hS2 hSK hScard
  have hSY : Nat.card S ≤ Nat.card ↥(P ⊔ S) := card_le_of_le le_sup_right
  have hpos : 0 < Nat.card ↥(S ⊓ coreActionKernel K) := Nat.card_pos
  have hS4 : Nat.card S = 4 := by omega
  have hSeq : S = P ⊔ S := eq_of_le_of_card_ge le_sup_right (by omega)
  have hPK : P ≤ S ⊓ coreActionKernel K :=
    le_inf (hSeq ▸ le_sup_left) (hPD.trans (kStarKernel_le_coreActionKernel hK))
  have hP1 : Nat.card P = 1 := by
    have h1 := card_le_of_le hPK
    have h2 : 0 < Nat.card P := Nat.card_pos
    omega
  have hDodd : ¬ 2 ∣ Nat.card ↥(kStarKernel N) := by
    intro h
    have h1 := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp h
    have h2 : 2 ≤ Nat.card P := by
      rw [hPcard]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have h3 := three_le_pRank_of_odd_kStarKernel hN.1 hr hK hDodd
  have h2 := R12.pRank_le_two_of_card_sylow hb2 hSKC hbS hS2 hScard hS4
  omega

end CFSG.ComponentClassification.Sol76T13
