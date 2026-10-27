module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitQuotientHyp

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem footeFamilyType_of_fusionZStar_equiv {X Y : Type} [Group X] [Group Y] {A : Subgroup X}
    {B : Subgroup Y} (e : A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B)
    (h : FooteFamilyType B) : FooteFamilyType A := by
  rcases h with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, h5, hL⟩
  · exact Or.inl ⟨e.trans e7⟩
  · exact Or.inr ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hL⟩

theorem le_pRank_of_card {H : Type*} [Group H] [Finite H] {E : Subgroup H}
    (hE : IsElementaryAbelian 2 E) {r : ℕ} (hcard : Nat.card E = 2 ^ r) :
    r ≤ CFSG.pRank 2 H := by
  apply le_csSup
  · refine ⟨Nat.card H, ?_⟩
    rintro k ⟨B, -, hB⟩
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : Nat.card B ≤ Nat.card H := Subgroup.card_le_card_group B
    omega
  · exact ⟨E, hE, hcard⟩

variable {G : Type} [Group G] [Finite G]

theorem card_le_two_of_odd_inf {A C S : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htA : t ∈ normalizer (A : Set G)) (hodd : Odd (Nat.card ↥(A ⊓ C))) (hS : IsPGroup 2 S)
    (hSX : S ≤ (A ⊔ zpowers t) ⊓ C) : Nat.card S ≤ 2 := by
  classical
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hSA : S ⊓ A = ⊥ := eq_bot_of_le_two_group_of_le_odd hS hodd inf_le_left
    (le_inf inf_le_right (inf_le_left.trans (hSX.trans inf_le_right)))
  have hle : zpowers t ≤ normalizer (A : Set G) := (zpowers_le).mpr htA
  have hform : ∀ s ∈ S, s ∉ A → ∃ a ∈ A, s = t * a := by
    intro s hs hsA
    have h1 : s ∈ zpowers t ⊔ A := by rw [sup_comm]; exact (hSX hs).1
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right (zpowers t) A hle] at h1
    obtain ⟨u, hu, a, ha, rfl⟩ := h1
    rcases UnbalancedGS.OrbitFixedComponent.eq_one_or_eq_of_mem_zpowers htt hu with rfl | rfl
    · exact absurd (show (1 : G) * a ∈ A by rw [one_mul]; exact ha) hsA
    · exact ⟨a, ha, rfl⟩
  have hinj : Function.Injective fun s : S => decide ((s : G) ∈ A) := by
    intro s₁ s₂ h
    simp only [decide_eq_decide] at h
    by_cases h₁ : (s₁ : G) ∈ A
    · have h₂ := h.mp h₁
      have e₁ : (s₁ : G) = 1 := by
        have := mem_inf.mpr ⟨s₁.2, h₁⟩
        rw [hSA, mem_bot] at this
        exact this
      have e₂ : (s₂ : G) = 1 := by
        have := mem_inf.mpr ⟨s₂.2, h₂⟩
        rw [hSA, mem_bot] at this
        exact this
      exact Subtype.ext (e₁.trans e₂.symm)
    · have h₂ : (s₂ : G) ∉ A := fun h2 => h₁ (h.mpr h2)
      obtain ⟨a₁, ha₁, e₁⟩ := hform s₁ s₁.2 h₁
      obtain ⟨a₂, ha₂, e₂⟩ := hform s₂ s₂.2 h₂
      have h3 : (s₁ : G)⁻¹ * s₂ ∈ S ⊓ A := by
        refine mem_inf.mpr ⟨mul_mem (inv_mem s₁.2) s₂.2, ?_⟩
        rw [e₁, e₂, show (t * a₁)⁻¹ * (t * a₂) = a₁⁻¹ * a₂ by group]
        exact mul_mem (inv_mem ha₁) ha₂
      rw [hSA, mem_bot] at h3
      exact Subtype.ext (inv_mul_eq_one.mp h3)
  calc Nat.card S ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

section Quotient

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 G)

theorem card_le_two_of_map_le {S : Subgroup G} (hS : IsPGroup 2 S)
    {Xq : Subgroup (G ⧸ pPrimeCore 2 G)} (hSX : S.map π ≤ Xq)
    (hXq : ∀ P : Sylow 2 ↥Xq, Nat.card P ≤ 2) : Nat.card S ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ((S.map π).subgroupOf Xq) = Nat.card S := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSX).toEquiv,
      GSThmB.OddQuot.card_map_of_isPGroup hS]
  have hS' : IsPGroup 2 ((S.map π).subgroupOf Xq) := by
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    exact IsPGroup.of_card (n := k) (by rw [hcard, hk])
  obtain ⟨Q, hQ⟩ := hS'.exists_le_sylow
  calc Nat.card S = Nat.card ((S.map π).subgroupOf Xq) := hcard.symm
    _ ≤ Nat.card Q := Subgroup.card_le_of_le hQ
    _ ≤ 2 := hXq Q

theorem footeConclusion_of_map {t : G} {L A J : Subgroup G} (hL : IsTwoComponentAt t L)
    (hJ : IsPComponent 2 J) (hAJ : A = J ⊔ conjugate J t)
    (h : FooteConclusion (π t) (L.map π) (A.map π)) : FooteConclusion t L A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := GSThmB.OddQuot.not_two_dvd_card_ker (H := G)
  obtain ⟨eA⟩ := GSThmB.OddQuot.nonempty_quotient_pPrimeCore_equiv π hker A
  obtain ⟨eL⟩ := GSThmB.OddQuot.nonempty_quotient_pPrimeCore_equiv π hker L
  have ht := hL.1
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  rcases h with ⟨⟨e⟩⟩ | ⟨Kq, hKq, hKqt, hAK⟩ | h3 | ⟨hs, he, hcl⟩ | ⟨hs, hodd⟩
  ·
    exact Or.inl ⟨eA.trans (e.trans eL.symm)⟩
  ·
    right; left
    have hJtop : IsPComponent 2 (J.subgroupOf ⊤) := isPComponent_subgroupOf_top_iff'.mpr hJ
    have hπJ : IsPComponent 2 ((J.map π).subgroupOf ⊤) := by
      have h1 := GSThmB.OddQuot.isPComponent_map π hker le_top hJtop
      rwa [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
    have hKqtop : IsPComponent 2 (Kq.subgroupOf ⊤) := isPComponent_subgroupOf_top_iff'.mpr hKq
    have hKqt' : IsPComponent 2 ((conjugate Kq (π t)).subgroupOf ⊤) :=
      isPComponent_subgroupOf_top_iff'.mpr (isPComponent_conjugate hKq (π t))
    have hle : J.map π ≤ Kq ⊔ conjugate Kq (π t) := by
      rw [← hAK, hAJ, Subgroup.map_sup]
      exact le_sup_left
    have hne : conjugate J t ≠ J := by
      intro hJt
      have h1 : conjugate (J.map π) (π t) = J.map π := by
        rw [← UnbalancedLayer.map_conjugate, hJt]
      rcases eq_or_eq_of_isPComponent_le_sup le_top le_top le_top hπJ hKqtop hKqt' hle with
        h2 | h2
      · exact hKqt (by rw [← h2, h1])
      · apply hKqt
        have hπtt : π t * π t = 1 := by rw [← map_mul, htt, map_one]
        have h3 : Kq = J.map π := by
          rw [← h1, h2, conjugate_conjugate_self_of_mul_self hπtt]
        exact h2.symm.trans h3.symm
    exact ⟨J, hJ, hne, hAJ⟩
  ·
    right; right; left
    rcases h3 with ⟨⟨e₁⟩, ⟨e₂⟩⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩ | ⟨⟨e₁⟩, ⟨e₂⟩⟩
    · exact Or.inl ⟨⟨eA.trans e₁⟩, ⟨eL.trans e₂⟩⟩
    · exact Or.inr (Or.inl ⟨⟨eA.trans e₁⟩, ⟨eL.trans e₂⟩⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨⟨eA.trans e₁⟩, ⟨eL.trans e₂⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨⟨eA.trans e₁⟩, ⟨eL.trans e₂⟩⟩))
  ·
    right; right; right; left
    refine ⟨eA.isSimpleGroup, ⟨fun f => he.false (eA.symm.trans (f.trans eL))⟩, ?_⟩
    have hCL : (coreActionKernel L).map π ≤ coreActionKernel (L.map π) := by
      have h1 := GSThmB.OddQuot.map_inf_coreActionKernel (H := G) (X := L)
        (Y := coreActionKernel L) (fun g hg => hg.1)
      rw [inf_idem] at h1
      rw [h1]
      exact inf_le_right
    have htA : t ∈ normalizer (A : Set G) := by
      apply mem_normalizer_of_conjugate_eq
      rw [hAJ, UnbalancedLayer.conjugate_sup, conjugate_conjugate_self_of_mul_self htt, sup_comm]
    have htX : t ∈ (A ⊔ zpowers t) ⊓ coreActionKernel L :=
      mem_inf.mpr ⟨mem_sup_right (mem_zpowers t),
        GSLit.mem_coreActionKernel_of_le_centralizer hL.2.1⟩
    have hXmap : ((A ⊔ zpowers t) ⊓ coreActionKernel L).map π ≤
        (A.map π ⊔ zpowers (π t)) ⊓ coreActionKernel (L.map π) := by
      refine (map_inf_le _ _ _).trans (inf_le_inf ?_ hCL)
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    have hbound : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ (A ⊔ zpowers t) ⊓ coreActionKernel L →
        Nat.card S ≤ 2 ∨ CFSG.pRank 2 ↥(A ⊓ coreActionKernel L) = 1 := by
      intro S hS hSX
      rcases hcl with ⟨P, hP⟩ | hrank
      · left
        refine card_le_two_of_map_le hS ((map_mono hSX).trans hXmap) fun Q => ?_
        have hPcard : Nat.card P = 2 := by
          rw [hP, Nat.card_congr (subgroupOfEquivOfLe (show zpowers (π t) ≤ _ from
            (zpowers_le).mpr (hXmap (mem_map_of_mem π htX)))).toEquiv, Nat.card_zpowers,
            orderOf_mk_eq_two ht]
        rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity P, hPcard]
      ·
        have hle1 : CFSG.pRank 2 ↥(A ⊓ coreActionKernel L) ≤ 1 := by
          rw [← hrank, SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top,
            ← SectionRank.pRank_eq_pRank_top_subgroup,
            ← SectionRank.pRank_eq_pRank_top_subgroup]
          obtain ⟨E, hEY, hE, hcard⟩ := SectionRank.exists_pRank one_lt_two (A ⊓ coreActionKernel L)
          have hEp : IsPGroup 2 E := IsPGroup.of_card hcard
          refine SectionRank.le_pRank one_lt_two ?_ (SectionRank.isElemAbelian_map hE π) ?_
          · refine (map_mono hEY).trans ((map_inf_le _ _ _).trans (inf_le_inf le_rfl hCL))
          · rw [GSThmB.OddQuot.card_map_of_isPGroup hEp, hcard]
        rcases Nat.lt_or_ge (CFSG.pRank 2 ↥(A ⊓ coreActionKernel L)) 1 with h0 | h1
        ·
          left
          have hodd : Odd (Nat.card ↥(A ⊓ coreActionKernel L)) := by
            by_contra hev
            obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2
              (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev))
            have := FooteLit.one_le_pRank_of_orderOf_eq_two hy
            omega
          exact card_le_two_of_odd_inf ht htA hodd hS hSX
        · right
          omega
    by_cases hY1 : CFSG.pRank 2 ↥(A ⊓ coreActionKernel L) = 1
    · exact Or.inr hY1
    left
    set X := (A ⊔ zpowers t) ⊓ coreActionKernel L with hX
    have hP0 : IsPGroup 2 ((zpowers t).subgroupOf X) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_congr (subgroupOfEquivOfLe ((zpowers_le).mpr htX)).toEquiv, Nat.card_zpowers,
        ht, pow_one]
    obtain ⟨Q, hQ⟩ := hP0.exists_le_sylow
    refine ⟨Q, ?_⟩
    have hQcard : Nat.card Q ≤ 2 := by
      have hQp : IsPGroup 2 ((Q : Subgroup X).map X.subtype) := by
        obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
        exact IsPGroup.of_card (n := k)
          (by rw [Subgroup.card_map_of_injective X.subtype_injective, hk])
      rcases hbound _ hQp (map_subtype_le _) with h1 | h1
      · rwa [Subgroup.card_map_of_injective X.subtype_injective] at h1
      · exact absurd h1 hY1
    have h0card : Nat.card ((zpowers t).subgroupOf X) = 2 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe ((zpowers_le).mpr htX)).toEquiv, Nat.card_zpowers,
        ht]
    exact (Subgroup.eq_of_le_of_card_ge hQ (by rw [h0card]; exact hQcard)).symm
  ·
    right; right; right; right
    exact ⟨eA.isSimpleGroup, (ClassicalInvolution.oddLieType_congr eA).2 hodd⟩

end Quotient

theorem footeOddCoreReduction_of_inputs (hLB : FooteLBalanceInput) : FooteOddCoreReduction := by
  intro G _ _ t L hmin hce
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hO
  obtain ⟨⟨hKp, hcore, hLt, hmax, hfam, hrank⟩, hcon⟩ := hce
  set π := QuotientGroup.mk' (pPrimeCore 2 G) with hπ
  have hker := GSThmB.OddQuot.not_two_dvd_card_ker (H := G)
  have hOodd : Odd (Nat.card (pPrimeCore 2 G)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))
  have hlt : Nat.card (G ⧸ pPrimeCore 2 G) < Nat.card G := by
    have h1 := (pPrimeCore 2 G).card_mul_index
    have h2 : 1 < Nat.card (pPrimeCore 2 G) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hO
    have h3 : 0 < (pPrimeCore 2 G).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    change (pPrimeCore 2 G).index < Nat.card G
    nlinarith
  obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_quotient_fusionZStar_equiv π hker L
  obtain ⟨eO⟩ := GSThmB.OddQuot.nonempty_quotient_pPrimeCore_equiv π hker L
  have hrank' : 2 ≤ CFSG.pRank 2 ↥(L.map π) := by
    rw [← pRank_quotient_pPrimeCore, ← pRank_eq_of_mulEquiv one_lt_two eO,
      pRank_quotient_pPrimeCore]
    exact hrank
  obtain ⟨J, hJ, -, hAJ, -⟩ := foote_lemma_2_1_iv hLt.1 hLt.2.1 hLt.2.2
  have hAmap : (conjClosure L (pLayer G 2)).map π = conjClosure (L.map π) (pLayer _ 2) := by
    rw [map_conjClosure, UnbalancingLocal.Correspondence.map_pLayer_of_coprime_kernel π
      (QuotientGroup.mk'_surjective _) hker]
  refine hmin.2 _ hlt (π t) (L.map π) ⟨⟨GSThmB.OddQuot.kProper_quotient hKp _,
    footeCoreHypothesis_quotient hOodd hcore, isTwoComponentAt_map hLt,
    footePointedMaximal_map hLB hmax,
    footeFamilyType_of_fusionZStar_equiv eZ.symm hfam, hrank'⟩, ?_⟩
  intro hconc
  rw [← hAmap] at hconc
  exact hcon (footeConclusion_of_map hLt hJ hAJ hconc)

end CFSG.ComponentClassification.FooteLit
