module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Four

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_mul_mem_normalizer_of_isSylowOf {p : ℕ} [Fact p.Prime] {Q K : Subgroup G}
    (hQ : IsSylowOf p Q K) {g : G} (hg : g ∈ normalizer (K : Set G)) :
    ∃ m ∈ K, g * m ∈ normalizer (Q : Set G) := by
  have hQg : IsSylowOf p (conjugate Q g) K := by
    refine isSylowOf_of_card ?_ ?_
    · rw [← conjugate_eq_of_mem_normalizer hg]
      exact map_mono hQ.le
    · rw [card_conjugate_eq_card, hQ.card_eq]
  obtain ⟨m, hm, hmQ⟩ := hQ.exists_mem_conj hQg
  refine ⟨m, hm, mem_normalizer_of_conjugate_eq ?_⟩
  rw [← UnbalancedLayer.conjugate_conjugate]
  ext x
  rw [mem_conjugate_iff, hmQ]
  constructor
  · intro hx
    rwa [show m⁻¹ * (m * x * m⁻¹) * m = x by group] at hx
  · intro hx
    rwa [show m⁻¹ * (m * x * m⁻¹) * m = x by group]

theorem normalizer_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {Q K X : Subgroup G}
    (hQ : IsSylowOf p Q K) (hKX : K ≤ X) (hQX : normalizer (Q : Set G) ≤ X) :
    normalizer (K : Set G) ≤ X := by
  intro g hg
  obtain ⟨m, hm, hgm⟩ := exists_mul_mem_normalizer_of_isSylowOf hQ hg
  rw [show g = g * m * m⁻¹ by group]
  exact mul_mem (hQX hgm) (inv_mem (hKX hm))

theorem exists_isKleinFour_of_mem_footeFamilyOf (h : FooteSec4 G L) {B : Subgroup G}
    (hBF : B ∈ footeFamilyOf L) : ∃ W : Subgroup G, IsKleinFour W ∧ W ≤ B := by
  have hrank : CFSG.Open.pRank 2 B = 2 := by
    have h1 := h.hrank2 _ hBF
    rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h1
  obtain ⟨V, hVB, hVel, hVcard⟩ := SectionRank.exists_pRank one_lt_two B
  rw [hrank] at hVcard
  exact ⟨V, isKleinFour_of_card_eq_four (by rw [hVcard]; norm_num) hVel.2, hVB⟩

theorem exists_isKleinFour_le_of_isSylowOf {Q K W₀ : Subgroup G} (hQ : IsSylowOf 2 Q K)
    (hW₀ : IsKleinFour W₀) (hW₀K : W₀ ≤ K) : ∃ W : Subgroup G, IsKleinFour W ∧ W ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW₀p : IsPGroup 2 W₀ := IsPGroup.of_card (n := 2) (by rw [hW₀.card_four]; norm_num)
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hQ hW₀K hW₀p
  exact ⟨conjugate W₀ k, isKleinFour_of_card_eq_four
    (by rw [card_conjugate_eq_card, hW₀.card_four])
    (sq_eq_one_of_mem_conjugate (fun x hx => sq_eq_one_of_isKleinFour hW₀ hx) k),
    conjugate_le_of_forall hk⟩

theorem exists_isSylowOf_centralizes {M₁ M₂ : Subgroup G}
    (hN : normalizer (M₁ : Set G) = normalizer (M₂ : Set G))
    (hodd : Odd (Nat.card ↥(coreActionKernel M₁ ⊓ coreActionKernel M₂)))
    {P : Subgroup G} (hP : IsSylowOf 2 P (coreActionKernel M₁)) :
    ∃ R₂ : Subgroup G, IsSylowOf 2 R₂ (coreActionKernel M₂) ∧
      ∀ x ∈ P, ∀ y ∈ R₂, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C₁ := coreActionKernel M₁ with hC₁
  set C₂ := coreActionKernel M₂ with hC₂
  have hPN₂ : P ≤ normalizer (C₂ : Set G) := fun x hx =>
    mem_normalizer_coreActionKernel (hN ▸ (hP.le hx).1)
  have hC₂N₁ : C₂ ≤ normalizer (C₁ : Set G) := fun x hx =>
    mem_normalizer_coreActionKernel (hN.symm ▸ hx.1)
  set X := P ⊔ C₂ with hX
  have hXN₂ : X ≤ normalizer (C₂ : Set G) := sup_le hPN₂ le_normalizer
  have hXN₁ : X ≤ normalizer (C₁ : Set G) :=
    sup_le (fun x hx => le_normalizer (hP.le hx)) hC₂N₁
  obtain ⟨R, hR, hPR⟩ := exists_isSylowOf_ge_of_le (le_sup_left : P ≤ X) hP.isPGroup
  have hR₂ : IsSylowOf 2 (R ⊓ C₂) C₂ := hR.inf_of_le_normalizer le_sup_right hXN₂
  have hR₁ : R ⊓ C₁ = P :=
    hP.eq_of_le (le_inf hPR hP.le) inf_le_right (hR.isPGroup.to_le inf_le_left)
  refine ⟨R ⊓ C₂, hR₂, fun x hx y hy => ?_⟩
  have hxR : x ∈ R := hPR hx
  have hyR : y ∈ R := (mem_inf.mp hy).1
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ R ⊓ C₁ := by
    rw [hR₁]
    have hyN : y ∈ normalizer (P : Set G) := by
      rw [← hR₁]
      exact mem_normalizer_inf' (le_normalizer hyR) (hXN₁ (hR.le hyR))
    rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact mul_mem hx ((mem_normalizer_iff.mp hyN _).mp (inv_mem hx))
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ R ⊓ C₂ := by
    have hxN : x ∈ normalizer ((R ⊓ C₂ : Subgroup G) : Set G) :=
      mem_normalizer_inf' (le_normalizer hxR) (hXN₂ (hR.le hxR))
    refine mul_mem ?_ (inv_mem hy)
    exact (mem_normalizer_iff.mp hxN _).mp hy
  have h3 : x * y * x⁻¹ * y⁻¹ = 1 :=
    eq_one_of_mem_of_odd hR.isPGroup hodd (mem_inf.mp h1).1
      (mem_inf.mpr ⟨(mem_inf.mp h1).2, (mem_inf.mp h2).2⟩)
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

theorem centralizer_le_normalizer_of_mem (h : FooteSec4 G L) {M₁ M₂ : Subgroup G}
    (hM₁ : IsFooteM L M₁) (hM₂ : IsFooteM L M₂)
    (hN : normalizer (M₁ : Set G) = normalizer (M₂ : Set G))
    (hodd : Odd (Nat.card ↥(coreActionKernel M₁ ⊓ coreActionKernel M₂)))
    (hfour : ∀ W : Subgroup G, IsKleinFour W → W ≤ M₁ →
      ∃ F : Subgroup G, (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 8 ∧ W ≤ F ∧
        F ≤ coreActionKernel M₂)
    {t : G} (ht : orderOf t = 2) (htC : t ∈ coreActionKernel M₁) :
    centralizer ({t} : Set G) ≤ normalizer (M₁ : Set G) ∧ footeF L t ≤ M₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨P, hP, htP⟩ := exists_isSylowOf_ge_of_le (zpowers_le.mpr htC) ht2
  obtain ⟨R₂, hR₂, hPR₂⟩ := exists_isSylowOf_centralizes hN hodd hP
  obtain ⟨F₀, hF₀2, hF₀8, hF₀C⟩ := hM₂.exists_card_eight h
  have hF₀p : IsPGroup 2 F₀ := IsPGroup.of_card (n := 3) (by rw [hF₀8]; norm_num)
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hR₂ hF₀C hF₀p
  set F := conjugate F₀ k with hFdef
  have hFR : F ≤ R₂ := conjugate_le_of_forall hk
  have hF2 : ∀ x ∈ F, x ^ 2 = 1 := sq_eq_one_of_mem_conjugate hF₀2 k
  have hF8 : Nat.card F = 8 := by rw [card_conjugate_eq_card, hF₀8]
  have hFC : F ≤ coreActionKernel M₂ := hFR.trans hR₂.le
  have hFt : F ≤ centralizer ({t} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hPR₂ t (htP (mem_zpowers t)) x (hFR hx)).symm
  have hO : oddCoreOfCentralizer t ≤ normalizer (M₂ : Set G) := by
    refine le_of_forall_hyperplane_inf_centralizer_le (isMulCommutative_of_sq_eq_one hF2) hF2
      (fun h1 => by rw [h1, card_bot] at hF8; omega)
      (fun x hx => mem_normalizer_oddCoreOfCentralizer (hFt hx))
      (odd_card_oddCoreOfCentralizer t) fun B hBF hB => ?_
    have hB4 : Nat.card B = 4 := by omega
    have hB : IsKleinFour B := isKleinFour_of_card_eq_four hB4 fun x hx => hF2 x (hBF hx)
    exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (B : Set G)).trans
      (foote_lemma_4_5_iii_four h hM₂ hB hF2 hF8 hFC hBF))
  rw [← hN] at hO
  obtain ⟨hfix, -, hBmax, hBF⟩ := foote_lemma_4_5_i h hM₁ ht htC
  have hBM : footeF L t ≤ M₁ := by
    rw [← hfix, footeFixed_eq_oddResidualIn]
    refine (closure_le _).mpr fun g hg => ?_
    obtain ⟨hgX, h2⟩ := hg
    have hg' : g ∈ oddCoreOfCentralizer t ⊔ M₁ :=
      (sup_le (inf_le_left.trans le_sup_right) le_sup_left :
        (M₁ ⊓ centralizer ({t} : Set G)) ⊔ oddCoreOfCentralizer t ≤ _) hgX
    exact mem_of_two_element_of_mem_sup hO
      (by rw [oddResidualIn_eq_bot_of_odd (odd_card_oddCoreOfCentralizer t)]; exact bot_le) hg' h2
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 (footeF L t)
  obtain ⟨W₀, hW₀, hW₀B⟩ := exists_isKleinFour_of_mem_footeFamilyOf h hBF
  obtain ⟨W, hW, hWQ⟩ := exists_isKleinFour_le_of_isSylowOf hQ hW₀ hW₀B
  have hNQ : normalizer (Q : Set G) ≤ normalizer (M₁ : Set G) := by
    rw [hN]
    exact normalizer_le_normalizer_of_le h hM₂ hfour (hQ.le.trans hBM) hW hWQ
  have hNB : normalizer (footeF L t : Set G) ≤ normalizer (M₁ : Set G) :=
    normalizer_le_of_isSylowOf hQ (hBM.trans le_normalizer) hNQ
  exact ⟨(le_normalizer_of_mem_footeFamilyOf h.huniq hBmax.1 hBF).trans hNB, hBM⟩

end CFSG.ComponentClassification.FooteLit
