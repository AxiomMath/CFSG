module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def FooteInCC (M : Subgroup G) (t : G) : Prop :=
  orderOf t = 2 ∧ t ∈ coreActionKernel M ∧ ¬ centralizer ({t} : Set G) ≤ normalizer (M : Set G)

theorem inf_centralizer_le_footeB (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    {M : Subgroup G} (hM : IsFooteM L M) {t : G} (ht : orderOf t = 2)
    (htC : t ∈ coreActionKernel M) :
    coreActionKernel M ⊓ centralizer ({t} : Set G) ≤ footeB L t := by
  obtain ⟨-, -, hBmax, hBF⟩ := foote_lemma_4_5_i h hM ht htC
  have hBN : centralizer ({t} : Set G) ≤ normalizer (footeF L t : Set G) :=
    le_normalizer_of_mem_footeFamilyOf h.huniq hBmax.1 hBF
  obtain ⟨F, hF, hF2, hF8⟩ := exists_card_eight_of_le_pRank (h47 G L h M hM t ht htC)
  obtain ⟨hBM, -⟩ := footeF_le_of_card_eight h hM ht htC hF2 hF8 hF
  intro x hx
  exact mem_inf.mpr ⟨(mem_inf.mp hx).2,
    mem_coreActionKernel_of_le hBM (hBN (mem_inf.mp hx).2) (mem_inf.mp hx).1⟩

theorem foote_lemma_4_11 (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M)
    (hH : ∀ t : G, FooteInCC M t → ∀ u ∈ footeK L t, FooteInCC M u → u = t)
    {U : Subgroup G} (hUC : U ≤ coreActionKernel M) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hU4 : 4 ≤ Nat.card U) :
    ∃ v ∈ U, v ≠ 1 ∧ centralizer ({v} : Set G) ≤ normalizer (M : Set G) := by
  by_contra hcon
  push Not at hcon
  have hCC : ∀ v ∈ U, v ≠ 1 → FooteInCC M v := fun v hv hv1 =>
    ⟨orderOf_eq_prime (hU2 v hv) hv1, hUC hv, hcon v hv hv1⟩
  obtain ⟨W, hW, hWU⟩ := exists_isKleinFour_le hU2 hU4
  obtain ⟨t, htW, ht1, -⟩ := exists_ne_of_isKleinFour hW 1
  have htU := hWU htW
  obtain ⟨ht, htC, hCt⟩ := hCC t htU ht1
  obtain ⟨hKB, -, -, -, htype, hinv⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM ht htC hCt
  have ht2 : t ^ 2 = 1 := hU2 t htU
  have hUB : U ≤ footeB L t := fun u hu => inf_centralizer_le_footeB h h47 hM ht htC
    ⟨hUC hu, mem_centralizer_singleton_iff.mpr (commute_of_sq_eq_one hU2 hu htU)⟩
  have hsub : ∀ u ∈ U, u = 1 ∨ u = t := by
    intro u hu
    by_cases hu1 : u = 1
    · exact Or.inl hu1
    right
    have huK : u ∈ footeK L t ⊔ zpowers t :=
      hinv u (hUB hu) (orderOf_eq_prime (hU2 u hu) hu1)
    have hKt : footeK L t ≤ normalizer ((zpowers t : Subgroup G) : Set G) := by
      intro k hk
      have hkt : k * t = t * k :=
        mem_centralizer_singleton_iff.mp ((hKB.trans inf_le_left) hk)
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
        rw [show k * t ^ i * k⁻¹ = t ^ i by
          rw [(Commute.zpow_right hkt i).eq]; group]
        exact zpow_mem_zpowers t i
      · intro hx
        obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hx
        have hc : k * t ^ i = t ^ i * k := (Commute.zpow_right hkt i).eq
        have hx' : x = t ^ i := by
          calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
            _ = k⁻¹ * t ^ i * k := by rw [hi]
            _ = k⁻¹ * (t ^ i * k) := by group
            _ = k⁻¹ * (k * t ^ i) := by rw [hc]
            _ = t ^ i := by group
        rw [hx']
        exact zpow_mem_zpowers t i
    have hu' : u ∈ ((footeK L t ⊔ zpowers t : Subgroup G) : Set G) := huK
    rw [coe_mul_of_left_le_normalizer_right _ _ hKt] at hu'
    obtain ⟨k, hk, s, hs, rfl⟩ := Set.mem_mul.mp hu'
    have hs' : s = 1 ∨ s = t := by
      by_cases hs1 : s = 1
      · exact Or.inl hs1
      · exact Or.inr (eq_of_mem_zpowers_of_sq ht2 hs1 hs)
    have hkU : k ∈ U := by
      rcases hs' with hs1 | hs1
      · rw [hs1, mul_one] at hu
        exact hu
      · rw [hs1] at hu
        have : k = k * t * t := by rw [mul_assoc, ← sq, ht2, mul_one]
        rw [this]
        exact mul_mem hu htU
    have hk1 : k = 1 ∨ k = t := by
      by_cases hk1 : k = 1
      · exact Or.inl hk1
      · exact Or.inr (hH t ⟨ht, htC, hCt⟩ k hk (hCC k hkU hk1))
    rcases htype with ⟨-, htK⟩ | ⟨-, htK⟩
    ·
      have hk1' : k = 1 := hk1.resolve_right fun h1 => htK (h1 ▸ hk)
      rcases hs' with hs1 | hs1
      · exact absurd (by rw [hk1', hs1, mul_one]) hu1
      · rw [hk1', hs1, one_mul]
    ·
      have huK' : k * s ∈ footeK L t := by
        rcases hs' with hs1 | hs1
        · rw [hs1, mul_one]
          exact hk
        · rw [hs1]
          exact mul_mem hk htK
      exact hH t ⟨ht, htC, hCt⟩ (k * s) huK' (hCC _ hu hu1)
  have hsubset : (U : Set G) ⊆ {1, t} := fun u hu => by
    rcases hsub u hu with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hcard : Nat.card U ≤ 2 := by
    calc Nat.card U = Nat.card ↥(U : Set G) := rfl
      _ = (U : Set G).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, t} : Set G).ncard := Set.ncard_le_ncard hsubset (Set.toFinite _)
      _ ≤ ({t} : Set G).ncard + 1 := Set.ncard_insert_le 1 {t}
      _ = 2 := by rw [Set.ncard_singleton]
  omega

end CFSG.ComponentClassification.FooteLit
