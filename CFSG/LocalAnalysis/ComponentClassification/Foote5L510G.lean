module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L510F
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L510D

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem exists_fourgroup_Q : ∃ Q₀ : Subgroup G, Q₀ ≤ Q ∧ (∀ q ∈ Q₀, q * q = 1) ∧
    Nat.card Q₀ = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEQ, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := 2) (H := Q) (k := 2) (by rw [h.open_pRank_Q])
  exact ⟨E, hEQ, fun q hq => by rw [← sq]; exact hE.2 q hq, by rw [hEc]; norm_num⟩

include ε in
theorem R_le_jeSub5
    (h𝕊 : FooteSimpleType 𝕊) (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {M : ℕ} (hM : M = 16 ∨ M = 32)
    (hmem : M = 32 → ∃ E : Subgroup G, E ≤ S ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = M) :
    S ⊓ L ≤ jeSub5 S M := by
  have hQR : ∀ X : Subgroup G, X ≤ Q → X ⊓ (S ⊓ L) = ⊥ := fun X hXQ => by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ Q ⊓ L := mem_inf.mpr ⟨hXQ (mem_inf.mp hx).1, (mem_inf.mp (mem_inf.mp hx).2).2⟩
    rwa [h.Q_inf_L] at h1
  refine h.R_le_of_involutions fun r hr hr2 => ?_
  rcases hM with rfl | rfl
  · obtain ⟨Q₀, hQ₀Q, hQ₀sq, hQ₀4⟩ := h.exists_fourgroup_Q
    exact h.mem_jeSub5_of_ext hna (hQ₀Q.trans h.QS) hQ₀sq (hQR Q₀ hQ₀Q)
      (fun x hx r hr => h.commute_Q_R (hQ₀Q hx) hr) (by rw [hQ₀4]) hr hr2
  · obtain ⟨E, hES, hEsq, hE32⟩ := hmem rfl
    obtain ⟨e', he'S, he'2, he'inn, he'R, he'Q⟩ :=
      h.exists_field_centralizer_R ε h𝕊 hD hES hEsq hE32
    have hEN : E ≤ normalizer (L : Set G) := hES.trans h.S_le
    have h1 := card_eq_card_inf_mul_card_actImage ε hEN
    have hEC : E ⊓ coreActionKernel L = E ⊓ Q := by
      rw [← h.inf_coreActionKernel, ← inf_assoc, inf_of_le_left hES]
    rw [hEC, hE32] at h1
    have h2 := h.card_le_four_of_le_Q (E := E ⊓ Q) inf_le_right
      (fun e he => hEsq e (mem_inf.mp he).1)
    have h3 := AutL2Facts.footeAutRankThree 𝕊 h𝕊 (actImage L ε E) (by
      intro α hα
      obtain ⟨e, he, rfl⟩ := (mem_actImage ε hEN).mp hα
      rw [← actG_mul ε (hEN he) (hEN he), hEsq e he, actG_one])
    have hEQ4 : Nat.card ↥(E ⊓ Q) = 4 := by
      by_contra hne
      have h4 : Nat.card ↥(E ⊓ Q) ≤ 3 := by omega
      have h5 : Nat.card ↥(E ⊓ Q) * Nat.card (actImage L ε E) ≤ 3 * 8 := Nat.mul_le_mul h4 h3
      omega
    have he'1 : e' ≠ 1 := fun h4 => he'inn (by rw [h4, actG_one]; exact one_mem _)
    have he'o : orderOf e' = 2 := orderOf_eq_prime (by rw [sq]; exact he'2) he'1
    have hinnQR : ∀ q ∈ Q, actG L ε q ∈ innAut5 𝕊 := fun q hq => by
      rw [(h.actG_eq_one_iff_mem_Q ε (h.QS hq)).mpr hq]
      exact one_mem _
    have hcz : ∀ q ∈ E ⊓ Q, ∀ y ∈ zpowers e', q * y = y * q := by
      intro q hq y hy
      rcases eq_one_or_eq_of_mem_zpowers_sq he'2 hy with rfl | rfl
      · rw [mul_one, one_mul]
      · exact (he'Q q hq).symm
    have hdisj : E ⊓ Q ⊓ zpowers e' = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rcases eq_one_or_eq_of_mem_zpowers_sq he'2 (mem_inf.mp hy).2 with rfl | rfl
      · exact one_mem _
      · exact absurd (hinnQR y (mem_inf.mp (mem_inf.mp hy).1).2) he'inn
    have hXcard : Nat.card ↥(E ⊓ Q ⊔ zpowers e') = 8 := by
      rw [card_sup_eq_mul_of_disjoint_of_le_normalizer (E ⊓ Q) (zpowers e')
        (le_normalizer_of_commute hcz) (disjoint_iff.mpr hdisj), hEQ4, Nat.card_zpowers, he'o]
    have hXS : E ⊓ Q ⊔ zpowers e' ≤ S := sup_le (inf_le_left.trans hES) (zpowers_le.mpr he'S)
    have hXsq : ∀ x ∈ E ⊓ Q ⊔ zpowers e', x * x = 1 :=
      fun x hx => sq_eq_one_of_mem_sup (fun e he => hEsq e (mem_inf.mp he).1)
        (fun y hy => by
          rcases eq_one_or_eq_of_mem_zpowers_sq he'2 hy with rfl | rfl
          · exact one_mul 1
          · exact he'2) hcz hx
    have hXc : ∀ x ∈ E ⊓ Q ⊔ zpowers e', ∀ r ∈ S ⊓ L, x * r = r * x := by
      intro x hx r hr
      obtain ⟨q, hq, y, hy, rfl⟩ := exists_mul_of_mem_sup_commute hcz hx
      have hyr : y * r = r * y := by
        rcases eq_one_or_eq_of_mem_zpowers_sq he'2 hy with rfl | rfl
        · rw [mul_one, one_mul]
        · exact he'R r hr
      rw [mul_assoc, hyr, ← mul_assoc, h.commute_Q_R (mem_inf.mp hq).2 hr, mul_assoc]
    have hXR : (E ⊓ Q ⊔ zpowers e') ⊓ (S ⊓ L) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨q, hq, y, hy, hqy⟩ := exists_mul_of_mem_sup_commute hcz (mem_inf.mp hx).1
      rcases eq_one_or_eq_of_mem_zpowers_sq he'2 hy with hy1 | hye
      · rw [hy1, mul_one] at hqy
        have h4 : q ∈ Q ⊓ L := mem_inf.mpr ⟨(mem_inf.mp hq).2,
          (mem_inf.mp (hqy ▸ (mem_inf.mp hx).2 : q ∈ S ⊓ L)).2⟩
        rw [h.Q_inf_L, mem_bot] at h4
        rw [mem_bot, hqy, h4]
      · exfalso
        rw [hye] at hqy
        have hxR := (mem_inf.mp hx).2
        have hxinn : actG L ε x ∈ innAut5 𝕊 := by
          rw [actG_of_mem_self ε (mem_inf.mp hxR).2]
          exact ⟨_, rfl⟩
        apply he'inn
        have h4 : actG L ε e' = (actG L ε q)⁻¹ * actG L ε x := by
          rw [hqy, actG_mul ε (h.S_le (h.QS (mem_inf.mp hq).2)) (h.S_le he'S)]
          group
        rw [h4]
        exact mul_mem (inv_mem (hinnQR q (mem_inf.mp hq).2)) hxinn
    exact h.mem_jeSub5_of_ext hna hXS hXsq hXR hXc (by rw [hXcard]) hr hr2

include ε in
theorem card_T_of_lemmas
    (h𝕊 : FooteSimpleType 𝕊) (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hQ : 4 < Nat.card Q)
    (hCt : ∀ y ∈ T, y * t = t * y → y ∈ S) (hST : S < T) : Nat.card T = 2 * Nat.card S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := h.sylT.isPGroup
  set S₁ := T ⊓ normalizer (S : Set G) with hS₁
  have hS₁le := h.card_normalizer_le_of_R_le ε hD hna hQ hCt (H := S) inf_le_left le_rfl
  have hSS₁ : S ≤ S₁ := le_inf h.ST le_normalizer
  obtain ⟨u, huT, huS, huN⟩ := exists_mem_normalizer_not_mem_of_lt hT hST
  have hS₁ge : 2 * Nat.card S ≤ Nat.card S₁ := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hSS₁
    have hlt : Nat.card S < Nat.card S₁ := by
      refine lt_of_le_of_ne (card_le_of_le hSS₁) fun h1 => huS ?_
      have h2 := eq_of_le_of_card_ge hSS₁ h1.ge
      rw [h2]
      exact mem_inf.mpr ⟨huT, huN⟩
    rcases k with _ | _ | k
    · simp at hk
      exact absurd hk (Nat.card_pos (α := S₁)).ne'
    · omega
    · rw [hk]
      nlinarith
  have hcard₁ : Nat.card S₁ = 2 * Nat.card S := le_antisymm hS₁le hS₁ge
  by_contra hne
  have hS₁T : S₁ < T := by
    refine lt_of_le_of_ne inf_le_left fun h1 => hne ?_
    rw [← h1, hcard₁]
  obtain ⟨x, hxT, hxS₁, hxN, -⟩ := exists_mem_normalizer_sq_mem hT hS₁T
  set M := if ∃ E : Subgroup G, E ≤ S ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 32 then 32 else 16
    with hMdef
  have hM : M = 16 ∨ M = 32 := by
    rw [hMdef]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hmem : M = 32 → ∃ E : Subgroup G, E ≤ S ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = M := by
    intro hM32
    rw [hMdef] at hM32 ⊢
    split_ifs at hM32 ⊢ with h1
    · exact h1
    · omega
  have hmax : ∀ E : Subgroup G, E ≤ S → (∀ e ∈ E, e * e = 1) → Nat.card E ≤ M := by
    intro E hES hEsq
    have h1 := h.card_le_thirtytwo ε h𝕊 hES hEsq
    rw [hMdef]
    split_ifs with h2
    · exact h1
    · push Not at h2
      have h3 := h2 E hES hEsq
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (h.isPGroup_S.to_le hES)
      rw [hk] at h1 h3 ⊢
      have hk5 : k ≤ 5 := by
        by_contra hk5
        push Not at hk5
        have h4 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk5
        omega
      interval_cases k <;> simp only [Nat.reducePow] at h1 h3 ⊢ <;> omega
  set J := jeSub5 S M with hJ
  have hRJ : S ⊓ L ≤ J := h.R_le_jeSub5 ε h𝕊 hD hna hM hmem
  have hJS : J ≤ S := jeSub5_le S M
  have hS₁J : S₁ ≤ normalizer (J : Set G) := fun y hy =>
    mem_normalizer_jeSub5 fun E hES _ _ e he =>
      (mem_normalizer_iff.mp (mem_inf.mp hy).2 e).mp (hES he)
  have hxJ : x ∈ normalizer (J : Set G) :=
    mem_normalizer_jeSub5 fun E hES hEsq hEM =>
      h.conj_mem_S_of_max ε h𝕊 hna hCt hM hmax hSS₁ inf_le_left inf_le_right hcard₁
        (fun y hy => (mem_normalizer_iff.mp hxN y).mp (hSS₁ hy)) hES hEsq hEM
  have hle : S₁ ⊔ zpowers x ≤ T ⊓ normalizer (J : Set G) :=
    sup_le (le_inf inf_le_left hS₁J) (zpowers_le.mpr (mem_inf.mpr ⟨hxT, hxJ⟩))
  have h1 : Nat.card ↥(T ⊓ normalizer (J : Set G)) ≤ 2 * Nat.card S :=
    h.card_normalizer_le_of_R_le ε hD hna hQ hCt hRJ hJS
  have hlt : Nat.card S₁ < Nat.card ↥(S₁ ⊔ zpowers x) := by
    refine lt_of_le_of_ne (card_le_of_le le_sup_left) fun h2 => hxS₁ ?_
    have h3 := eq_of_le_of_card_ge (le_sup_left : S₁ ≤ S₁ ⊔ zpowers x) h2.ge
    rw [h3]
    exact mem_sup_right (mem_zpowers x)
  have h2 := card_le_of_le hle
  omega

theorem card_T_eq_two_mul
    (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups) (hB4 : GoldschmidtCorB4)
    (hAut : Foote5AutStructure) (hMW : MacWilliamsStatement)
    (hFC : Foote5FieldCentralizer) : Nat.card T = 2 * Nat.card S := by
  obtain ⟨Lin, hD⟩ := h.exists_autData hAut
  obtain ⟨ε⟩ := h.quotient_simple.2
  have hST := h.not_isSylowOf_top hGH hKG hB4 hAut
  have hSlt : S < T := lt_of_le_of_ne h.ST fun h1 => hST (by rw [h1]; exact h.sylT)
  exact h.card_T_of_lemmas ε h.sec4.footeFamilyType hD
    (h.nonabelian_R_of_not_sylow hGH hKG hAut hMW hST)
    (h.four_lt_card_Q hGH hKG hB4 hAut hMW hFC)
    (fun y hyT hyt => h.mem_S_of_commute_t_of_inputs hGH hKG hB4 hAut hMW hFC hyT hyt) hSlt

end Sec5

end CFSG.ComponentClassification.Foote5
