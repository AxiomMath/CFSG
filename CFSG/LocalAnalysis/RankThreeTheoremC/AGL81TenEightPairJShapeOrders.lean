module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightPairJShapeU42
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1L3Classical
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Open
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

@[expose] def IsPairJOrder (n : ℕ) : Prop :=
  n = 25920 ∨ n = 5515776 ∨ n = 504 ∨ n = 5616 ∨ n = 60 ∨ n = 126000 ∨ n = 1876896 ∨
    n = 4030387200

section Arithmetic

theorem pairJ_factorial_div_two_ne {n N : ℕ} (hn : IsPairJOrder n) (hN : 6 ≤ N) :
    N.factorial / 2 ≠ n := by
  intro h
  have hle : n ≤ 4030387200 := by
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hN14 : N < 14 := by
    by_contra hc
    push_neg at hc
    have h1 : Nat.factorial 14 ≤ Nat.factorial N := Nat.factorial_le hc
    have h2 : Nat.factorial 14 = 87178291200 := by norm_num [Nat.factorial]
    omega
  interval_cases N <;> norm_num [Nat.factorial] at h <;> unfold IsPairJOrder at hn <;> omega

theorem pairJ_not_two_pow_twelve_dvd {n : ℕ} (hn : IsPairJOrder n) : ¬ 2 ^ 12 ∣ n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem pairJ_not_charTwoShape {n : ℕ} (hn : n = 5616 ∨ n = 126000 ∨ n = 1876896 ∨ n = 4030387200)
    {v M : ℕ} (h : n = 2 ^ v * M) (hM : M < 2 ^ (2 * v)) : False := by
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · subst h0
      rcases hn with rfl | rfl | rfl | rfl <;> simp at h
    · exact h0
  have hv : v < 32 := by
    by_contra hc
    push_neg at hc
    have h1 : 2 ^ 32 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hc
    have h2 : 2 ^ v ≤ n := by rw [h]; exact Nat.le_mul_of_pos_right _ hM0
    rcases hn with rfl | rfl | rfl | rfl <;> omega
  interval_cases v <;> omega

theorem pairJ_two_pow_twelve_dvd_orderD {m : ℕ} (hm : 4 ≤ m) : 2 ^ 12 ∣ orderD m 2 := by
  have hodd : Odd (2 ^ m - 1) := by
    have hqn : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by omega)
    obtain ⟨k, hk⟩ := hqn
    exact ⟨k - 1, by omega⟩
  have hg : Nat.gcd 4 (2 ^ m - 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd) |>.symm.symm
  unfold orderD
  rw [hg, Nat.div_one]
  have h12 : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
  have : 2 ^ 12 ∣ 2 ^ (m * (m - 1)) := pow_dvd_pow 2 (by omega)
  exact (this.trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _)

theorem pairJ_two_pow_twelve_dvd_orderTwistedD {m : ℕ} (hm : 4 ≤ m) :
    2 ^ 12 ∣ orderTwistedD m 2 := by
  have hodd : Odd (2 ^ m + 1) := by
    have h2 : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
    exact h2.add_one
  have hg : Nat.gcd 4 (2 ^ m + 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd) |>.symm.symm
  unfold orderTwistedD
  rw [hg, Nat.div_one]
  have h12 : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
  have : 2 ^ 12 ∣ 2 ^ (m * (m - 1)) := pow_dvd_pow 2 (by omega)
  exact (this.trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _)

theorem pairJ_lieOrderFormula_small_eq {d : TauCeti.ValidLieTypeIndex}
    (h : (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) :
    lieOrderFormula d.1 = 168 ∨ lieOrderFormula d.1 = 6048 := by
  rcases h with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
  · left
    rw [hd]
    simp only [lieOrderFormula, hq]
    norm_num [orderA]
  · right
    rw [hd]
    simp only [lieOrderFormula, hq]
    norm_num [orderTwistedA, Finset.prod_Icc_succ_top]

end Arithmetic

section Clauses

theorem pairJ_not_isClassicalTwoOrG2_of_card (hB : LieOrderBridgeHyp) (hC : LieCharPartHyp)
    {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : Nat.card Y = n)
    (hn : n = 5616 ∨ n = 126000 ∨ n = 1876896 ∨ n = 4030387200) : ¬ IsClassicalTwoOrG2 Y := by
  rintro (⟨d, hd, ⟨e⟩⟩ | ⟨N, hN, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩)
  · have hord : Nat.card Y = lieOrderFormula d.1 := hB d Y ⟨e⟩
    obtain ⟨v, M, hv, hM⟩ := hC d.1 d.2
    rw [characteristic_eq_two_of_classicalOrG2 hd] at hv hM
    exact pairJ_not_charTwoShape hn (v := v) (M := M) (by rw [← hY, hord, hv]) hM
  · have hcard := card_alt_fin_small hN
    rw [← Nat.card_congr e.toEquiv, hY] at hcard
    omega
  · have h := pairJ_lieOrderFormula_small_eq hd
    rw [← hB d Y ⟨e⟩, hY] at h
    clear hd
    omega

theorem pairJ_orthogonal_clause
    (hB : LieOrderBridgeHyp) {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : IsPairJOrder n)
    (hY : Nat.card Y = n) (hO : IsOrthogonalTwo Y) :
    Nonempty (Y ≃* alternatingGroup (Fin 5)) ∨ U42Facts Y := by
  have h12 := pairJ_not_two_pow_twelve_dvd hn
  rcases hO with ⟨⟨d, hv⟩, ⟨m, q, hq, hdm⟩, ⟨e⟩⟩ | ⟨N, hN, ⟨e⟩⟩
  · have hcard : Nat.card Y = lieOrderFormula d := hB ⟨d, hv⟩ Y ⟨e⟩
    have hq2 : q.p = 2 ∧ q.exponent = 1 :=
      (Nat.Prime.pow_eq_iff Nat.prime_two).1 (by rw [← TauCeti.PrimePower.card_def]; exact hq)
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff d).1
      ((TauCeti.LieTypeIndex.valid_iff d).1 hv).1
    rcases hdm with rfl | rfl | ⟨rfl, rfl⟩
    · exfalso
      have hdvd := pairJ_two_pow_twelve_dvd_orderD (m := m) hrange
      simp only [lieOrderFormula, hq] at hcard
      rw [← hY, hcard] at h12
      exact h12 hdvd
    · exfalso
      have hdvd := pairJ_two_pow_twelve_dvd_orderTwistedD (m := m) hrange
      simp only [lieOrderFormula, hq] at hcard
      rw [← hY, hcard] at h12
      exact h12 hdvd
    · right
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
      rw [hq2.1, hq2.2] at h
      exact u42Facts_of_model_psu_four_two h
  · rcases hN with rfl | rfl | rfl
    · exact Or.inl ⟨e⟩
    · exfalso
      have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup]
        simp [Nat.factorial]
      rw [← Nat.card_congr e.toEquiv, hY] at hcard
      unfold IsPairJOrder at hn
      omega
    · exfalso
      have hcard : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
        rw [nat_card_alternatingGroup]
        simp [Nat.factorial]
      rw [← Nat.card_congr e.toEquiv, hY] at hcard
      unfold IsPairJOrder at hn
      omega

theorem pairJ_clauses
    (hB : LieOrderBridgeHyp) {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : IsPairJOrder n)
    (hY : Nat.card Y = n) (hs : IsSimpleGroup Y)
    (h4 : IsClassicalTwoOrG2 Y → ∀ T J : Subgroup Y, IsSylowTwoOf T ⊤ →
      Subgroup.normalizer (T : Set Y) ≤ J → J ≠ Subgroup.normalizer (T : Set Y) → J ≠ ⊤ →
        U42Facts Y) :
    (IsSimpleGroup Y ∧ ∃ a b : Y, a * b ≠ b * a) ∧
    (∀ N : ℕ, 6 ≤ N → IsEmpty (Y ≃* alternatingGroup (Fin N))) ∧
    (IsOrthogonalTwo Y → Nonempty (Y ≃* alternatingGroup (Fin 5)) ∨ U42Facts Y) ∧
    (IsClassicalTwoOrG2 Y → ∀ T J : Subgroup Y, IsSylowTwoOf T ⊤ →
      Subgroup.normalizer (T : Set Y) ≤ J → J ≠ Subgroup.normalizer (T : Set Y) → J ≠ ⊤ →
        U42Facts Y) := by
  refine ⟨⟨hs, ?_⟩, ?_, pairJ_orthogonal_clause hB hn hY, h4⟩
  · by_contra hc
    push_neg at hc
    letI : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hc }
    have hp : (Nat.card Y).Prime := IsSimpleGroup.prime_card
    rw [hY] at hp
    unfold IsPairJOrder at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hp
  · intro N hN
    refine ⟨fun e => ?_⟩
    haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.2 (by omega)
    have h1 := Nat.card_congr e.toEquiv
    have h2 : Nat.card (alternatingGroup (Fin N)) = N.factorial / 2 := by
      rw [nat_card_alternatingGroup]
      simp
    rw [h2, hY] at h1
    exact pairJ_factorial_div_two_ne hn hN h1.symm

end Clauses

end CFSG.LocalAnalysis.RankThreeTheoremC.TenEight
