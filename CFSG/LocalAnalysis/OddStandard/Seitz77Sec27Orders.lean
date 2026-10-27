module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27OrdersArith
public import CFSG.LocalAnalysis.ComponentClassification.UFrontierCoreBranches
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Milestones.LR_rank_two_isomorphism_types
public import CFSG.Walter.TwoRank
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.Ly

public section

namespace CFSG.OddStandard.Seitz77

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

@[expose] def Survivors27 (S : Type) [Group S] : Prop :=
  (∃ n : ℕ, 7 ≤ n ∧ n ≤ 10 ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel S .PSL 2 p f) ∨
  LieModel S .PSL 2 2 3 ∨ LieModel S .PSL 2 2 4 ∨ LieModel S .PSL 3 2 2 ∨
  LieModel S .PSU 3 3 1 ∨ LieModel S .PSp 2 3 1 ∨ NativeSporadic.IsSporadic S .J2

private theorem admissible_of_lieModel' {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel X t n p f) : StatedLieAdmissible t n p f :=
  CFSG.Blueprint.LieModel.admissible h

private theorem two_pow_mod_four {f : ℕ} (hf : 1 ≤ f) : 2 ^ f % 4 = 2 ∨ 2 ^ f % 4 = 0 := by
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    left; norm_num
  · right
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add]
    simp

private theorem false_of_card_eq {S : Type} [Group S] [Finite S]
    (hdvd : Nat.card S ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127) {m q : ℕ}
    (hm : Nat.card S = m) (hq : q ∣ m)
    (hnq : ¬ q ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127) : False :=
  hnq (hq.trans (hm ▸ hdvd))

private theorem sylowExp_PSp2 : lieSylowExponent .PSp 2 = 4 := by decide

private theorem sylowExp_PSL3 : lieSylowExponent .PSL 3 = 3 := by decide

private theorem sylowExp_PSU3 : lieSylowExponent .PSU 3 = 3 := by decide

private theorem sylowExp_PSL4 : lieSylowExponent .PSL 4 = 6 := by decide

private theorem sylowExp_PSU4 : lieSylowExponent .PSU 4 = 6 := by decide

private theorem sylowExp_PSL5 : lieSylowExponent .PSL 5 = 10 := by decide

private theorem sylowExp_PSU5 : lieSylowExponent .PSU 5 = 10 := by decide

section LieOrder


theorem lie_exponent_le {S : Type} [Group S] [Finite S]
    (hdvd : Nat.card S ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127)
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel S t n p f) :
    lieSylowExponent t n * f ≤
      (2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 : ℕ).factorization p := by
  obtain ⟨-, -, hv⟩ := lieOrderFormulasInput S t n p f (admissible_of_lieModel' h) h
  have := factorization_le_GL8 Nat.card_pos.ne' hdvd p
  rwa [hv] at this

theorem lie_card_mul {S : Type} [Group S]
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel S t n p f) :
    Nat.card S * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) :=
  (lieOrderFormulasInput S t n p f (admissible_of_lieModel' h) h).2.1

end LieOrder

section M23


private theorem card_M23' : Nat.card NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans CFSG.M23.M23Group.card_M23

end M23

section Sporadic


theorem sporadic_false {S : Type} [Group S] [Finite S]
    (hdvd : Nat.card S ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127)
    (h : NativeSporadic.IsSporadic S .M12 ∨ NativeSporadic.IsSporadic S .M22 ∨
      NativeSporadic.IsSporadic S .M23 ∨ NativeSporadic.IsSporadic S .J1 ∨
      NativeSporadic.IsSporadic S .J3 ∨ NativeSporadic.IsSporadic S .McL ∨
      NativeSporadic.IsSporadic S .Ly) : False := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact false_of_card_eq hdvd ((Nat.card_congr e.toEquiv).trans
      (CFSG.Sporadic.Mathieu.card_M12 : Nat.card (NativeSporadic.Carrier .M12) = 95040))
      (by norm_num : 11 ∣ 95040) not_dvd_GL8_eleven
  · exact false_of_card_eq hdvd ((Nat.card_congr e.toEquiv).trans
      (CFSG.Sporadic.Mathieu.card_M22 : Nat.card (NativeSporadic.Carrier .M22) = 443520))
      (by norm_num : 11 ∣ 443520) not_dvd_GL8_eleven
  · exact false_of_card_eq hdvd ((Nat.card_congr e.toEquiv).trans
      (card_M23' : Nat.card (NativeSporadic.Carrier .M23) = 10200960))
      (by norm_num : 11 ∣ 10200960) not_dvd_GL8_eleven
  · exact false_of_card_eq hdvd ((Nat.card_congr e.toEquiv).trans
      (CFSG.Sporadic.J1.card_J1 : Nat.card (NativeSporadic.Carrier .J1) = 175560))
      (by norm_num : 11 ∣ 175560) not_dvd_GL8_eleven
  · exact false_of_card_eq hdvd ((Nat.card_congr e.toEquiv).trans
      (CFSG.Sporadic.J3.card_J3 : Nat.card (NativeSporadic.Carrier .J3) = 50232960))
      (by norm_num : 19 ∣ 50232960) not_dvd_GL8_nineteen
  · exact false_of_card_eq hdvd ((Nat.card_congr e.toEquiv).trans
      (CFSG.Sporadic.McL.card_McL : Nat.card (NativeSporadic.Carrier .McL) = 898128000))
      (by norm_num : 11 ∣ 898128000) not_dvd_GL8_eleven
  · exact false_of_card_eq hdvd ((Nat.card_congr e.toEquiv).trans
      (CFSG.Sporadic.Ly.card_Ly : Nat.card (NativeSporadic.Carrier .Ly) = 51765179004000000))
      (by norm_num : 11 ∣ 51765179004000000) not_dvd_GL8_eleven

end Sporadic

section Main


theorem survivors27 (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hgen : ∀ P : Subgroup S, IsPGroup 2 P →
      ∃ s : Finset S, s.card ≤ 4 ∧ Subgroup.closure (s : Set S) = P)
    (hdvd : Nat.card S ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127) : Survivors27 S := by
  have heven := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnonab).1
  have h2 : 2 ≤ CFSG.Open.twoRank S := CFSG.Walter.two_le_twoRank S hnonab heven
  unfold Survivors27
  by_cases h3 : 3 ≤ CFSG.Open.twoRank S
  · rcases hGH S hnonab h3 hgen with
      ⟨p, f, hp, hp2, hf, hG⟩ | ⟨p, f, hp, hp2, hf, hPSp⟩ | ⟨f, htG2⟩ |
      ⟨p, f, hp, hp2, hf, -, hL4⟩ | ⟨p, f, hp, hp2, hf, -, hU4⟩ | ⟨p, f, hp, hf, hmod, hL5⟩ |
      ⟨p, f, hp, hf, hmod, hU5⟩ | hmid | ⟨n, hn8, hn11, ⟨e⟩⟩ | hspor
    ·
      exfalso
      have h5 := factorization_GL8_le_five hp hp2
      rcases hG with hG | hG
      · have := lie_exponent_le hdvd hG
        simp only [lieSylowExponent] at this
        omega
      · have := lie_exponent_le hdvd hG
        simp only [lieSylowExponent] at this
        omega
    ·
      have := lie_exponent_le hdvd hPSp
      rw [sylowExp_PSp2] at this
      obtain ⟨rfl, rfl⟩ := eq_three_of_four_mul_le hp hp2 hf this
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hPSp))))))
    ·
      exfalso
      have hadm := admissible_of_lieModel' htG2
      have := lie_exponent_le hdvd htG2
      simp only [lieSylowExponent] at this
      rw [factorization_GL8_three] at this
      have h3f : 3 ≤ f := hadm.2.2.2.2.2
      omega
    ·
      exfalso
      have h5 := factorization_GL8_le_five hp hp2
      have := lie_exponent_le hdvd hL4
      rw [sylowExp_PSL4] at this
      omega
    ·
      exfalso
      have h5 := factorization_GL8_le_five hp hp2
      have := lie_exponent_le hdvd hU4
      rw [sylowExp_PSU4] at this
      omega
    ·
      exfalso
      have hp2 : p ≠ 2 := by
        rintro rfl
        rcases two_pow_mod_four hf with h | h <;> omega
      have h5 := factorization_GL8_le_five hp hp2
      have := lie_exponent_le hdvd hL5
      rw [sylowExp_PSL5] at this
      omega
    ·
      exfalso
      have hp2 : p ≠ 2 := by
        rintro rfl
        rcases two_pow_mod_four hf with h | h <;> omega
      have h5 := factorization_GL8_le_five hp hp2
      have := lie_exponent_le hdvd hU5
      rw [sylowExp_PSU5] at this
      omega
    · rcases hmid with hL28 | hL216 | hL34 | hSz
      · exact Or.inr (Or.inr (Or.inl hL28))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hL216)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL34))))
      ·
        exfalso
        have h := lie_card_mul hSz
        simp only [lieOrderDivisor, lieOrderNumerator, mul_one] at h
        exact false_of_card_eq hdvd (h.trans (by norm_num)) (by norm_num : 13 ∣ 29120)
          not_dvd_GL8_thirteen
    ·
      by_cases hn : n ≤ 10
      · exact Or.inl ⟨n, by omega, hn, ⟨e⟩⟩
      · exfalso
        obtain rfl : n = 11 := by omega
        have h2' := two_mul_nat_card_alternatingGroup (α := Fin 11)
        simp only [Nat.card_perm, Nat.card_fin] at h2'
        have h11 : 11 ∣ Nat.card S := by
          have hc : Nat.card S = Nat.card (alternatingGroup (Fin 11)) := Nat.card_congr e.toEquiv
          have h11' : 11 ∣ 2 * Nat.card (alternatingGroup (Fin 11)) := by
            rw [h2']; exact ⟨3628800, by decide⟩
          rw [hc]
          exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h11')
        exact not_dvd_GL8_eleven (h11.trans hdvd)
    ·
      rcases hspor with h | h | h | h | h | h | h | h
      · exact (sporadic_false hdvd (Or.inl h)).elim
      · exact (sporadic_false hdvd (Or.inr (Or.inl h))).elim
      · exact (sporadic_false hdvd (Or.inr (Or.inr (Or.inl h)))).elim
      · exact (sporadic_false hdvd (Or.inr (Or.inr (Or.inr (Or.inl h))))).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
      · exact (sporadic_false hdvd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).elim
      · exact (sporadic_false hdvd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).elim
      · exact (sporadic_false hdvd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))).elim
  · have hrank : CFSG.Open.twoRank S = 2 := by omega
    rcases CFSG.Milestones.lr_rank_two_isomorphism_types S hnonab hrank with
      ⟨p, f, hp, hp2, hf, hL2⟩ | ⟨p, f, hp, hp2, hf, hL3⟩ | ⟨p, f, hp, hp2, hf, hU3⟩ | hU34 |
      ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, Or.inl ⟨by decide, hL2⟩⟩)
    ·
      exfalso
      have hL3' : LieModel S .PSL 3 p f := Or.inl ⟨by decide, hL3⟩
      have := lie_exponent_le hdvd hL3'
      rw [sylowExp_PSL3] at this
      obtain ⟨rfl, rfl⟩ := eq_three_of_three_mul_le hp hp2 hf this
      have h := lie_card_mul hL3'
      simp only [lieOrderDivisor, lieOrderNumerator] at h
      norm_num [Finset.prod_Icc_succ_top] at h
      exact false_of_card_eq hdvd h (by norm_num : 13 ∣ 5616) not_dvd_GL8_thirteen
    ·
      have hU3' : LieModel S .PSU 3 p f := Or.inl ⟨by decide, hU3⟩
      have := lie_exponent_le hdvd hU3'
      rw [sylowExp_PSU3] at this
      obtain ⟨rfl, rfl⟩ := eq_three_of_three_mul_le hp hp2 hf this
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hU3')))))
    ·
      exfalso
      have hU34' : LieModel S .PSU 3 2 2 := Or.inl ⟨by decide, hU34⟩
      have h := lie_card_mul hU34'
      simp only [lieOrderDivisor, lieOrderNumerator] at h
      norm_num [Finset.prod_Icc_succ_top] at h
      exact false_of_card_eq hdvd h (by norm_num : 13 ∣ 62400) not_dvd_GL8_thirteen
    · exact Or.inl ⟨7, le_rfl, by norm_num, ⟨e⟩⟩
    ·
      exfalso
      have hc : Nat.card S = 7920 :=
        (Nat.card_congr e.toEquiv).trans CFSG.Semidihedral.GL2Recognition.card_lowTwoRankStatedM11
      exact false_of_card_eq hdvd hc (by norm_num : 11 ∣ 7920) not_dvd_GL8_eleven

end Main

end CFSG.OddStandard.Seitz77
