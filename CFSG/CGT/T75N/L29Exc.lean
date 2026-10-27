module

public import CFSG.CGT.T75N.L29Std
public import CFSG.CGT.T75N.L29Chain
public import CFSG.CGT.T75N.L29SylowLift

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75

theorem factorization_two_pow_mul_odd (a b : ℕ) (hb : b % 2 = 1) :
    (2 ^ a * b).factorization 2 = a := by
  have hb0 : b ≠ 0 := by omega
  rw [Nat.factorization_mul (pow_ne_zero a (by norm_num)) hb0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by omega)]
  simp

theorem ker_eq_bot_of_std
    {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ} {k : ℕ} (hFk : Nat.card F = 2 ^ k)
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (e₀ : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL (m + 2) F))
    (π : Y →* SpecialLinearGroup (Fin (m + 2)) F) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center Y)
    (compat : ∀ y : Y, projectiveSpecialLinearGroupEquivStatedProj (m + 2) F
      (QuotientGroup.mk (π y)) = e₀ (QuotientGroup.mk y))
    {E : Subgroup Y} (hE : IsWC E) (hEZ : E ⊓ Subgroup.center Y = ⊥) (hE4 : 4 ≤ Nat.card E)
    (hcardstd : Nat.card (E.map (QuotientGroup.mk' (Subgroup.center Y))) = 2 ^ (k * (m + 1)))
    (hstd : (∃ c : Fin (m + 2) → F, c ≠ 0 ∧ (E.map (QuotientGroup.mk' (Subgroup.center Y))).map
        e₀.toMonoidHom = transvImage (m + 2) F (transvCenter (m + 2) F c)) ∨
      (∃ a : Fin (m + 2) → F, a ≠ 0 ∧ (E.map (QuotientGroup.mk' (Subgroup.center Y))).map
        e₀.toMonoidHom = transvImage (m + 2) F (transvAxis (m + 2) F a)))
    (hsyl : Nat.card F ^ (∑ j ∈ Finset.Ico 0 (m + 1), (m + 1 - j)) =
      2 ^ (Nat.card (SpecialLinearGroup (Fin (m + 2)) F)).factorization 2) :
    π.ker = ⊥ := by
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by
    have := hE.1.2 x hx
    simpa [pow_two] using this
  have hEK : E ⊓ π.ker = ⊥ := by
    rw [eq_bot_iff, ← hEZ]
    exact inf_le_inf_left E hcen
  have hE1 : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE4
    omega
  have hEcard : Nat.card E = Nat.card F ^ (m + 2 - 1) := by
    have hinj : Function.Injective ((QuotientGroup.mk' (Subgroup.center Y)).comp E.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxZ : (x : Y) ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff _).1 hx
      have : (x : Y) ∈ E ⊓ Subgroup.center Y := ⟨x.2, hxZ⟩
      rw [hEZ, Subgroup.mem_bot] at this
      exact Subtype.ext this
    have h2 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at h2
    rw [h2, hcardstd, hFk, ← pow_mul]
    have hn1 : m + 2 - 1 = m + 1 := by omega
    rw [hn1]
  have hstd' : (∃ c : Fin (m + 2) → F, c ≠ 0 ∧ (E.map (QuotientGroup.mk' (Subgroup.center Y))).map
        e₀.toMonoidHom = transvImage (m + 2) F (transvCenter (m + 2) F c)) ∨
      (∃ a : Fin (m + 2) → F, a ≠ 0 ∧ (E.map (QuotientGroup.mk' (Subgroup.center Y))).map
        e₀.toMonoidHom = transvImage (m + 2) F (transvAxis (m + 2) F a)) := hstd
  obtain ⟨π', hπ', hker', hEπ'⟩ := exists_std_surjection e₀ π hπ compat hE2 hEK hEcard hstd'
  have hcen' : π'.ker ≤ Subgroup.center Y := hker' ▸ hcen
  have hEK' : E ⊓ π'.ker = ⊥ := hker' ▸ hEK
  obtain ⟨H, hHK, -, -, hHcard⟩ := chain_exists π' hπ' hcen' hE hE1 hEπ' hEK' (m + 2 - 1) 0
    (by omega)
  have hn1 : m + 2 - 1 = m + 1 := by omega
  rw [hn1] at hHcard
  have := ker_eq_bot_of_sylow_lift (by omega : 2 ≤ m + 2) π' hπ' hcen' H hHK (hHcard.trans hsyl)
  rw [← hker']
  exact this

theorem card_SL_three_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card (SpecialLinearGroup (Fin (1 + 2)) F) = 168 := by
  have := Fintype.ofFinite F
  have hq : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [Matrix.card_SL_field (1 + 2), hq]
  simp [Fin.prod_univ_succ]

theorem card_SL_three_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card (SpecialLinearGroup (Fin (1 + 2)) F) = 60480 := by
  have := Fintype.ofFinite F
  have hq : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [Matrix.card_SL_field (1 + 2), hq]
  simp [Fin.prod_univ_succ]

theorem card_SL_four_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card (SpecialLinearGroup (Fin (2 + 2)) F) = 20160 := by
  have := Fintype.ofFinite F
  have hq : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [Matrix.card_SL_field (2 + 2), hq]
  simp [Fin.prod_univ_succ]

theorem hsyl_three_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card F ^ (∑ j ∈ Finset.Ico 0 (1 + 1), (1 + 1 - j)) =
      2 ^ (Nat.card (SpecialLinearGroup (Fin (1 + 2)) F)).factorization 2 := by
  rw [card_SL_three_two hF, hF]
  have := factorization_two_pow_mul_odd 3 21 (by norm_num)
  have h168 : (168 : ℕ).factorization 2 = 3 := by simpa using this
  rw [h168]
  decide

theorem hsyl_three_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card F ^ (∑ j ∈ Finset.Ico 0 (1 + 1), (1 + 1 - j)) =
      2 ^ (Nat.card (SpecialLinearGroup (Fin (1 + 2)) F)).factorization 2 := by
  rw [card_SL_three_four hF, hF]
  have := factorization_two_pow_mul_odd 6 945 (by norm_num)
  have h60480 : (60480 : ℕ).factorization 2 = 6 := by simpa using this
  rw [h60480]
  decide

theorem hsyl_four_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card F ^ (∑ j ∈ Finset.Ico 0 (2 + 1), (2 + 1 - j)) =
      2 ^ (Nat.card (SpecialLinearGroup (Fin (2 + 2)) F)).factorization 2 := by
  rw [card_SL_four_two hF, hF]
  have := factorization_two_pow_mul_odd 6 315 (by norm_num)
  have h20160 : (20160 : ℕ).factorization 2 = 6 := by simpa using this
  rw [h20160]
  decide

end CFSG.CGT.T75N
