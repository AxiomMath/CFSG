module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoCov
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Idx
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU4ThreeProof
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87BadSL3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Transport

private theorem l31f_isL2_of_equiv {Y T : Type} [Group Y] [Group T] (e : Y ≃* T) {P : ℕ → Prop}
    (h : IVK.IsL2 Y P) : IVK.IsL2 T P := by
  obtain ⟨F, hF, hFin, hP, ⟨f⟩⟩ := h
  exact ⟨F, hF, hFin, hP, ⟨e.symm.trans f⟩⟩

private theorem l31f_isSection_of_equiv_left {Y T B : Type} [Group Y] [Group T] [Group B]
    (e : Y ≃* T) (h : IsSection Y B) : IsSection T B := by
  obtain ⟨U, φ, hφ⟩ := h
  exact ⟨U, e.toMonoidHom.comp φ, e.surjective.comp hφ⟩

theorem l31f_kindFactorAll_of_equiv {k : Kind} {Y T : Type} [Group Y] [Group T] (e : Y ≃* T)
    (h : KindFactorAll k Y) : KindFactorAll k T := by
  cases k with
  | g2 => exact l31f_isL2_of_equiv (P := fun r => Odd r ∧ 5 ≤ r) e h
  | psp4 => exact l31f_isL2_of_equiv (P := fun r => Odd r ∧ 5 ≤ r) e h
  | m12 => exact l31f_isL2_of_equiv (P := fun r => Odd r ∧ 5 ≤ r) e h
  | l4 ε =>
    rcases h with h | h
    · exact Or.inl (l31f_isL2_of_equiv (P := fun r => Odd r ∧ 5 ≤ r) e h)
    · exact Or.inr (l31f_isSection_of_equiv_left e h)
  | mcl =>
    obtain ⟨n, h1, h2, h3⟩ := h
    exact ⟨n, h1, h2, l31f_isSection_of_equiv_left e h3⟩
  | ly =>
    obtain ⟨n, h1, h2, h3⟩ := h
    exact ⟨n, h1, h2, l31f_isSection_of_equiv_left e h3⟩

end Transport

section PrimePower

private theorem l31f_eq_two_two_of_pow_eq_four {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h4 : p ^ f = 4) : p = 2 ∧ f = 2 := by
  have hp2 : p = 2 := by
    have h : p ∣ 2 ^ 2 := by
      rw [show 2 ^ 2 = p ^ f from h4.symm]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (show 2 ^ f = 2 ^ 2 by rw [h4])⟩

private theorem l31f_ne_two_of_odd_pow {p f : ℕ} (hf : 1 ≤ f) (h : Odd (p ^ f)) : p ≠ 2 := by
  rintro rfl
  exact (Nat.not_even_iff_odd.mpr h) (Nat.even_pow.mpr ⟨even_two, by omega⟩)

end PrimePower

section PSL3

theorem l31f_not_kindFactorAll_psl3 (k : Kind) {Y : Type}
    [Group Y] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : Odd (p ^ f) ∨ p ^ f = 4)
    (hL : LieModel Y .PSL 3 p f) : ¬ KindFactorAll k Y := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  rcases hq with hodd | h4
  · have hp2 : p ≠ 2 := l31f_ne_two_of_odd_pow hf hodd
    have : Fact p.Prime := ⟨hp⟩
    have : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
    have hFodd : Odd (Nat.card F) := hcard ▸ hodd
    have h3 : 3 ≤ Nat.card F := by
      have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      have := Nat.odd_iff.mp hodd
      rw [hcard]
      omega
    intro h
    exact not_kindFactorAll hp2 (involved_qdSL_projectiveSL3 (p := p))
      (not_card_dvd_factorial_projectiveSL3 hFodd h3) (l31f_kindFactorAll_of_equiv e h)
  · obtain ⟨rfl, rfl⟩ := l31f_eq_two_two_of_pow_eq_four hp hf h4
    have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
    exact not_kindFactorAll_l34 minIndexL34 k hL

end PSL3

section PSU3

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem l31f_not_kindFactorAll_psu33 [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2)
    (hq3 : p ^ f = 3) (k : Kind) : ¬ KindFactorAll k (StatedProj (StatedSU 3 (p ^ f) K)) := by
  intro h
  obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp hq3
  have hmin := minIndexU33 _ (lieModel_statedProj_three_three hK)
  have hs := isSimpleGroup_statedProj_three_odd (K := K) (p := 3) (f := 1) hK (by norm_num)
  have : Nontrivial (StatedProj (StatedSU 3 (3 ^ 1) K)) := IsSimpleGroup.toNontrivial
  have hinv := involved_qdSL_statedProj_three (K := K) (p := 3) (f := 1) hK
  cases k with
  | g2 => exact not_isL2_of_involved (by norm_num) hinv h
  | psp4 => exact not_isL2_of_involved (by norm_num) hinv h
  | m12 => exact not_isL2_of_involved (by norm_num) hinv h
  | l4 ε =>
    rcases h with h | h
    · exact not_isL2_of_involved (by norm_num) hinv h
    · exact not_isSection_alt_seven_of_index (fun H hH => lt_trans (by norm_num) (hmin H hH)) h
  | mcl => exact not_kindFactorAll_mclly_of_index (Or.inl rfl) hmin h
  | ly => exact not_kindFactorAll_mclly_of_index (Or.inr rfl) hmin h

omit [Finite K] in
theorem l31f_not_kindFactorAll_psu34 (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2)
    (h4 : p ^ f = 4) (k : Kind) {Y : Type} [Group Y]
    (e : Y ≃* StatedProj (StatedSU 3 (p ^ f) K)) : ¬ KindFactorAll k Y := by
  have hcard := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (n := 3) hp hf hK
    (by norm_num)
  rw [h4] at hcard
  have hc : Nat.card Y = 62400 := by
    rw [Nat.card_congr e.toEquiv, h4, hcard]
    decide
  refine not_kindFactorAll_aux 62400 (by decide) (by norm_num) (by decide) k hc ?_
  intro hk hKF
  have := KindFactorAll.card_dvd hKF hk
  rw [hc] at this
  revert this
  decide

end PSU3

section PSU3Main

theorem l31f_not_kindFactorAll_psu3 (k : Kind) {Y : Type} [Group Y] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hq : Odd (p ^ f) ∨ p ^ f = 4)
    (hU : LieModel Y .PSU 3 p f) : ¬ KindFactorAll k Y := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hU
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hcard
  rcases hq with hodd | h4
  · have hp2 := l31f_ne_two_of_odd_pow hf hodd
    by_cases h5 : 5 ≤ p ^ f
    · intro h
      exact not_kindFactorAll hp2 (involved_qdSL_statedProj_three hcard)
        (not_card_dvd_factorial_statedProj_three_odd hf hcard (Nat.odd_iff.mp hodd) h5)
        (l31f_kindFactorAll_of_equiv e h)
    · have h3 : p ^ f = 3 := by
        have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
        have := Nat.odd_iff.mp hodd
        omega
      intro h
      exact l31f_not_kindFactorAll_psu33 hcard h3 k (l31f_kindFactorAll_of_equiv e h)
  · exact l31f_not_kindFactorAll_psu34 hp hf hcard h4 k e

end PSU3Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
