module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIUCfg
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Assembly.LowTwoRank

namespace QPUJ6

theorem five_le_pow_two_mul {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    5 ≤ p ^ (2 * f) := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  calc 5 ≤ 3 ^ 2 := by norm_num
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
    _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right hp.pos (by omega)

theorem statedClassicalModel_of_lieModel {X : Type} [Group X] {τ : StatedLieTag} {n p f : ℕ}
    (hn : n ≠ 0) (h : Blueprint.LieModel X τ n p f) : StatedClassicalModel X τ n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem isSimpleGroup {X : Type} [Group X] {p f : ℕ} (hX : IsL4U4Mod4 X p f) :
    IsSimpleGroup X := by
  rcases hX with ⟨hX, -⟩ | ⟨hX, -⟩
  · exact (LieType.Simplicity.fam_PSL_simplicity X 4 p f
      (statedClassicalModel_of_lieModel (by norm_num) hX)).2
  · exact (ClassicalGroups.Unitary.fam_PSU_simplicity X 4 p f
      (statedClassicalModel_of_lieModel (by norm_num) hX)).2

theorem not_dvd_pow_sub_one_add_one {p f k : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hk : 1 ≤ k) :
    ¬ p ∣ (p ^ f) ^ k - 1 ∧ ¬ p ∣ (p ^ f) ^ k + 1 := by
  have h1 : p ∣ (p ^ f) ^ k := dvd_pow (dvd_pow_self p (by omega)) (by omega)
  have h2 : 1 ≤ (p ^ f) ^ k := Nat.one_le_pow _ _ (pow_pos hp.pos _)
  constructor
  · intro h
    have h3 : p ∣ (p ^ f) ^ k - ((p ^ f) ^ k - 1) := Nat.dvd_sub h1 h
    rw [show (p ^ f) ^ k - ((p ^ f) ^ k - 1) = 1 by omega] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  · intro h
    exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h))

theorem order_data (hO : CatLeaf.LieOrderFormulasInput) {X : Type} [Group X] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hX : IsL4U4Mod4 X p f) :
    ∃ A : ℕ, Nat.card X * 2 = (p ^ f) ^ 6 * A ∧ ¬ p ∣ A ∧ A < (p ^ f) ^ 10 ∧ 128 ∣ A ∧
      ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1) ∣ A := by
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hq3 : 3 ≤ p ^ f := by
    have := hp.two_le
    exact (show 3 ≤ p by omega).trans (Nat.le_self_pow (by omega) p)
  have hdiv : ∀ {b : ℕ}, ¬ p ∣ b → ¬ p ∣ ((p ^ f) ^ 2 - 1) * (b * ((p ^ f) ^ 4 - 1)) := by
    intro b hb h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact (not_dvd_pow_sub_one_add_one hp hf (by norm_num)).1 h1
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · exact hb h2
    · exact (not_dvd_pow_sub_one_add_one hp hf (by norm_num)).1 h2
  have hlt : ∀ {b : ℕ}, b ≤ (p ^ f) ^ 4 →
      ((p ^ f) ^ 2 - 1) * (b * ((p ^ f) ^ 4 - 1)) < (p ^ f) ^ 10 := by
    intro b hb
    have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc ((p ^ f) ^ 2 - 1) * (b * ((p ^ f) ^ 4 - 1))
        ≤ ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 * (p ^ f) ^ 4) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hb (Nat.sub_le _ _))
      _ < (p ^ f) ^ 2 * ((p ^ f) ^ 4 * (p ^ f) ^ 4) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = (p ^ f) ^ 10 := by ring
  have h128 : ∀ {b : ℕ}, 128 ∣ ((p ^ f) ^ 2 - 1) * (b * ((p ^ f) ^ 4 - 1)) := by
    intro b
    have hQ1 : 1 ≤ p ^ f := hodd.pos
    have h8 : 8 ∣ (p ^ f) ^ 2 - 1 := Nat.eight_dvd_sq_sub_one_of_odd hodd
    have h16 : 16 ∣ (p ^ f) ^ 4 - 1 := by
      have h4 : (p ^ f) ^ 4 - 1 = ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 2 + 1) := by
        have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hQ1
        have h2 : 1 ≤ (p ^ f) ^ 4 := Nat.one_le_pow _ _ hQ1
        zify [h1, h2]
        ring
      rw [h4]
      exact Nat.mul_dvd_mul h8 (even_iff_two_dvd.mp hodd.pow.add_one)
    exact Nat.dvd_trans (by norm_num) (Nat.mul_dvd_mul h8 (Dvd.dvd.mul_left h16 _))
  have hfac : ∀ {b : ℕ}, ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1) ∣
      ((p ^ f) ^ 2 - 1) * (b * ((p ^ f) ^ 4 - 1)) :=
    Nat.mul_dvd_mul_left _ (Dvd.intro_left _ rfl)
  rcases hX with ⟨hX, hm⟩ | ⟨hX, hm⟩
  · obtain ⟨-, hc, -⟩ := hO X .PSL 4 p f (statedClassicalModel_of_lieModel (by norm_num) hX).1 hX
    have hg : Nat.gcd 4 (p ^ f - 1) = 2 := by
      rw [Nat.gcd_rec, show (p ^ f - 1) % 4 = 2 by omega]
      norm_num
    have hc' : Nat.card X * Nat.gcd 4 (p ^ f - 1) =
        (p ^ f) ^ 6 * ∏ i ∈ Finset.Icc 2 4, ((p ^ f) ^ i - 1) := hc
    rw [show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
      Finset.prod_pair (by norm_num), hg] at hc'
    refine ⟨_, hc', hdiv (not_dvd_pow_sub_one_add_one hp hf (by norm_num)).1, hlt ?_, h128,
      hfac⟩
    have h1 : (p ^ f) ^ 3 ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  · obtain ⟨-, hc, -⟩ := hO X .PSU 4 p f (statedClassicalModel_of_lieModel (by norm_num) hX).1 hX
    have hg : Nat.gcd 4 (p ^ f + 1) = 2 := by
      rw [Nat.gcd_rec, show (p ^ f + 1) % 4 = 2 by omega]
      norm_num
    have hc' : Nat.card X * Nat.gcd 4 (p ^ f + 1) = (p ^ f) ^ 6 *
        ∏ i ∈ Finset.Icc 2 4, (if Even i then (p ^ f) ^ i - 1 else (p ^ f) ^ i + 1) := hc
    rw [show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
      Finset.prod_pair (by norm_num), hg] at hc'
    simp only [show Even 2 by decide, show ¬ Even 3 by decide, show Even 4 by decide, ite_true,
      ite_false] at hc'
    refine ⟨_, hc', hdiv (not_dvd_pow_sub_one_add_one hp hf (by norm_num)).2, hlt ?_, h128,
      hfac⟩
    have h1 : (p ^ f) ^ 4 = (p ^ f) ^ 3 * p ^ f := pow_succ _ 3
    have h2 : (p ^ f) ^ 3 * 3 ≤ (p ^ f) ^ 3 * p ^ f := Nat.mul_le_mul_left _ hq3
    have h3 : 1 ≤ (p ^ f) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega

theorem sixteen_dvd_card (hO : CatLeaf.LieOrderFormulasInput) {X : Type} [Group X] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hX : IsL4U4Mod4 X p f) : 16 ∣ Nat.card X := by
  obtain ⟨A, hc, -, -, h128, -⟩ := order_data hO hp hp2 hf hX
  have h1 : 128 ∣ Nat.card X * 2 := by
    rw [hc]
    exact Dvd.dvd.mul_left h128 _
  omega

end QPUJ6

end CFSG.ComponentClassification.GSThmB
