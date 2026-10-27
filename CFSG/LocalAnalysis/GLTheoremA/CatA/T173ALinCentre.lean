module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
import CFSG.Assembly.GL83StatedBridge
import CFSG.LieType.Steinberg.CentralExt.PSLSmall
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultBound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups


private theorem two_pow_sub_one_odd {m : ℕ} (hm : 0 < m) : Odd (2 ^ m - 1) := by
  have h : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  obtain ⟨k, hk⟩ : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, hm.ne'⟩
  exact ⟨k - 1, by omega⟩

private theorem nonempty_linPSL_statedProj (d : ℕ) (F : Type) [Field F] :
    Nonempty (LinPSL d F ≃* StatedProj (StatedSL d F)) :=
  CFSG.StandardType.nonempty_proj_congr (largeEvenSLGroup_eq_statedSL (K := F) d)

private theorem center_dvd_of_griess_row {K X : Type} [Group K] [Finite K] [Group X]
    (hK : CFSG.Open.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* X) (A B C : ℕ)
    (hrow : commutator X = ⊤ ∧ Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
      Multiplicative (ZMod A × ZMod B × ZMod C))) :
    Nat.card (Subgroup.center K) ∣ A * B * C := by
  have h := card_center_dvd_hopfMultiplier_of_cover hK
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (by simp)
  obtain ⟨-, ⟨r⟩⟩ := hrow
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toEquiv,
    Nat.card_congr r.toEquiv] at h
  have hcard : Nat.card (Multiplicative (ZMod A × ZMod B × ZMod C)) = A * B * C := by
    simp only [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod]
    ring
  rwa [hcard] at h

private theorem not_dvd_griess_psl_orders {p d n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 2 ≤ n) (hd : ¬ p ∣ d) :
    ¬ p ∣ Nat.gcd d (2 ^ n - 1) *
      (CFSG.Open.griessPSLExceptional d (2 ^ n)).1 *
        (CFSG.Open.griessPSLExceptional d (2 ^ n)).2 := by
  have h2n4 : 2 ^ n = 4 ↔ n = 2 := by
    constructor
    · intro h
      exact Nat.pow_right_injective (le_refl 2)
        (show 2 ^ n = 2 ^ 2 from by rw [h])
    · intro h
      subst h
      norm_num
  have h2n2 : 2 ^ n ≠ 2 := by
    intro h
    have : n = 1 := Nat.pow_right_injective (le_refl 2)
      (show 2 ^ n = 2 ^ 1 from by rw [h])
    omega
  have h2n9 : 2 ^ n ≠ 9 := by
    intro h
    have hdvd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    rw [h] at hdvd
    norm_num at hdvd
  have hgcd : ¬ p ∣ Nat.gcd d (2 ^ n - 1) :=
    fun h => hd (h.trans (Nat.gcd_dvd_left d (2 ^ n - 1)))
  have hfour : ¬ p ∣ 4 := by
    intro h
    have h4 : p ∣ 2 ^ 2 := by
      norm_num
      exact h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  have hval : CFSG.Open.griessPSLExceptional d (2 ^ n) = (1, 1) ∨
      CFSG.Open.griessPSLExceptional d (2 ^ n) = (2, 1) ∨
      CFSG.Open.griessPSLExceptional d (2 ^ n) = (4, 4) := by
    by_cases hd2 : d = 2
    · by_cases hn2 : n = 2
      · exact Or.inr (Or.inl (by subst hd2; subst hn2; decide))
      · refine Or.inl ?_
        subst hd2
        exact CFSG.LieType.Steinberg.CentralExt.SLClosed.griessPSLExceptional_eq_one
          (by rintro ⟨-, h⟩; exact hn2 (h2n4.mp h))
          (by rintro ⟨-, h⟩; exact h2n9 h)
          (by rintro ⟨h, -⟩; omega)
          (by rintro ⟨h, -⟩; omega)
          (by rintro ⟨h, -⟩; omega)
    · by_cases hd3 : d = 3
      · by_cases hn2 : n = 2
        · exact Or.inr (Or.inr (by subst hd3; subst hn2; decide))
        · refine Or.inl ?_
          subst hd3
          exact CFSG.LieType.Steinberg.CentralExt.SLClosed.griessPSLExceptional_eq_one
            (by rintro ⟨h, -⟩; omega)
            (by rintro ⟨h, -⟩; omega)
            (by rintro ⟨-, h⟩; exact h2n2 h)
            (by rintro ⟨-, h⟩; exact hn2 (h2n4.mp h))
            (by rintro ⟨h, -⟩; omega)
      · refine Or.inl ?_
        exact CFSG.LieType.Steinberg.CentralExt.SLClosed.griessPSLExceptional_eq_one
          (by rintro ⟨h, -⟩; exact hd2 h)
          (by rintro ⟨h, -⟩; exact hd2 h)
          (by rintro ⟨h, -⟩; exact hd3 h)
          (by rintro ⟨h, -⟩; exact hd3 h)
          (by rintro ⟨-, h⟩; exact h2n2 h)
  rcases hval with hval | hval | hval
  · rw [hval]
    simpa using hgcd
  · rw [hval]
    intro h
    have h' : p ∣ Nat.gcd d (2 ^ n - 1) * 2 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).1 h' with h1 | h2
    · exact hgcd h1
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  · rw [hval]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h3 | h4
      · exact hgcd h3
      · exact hfour h4
    · exact hfour h2

theorem lin_center_coprime {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω]
    {S B : Subgroup Ω} (hS : CFSG.Open.IsQuasisimple ↥S) {n d : ℕ} {F : Type} [Field F]
    [Finite F] {θ : ↥S ⧸ Subgroup.center ↥S ≃* LinPSL d F} (hM : LinMarking p S B n d F θ)
    (hn : 2 ≤ n) (hd : ¬ p ∣ d) : ¬ p ∣ Nat.card (Subgroup.center ↥S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFcard : Nat.card F = 2 ^ n := hM.1
  have hd2 : 2 ≤ d := hM.2.2.1
  have hpdvd : p ∣ 2 ^ n - 1 := by
    rcases hM.2.2.2.2.1 with h | ⟨hn1, -⟩
    · exact h
    · omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := two_pow_sub_one_odd (by omega : 0 < n)
    obtain ⟨m, hm⟩ := hpdvd
    omega
  have hsmall : d = 2 → 4 ≤ 2 ^ n := by
    intro hd_eq
    subst hd_eq
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right' (by norm_num) hn
  have h29 : ¬ (d = 2 ∧ 2 ^ n = 9) := by
    rintro ⟨-, h⟩
    have hdvd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    rw [h] at hdvd
    norm_num at hdvd
  have h42 : ¬ (d = 4 ∧ 2 ^ n = 2) := by
    rintro ⟨-, h⟩
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right' (by norm_num) hn
    omega
  have hrow := CFSG.LieType.Steinberg.CentralExt.SLClosed.griess_psl_of_ne 2 n d
    (by omega : 0 < n) hd2 hsmall h29 h42
  let eSL : LinPSL d F ≃* StatedProj (StatedSL d F) :=
    (nonempty_linPSL_statedProj d F).some
  let eGal : StatedProj (StatedSL d F) ≃* PSL(d, GaloisField 2 n) :=
    CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F d 2 n (by omega : 0 < n) hFcard
  have hcenter : Nat.card (Subgroup.center ↥S) ∣
      Nat.gcd d (2 ^ n - 1) * (CFSG.Open.griessPSLExceptional d (2 ^ n)).1 *
        (CFSG.Open.griessPSLExceptional d (2 ^ n)).2 :=
    center_dvd_of_griess_row hS (θ.trans (eSL.trans eGal))
      (Nat.gcd d (2 ^ n - 1)) (CFSG.Open.griessPSLExceptional d (2 ^ n)).1
      (CFSG.Open.griessPSLExceptional d (2 ^ n)).2 hrow
  intro hpZ
  exact not_dvd_griess_psl_orders hp hp2 hn hd (hpZ.trans hcenter)

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
