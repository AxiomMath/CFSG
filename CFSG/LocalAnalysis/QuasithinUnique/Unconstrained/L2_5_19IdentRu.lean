module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathieu
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.Schreier.RuOddCoreBase

public section

namespace CFSG.QuasithinUnique.Id2519.MathNoLayer

open CFSG.Blueprint CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_hasKComponent_of_dvd_primes {K : Type*} [Group K] [Finite K] {N : ℕ}
    (hN : Nat.card K ∣ N) (h168 : ¬ 168 ∣ N) (h360 : ¬ 360 ∣ N)
    (hp : ∀ p : ℕ, p.Prime → 17 ≤ p → ¬ p ∣ 2 * N) : ¬ HasKComponent K := by
  rintro ⟨B, -, hKB⟩
  have hd : Nat.card ↥B ∣ N := (Subgroup.card_subgroup_dvd_card B).trans hN
  rcases hKB with h | h | ⟨p, hFM, h7, hpB⟩
  · rw [h] at hd
    exact h168 hd
  · rw [h] at hd
    exact h360 hd
  · refine hp p hFM.1 (seventeen_le_of_isFermatOrMersenne hFM h7) ?_
    have h1 : p ∣ p * (p * p - 1) := dvd_mul_right p _
    rw [hpB] at h1
    exact h1.trans (Nat.mul_dvd_mul_left 2 hd)

theorem no_prime_dvd_245760 : ∀ p : ℕ, p.Prime → 17 ≤ p → ¬ p ∣ 2 * 245760 := by
  intro p hp h17 hd
  have e : 2 * 245760 = 2 ^ 15 * (3 * 5) := by norm_num
  rw [e] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega

theorem no_prime_dvd_116480 : ∀ p : ℕ, p.Prime → 17 ≤ p → ¬ p ∣ 2 * 116480 := by
  intro p hp h17 hd
  have e : 2 * 116480 = 2 ^ 9 * (5 * (7 * 13)) := by norm_num
  rw [e] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · have := Nat.le_of_dvd (by norm_num) h
        omega
      · have := Nat.le_of_dvd (by norm_num) h
        omega

theorem ru_centralizer_card
    {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruP) (h2 : orderOf t = 2) :
    Nat.card ↥(ruP ⊓ Subgroup.centralizer {t}) = 245760 ∨
      Nat.card ↥(ruP ⊓ Subgroup.centralizer {t}) = 116480 := by
  have hinv : t ∈ {t | t ∈ ruP ∧ orderOf t = 2} := ⟨ht, h2⟩
  rw [ruInvolutions_eq] at hinv
  rcases hinv with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · left
    rw [← Nat.card_congr (conjCentralizerEquiv hg ruZ).toEquiv, ← ruC_eq_centralizer, card_ruC]
  · right
    rw [← Nat.card_congr (conjCentralizerEquiv hg ruA0).toEquiv, ruCentralizer_a, card_ruL]

theorem ru_centralizer_noK
    {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruP) (h2 : orderOf t = 2) :
    NoK (centralizerIn ruP t) := by
  rcases ru_centralizer_card ht h2 with h | h
  · exact not_hasKComponent_of_dvd_primes (N := 245760) (by rw [centralizerIn]; rw [h])
      (by decide) (by decide) no_prime_dvd_245760
  · exact not_hasKComponent_of_dvd_primes (N := 116480) (by rw [centralizerIn]; rw [h])
      (by decide) (by decide) no_prime_dvd_116480

noncomputable def ruEquivCar
    : NativeSporadic.Carrier .Ru ≃* ↥ruP := ruEquivP

theorem ru_fix_noK
    (α : MulAut (NativeSporadic.Carrier .Ru)) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    ¬ HasKComponent ↥(fixSubgroup α) := by
  intro hk
  set α' : MulAut ruP := MulAut.congr ruEquivCar α with hα'
  have hk' : HasKComponent ↥(fixSubgroup α') :=
    hasKComponent_fixSubgroup_of_intertwine ruEquivCar α α'
      (fun y => by
        rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply]) hk
  have hα'2 : α' * α' = 1 := by rw [hα', ← map_mul, hα2, map_one]
  have hα'1 : α' ≠ 1 := fun h =>
    hα1 ((MulAut.congr ruEquivCar).injective (by rw [map_one]; exact h))
  obtain ⟨g, hg⟩ := mulAut_inner α'
  obtain ⟨y, hy, ⟨e⟩⟩ := fix_of_inner ruP center_ruP α' ⟨g, hg.symm⟩ hα'2 hα'1
  exact ru_centralizer_noK y.2 hy (hk'.of_mulEquiv e)

theorem tabIdentFor_ru
    : TabIdentFor (@Ident.FamSporadic .Ru) := by
  refine tabIdentFor_of_fix CFSG.Sporadic.Ru.fam_ru_simplicity.2.2 ?_ ru_fix_noK
  by_contra hcon
  push Not at hcon
  have : IsSimpleGroup NativeSporadic.Ru := CFSG.Sporadic.Ru.fam_ru_simplicity.2.2
  let _ : CommGroup NativeSporadic.Ru :=
    { (inferInstance : Group NativeSporadic.Ru) with mul_comm := fun a b => hcon a b }
  have : Finite NativeSporadic.Ru := CFSG.Sporadic.Ru.fam_ru_simplicity.1
  have hp := IsSimpleGroup.prime_card (α := NativeSporadic.Ru)
  rw [CFSG.Sporadic.Ru.card_Ru] at hp
  exact absurd hp (by norm_num)

end CFSG.QuasithinUnique.Id2519.MathNoLayer
