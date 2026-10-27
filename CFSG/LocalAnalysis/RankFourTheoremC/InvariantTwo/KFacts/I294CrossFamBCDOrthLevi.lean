module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDOrthCore
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDSp

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup Matrix CFSG.ClassicalGroups.Orthogonal

section Levi

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
  {p s e : ℕ} [hp : Fact p.Prime] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

theorem crossAt_statedProj_omega_levi (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) (he : 0 < e)
    (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) (hQ : ⇑Q = Q₀)
    (hab : CFSG.IsElementaryAbelian 2 (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q)))
    (hhom : ∀ (c : K) (w : ι → K), Q₀ (c • w) = c ^ 2 * Q₀ w) {w₀ : ι → K} (hw₀ : Q₀ w₀ = 1)
    (lev : GL (Fin s) K →* GL ι K) (hlev : Function.Injective lev)
    (hiso : ∀ (g : GL (Fin s) K) (v : ι → K), Q₀ ((lev g : Matrix ι ι K) *ᵥ v) = Q₀ v)
    (hord : padicValNat p (Nat.card (StatedProj (StatedOmega Q₀))) =
      padicValNat p (Nat.card (GL (Fin s) K))) :
    (CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega Q₀))) = 2 →
      ∀ R : Sylow p (StatedProj (StatedOmega Q₀)),
        IsMulCommutative (R : Subgroup (StatedProj (StatedOmega Q₀)))) ∧
    (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega Q₀))) →
      ∀ y : StatedProj (StatedOmega Q₀), y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (StatedProj (StatedOmega Q₀))))) := by
  have hp2 : Odd p := hp.out.odd_of_ne_two (by omega)
  set Ω := StatedOmega Q₀ with hΩ
  let N : Subgroup Ω := (StatedScalars ι K).subgroupOf Ω
  have hN : ¬ p ∣ Nat.card N := by
    intro hd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
    obtain ⟨c, hc⟩ : ((z : Ω) : GL ι K) ∈ StatedScalars ι K := z.2
    have hiso' : ∀ v, Q₀ (((Matrix.GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K) *ᵥ v) =
        Q₀ v := by
      rw [hc]
      exact isometry_of_mem_statedOmega hQ (z : Ω).2
    have hc2 := sq_eq_one_of_scalar_isometry hhom hw₀ c hiso'
    have hz2 : z ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      change ((z : Ω) : GL ι K) ^ 2 = 1
      rw [← hc, ← map_pow, hc2, map_one]
    have := Nat.le_of_dvd two_pos (hz ▸ orderOf_dvd_of_pow_eq_one hz2)
    omega
  let M' : Subgroup (GL (Fin s) K) := Ω.comap lev
  have hcont : ∀ g : GL (Fin s) K, (∃ k : ℕ, g ^ (p ^ k) = 1) → g ∈ M' := by
    rintro g ⟨k, hk⟩
    exact mem_statedOmega_of_pow_eq_one hQ hab hp2 (hiso g) (by rw [← map_pow, hk, map_one])
  have hcont1 : ∀ g : GL (Fin s) K, g ^ p = 1 → g ∈ M' := fun g hg =>
    hcont g ⟨1, by simpa using hg⟩
  let ι' : M' →* Ω := (lev.comp M'.subtype).codRestrict Ω (fun x => x.2)
  have hι' : Function.Injective ι' := fun a b h => Subtype.ext (hlev (congrArg Subtype.val h))
  have hidx : ¬ p ∣ ι'.range.index := by
    have hmul := Subgroup.card_mul_index ι'.range
    have hcardR : Nat.card ι'.range = Nat.card M' :=
      (Nat.card_congr (MonoidHom.ofInjective hι').toEquiv).symm
    have hH : Nat.card Ω = Nat.card (StatedProj Ω) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hI0 : ι'.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hM'v : padicValNat p (Nat.card M') = padicValNat p (Nat.card (GL (Fin s) K)) := by
      have h1 := Subgroup.card_mul_index M'
      have hI : ¬ p ∣ M'.index := not_dvd_index_of_contains_pElements M' hcont
      have hI0' : M'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h2 := congrArg (padicValNat p) h1
      rw [padicValNat.mul Nat.card_pos.ne' hI0', padicValNat.eq_zero_of_not_dvd hI,
        add_zero] at h2
      exact h2
    have hLN : padicValNat p (Nat.card Ω) = padicValNat p (Nat.card (StatedProj Ω)) := by
      rw [hH, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne',
        padicValNat.eq_zero_of_not_dvd hN, add_zero]
    have h1 := congrArg (padicValNat p) hmul
    rw [padicValNat.mul Nat.card_pos.ne' hI0, hcardR, hM'v, hLN, hord] at h1
    intro hd
    have := (dvd_iff_padicValNat_ne_zero hI0).1 hd
    omega
  refine crossAt_of_levi (d := s / e) hp5 N hN ι' hι' hidx ?_ ?_ ?_
  · exact fun hne => restrict_isMulCommutative M' fun P hP =>
      isMulCommutative_of_isPGroup_GL_matrix hp2 hpK he hpe hne hP
  · exact restrict_le_pRank M' hcont1 (le_pRank_GL_matrix hpK he hpe (Nat.div_mul_le_self s e))
  · intro hpd y hy
    have h3e : 3 * e ≤ s := by
      have := (Nat.le_div_iff_mul_le he).1 hpd
      nlinarith
    exact restrict_centralizer M' hcont1 (fun y₀ hy₀ =>
      le_pRank_centralizer_GL_matrix hp5 hpK he hpe (by omega) h3e hy₀) y hy

end Levi

end CFSG.LocalAnalysis.RankFourTheoremC
