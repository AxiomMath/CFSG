module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslNonab
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslBlock
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous
import CFSG.GroupTheory.WeirSylow.FieldTorus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

theorem wcOn_projSL_of_not_dvd_sub_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {F : Type}
    [Field F] [Finite F] {n : ℕ} [NeZero n] (hpq : ¬ p ∣ Nat.card F)
    (hpq1 : ¬ p ∣ Nat.card F - 1) : WCOn p (StatedProj (StatedSL n F)) := by
  have hp := (Fact.out : p.Prime)
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have he : 0 < CrossNum.crossE p (Nat.card F) := CrossNum.crossE_pos hpq
  have he1 : CrossNum.crossE p (Nat.card F) ≠ 1 := by
    intro h
    apply hpq1
    have h1 : ((Nat.card F : ℕ) : ZMod p) = 1 := orderOf_eq_one_iff.1 h
    have h2 : (((Nat.card F - 1 : ℕ) : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hq1.le, h1, Nat.cast_one, sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).1 h2
  have ha1 : 1 ≤ CrossNum.crossA p (Nat.card F) := CrossNum.one_le_crossA hpq hq1
  have hdvd : p ^ CrossNum.crossA p (Nat.card F) ∣
      Nat.card F ^ CrossNum.crossE p (Nat.card F) - 1 := CrossNum.pow_crossA_dvd hpq
  have hN : ¬ p ∣ Nat.card ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) :=
    not_dvd_card_scalars_of_not_dvd_sub_one hpq1
  have hord := factorization_card_projSL hp2 hpq hN
  rw [Nat.factorization_eq_zero_of_not_dvd hpq1, add_zero] at hord
  generalize CrossNum.crossE p (Nat.card F) = e at he he1 hdvd hord
  generalize CrossNum.crossA p (Nat.card F) = a at ha1 hdvd hord
  obtain ⟨r, hr⟩ : ∃ r, n / e = r := ⟨_, rfl⟩
  rw [hr] at hord
  by_cases hr0 : r = 0
  · subst hr0
    refine WCOn.of_factorization_le_one ?_
    rw [hord]
    simp
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  haveI : NeZero e := ⟨he.ne'⟩
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq
    (L := FiniteField.Extension F (ringChar F) e) (d := p ^ a)
    (by rwa [FiniteField.natCard_extension])
  obtain ⟨ρ₀, hρ₀⟩ := CFSG.GroupTheory.WeirSylow.exists_injective_hom_of_orderOf_eq
    (H := (⊤ : Subgroup (FiniteField.Extension F (ringChar F) e)ˣ)) (Subgroup.mem_top ζ) hζ
  obtain ⟨T, S, Fr, hTinj, -, hS, -, hFr, hU⟩ :=
    exists_blockFrame F
      ((⊤ : Subgroup (FiniteField.Extension F (ringChar F) e)ˣ).subtype.comp ρ₀)
      (Subtype.val_injective.comp hρ₀) r (n % e) n
      (by rw [FiniteField.finrank_extension, ← hr]; exact Nat.div_add_mod n e) hrpos
  have hdet1 : ∀ c, ((T c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := fun c =>
    det_eq_one_of_pow_eq_one hpq1 (k := a) (by rw [← map_pow, pow_pPow_eq_one_pi, map_one])
  by_cases hrp : p ≤ r
  ·
    have hNP := nonscalarPPair_of_frame hp2 ha1 hrp (Or.inl hpq1) T S hTinj hS
      (fun c _ => hdet1 c)
      (fun σ hσ => det_eq_one_of_pow_eq_one hpq1 (k := 1)
        (by rw [pow_one, ← map_pow, hσ, map_one]))
    exact hNP.wcOn_statedProj
  · push Not at hrp
    have hv : (Nat.card (StatedProj (StatedSL n F))).factorization p = a * r := by
      rw [hord, padicValNat.eq_zero_of_not_dvd, add_zero]
      intro hdvd'
      have := (Nat.Prime.dvd_factorial hp).1 hdvd'
      omega
    have hΨ : Function.Injective (liftSL T hdet1) :=
      liftSL_injective hTinj (fun c => ⟨a, pow_pPow_eq_one_pi c⟩) hN
    have hcard : Nat.card (Fin r → Multiplicative (ZMod (p ^ a))) =
        p ^ (Nat.card (StatedProj (StatedSL n F))).factorization p := by
      rw [hv, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, ← pow_mul, mul_comm]
    by_cases hr1 : r = 1
    · subst hr1
      haveI : IsCyclic (Fin 1 → Multiplicative (ZMod (p ^ a))) :=
        isCyclic_of_surjective (MulEquiv.funUnique (Fin 1) (Multiplicative (ZMod (p ^ a)))).symm
          (MulEquiv.funUnique (Fin 1) (Multiplicative (ZMod (p ^ a)))).symm.surjective
      exact wcOn_of_range_cyclic (liftSL T hdet1) hΨ hcard
    · have hr2 : 2 ≤ r := by omega
      refine wcOn_of_range_nml (liftSL T hdet1) hΨ hcard
        (normalizerMovesLines_range_twisted hr2 (liftSL T hdet1) hΨ ?_ ⟨0, by omega⟩ ?_)
      · intro i j
        obtain ⟨g', hg'det, hg'⟩ := exists_det_one_conj hU (S (Equiv.swap i j))
        refine ⟨slProj n F ⟨g', CFSG.Open.StatedAPI.mem_statedSL_of_det hg'det⟩,
          fun c => liftSL_conj hg'det ?_⟩
        rw [hg', hS, Equiv.swap_inv]
      · obtain ⟨g', hg'det, hg'⟩ := exists_det_one_conj hU (Fr ⟨0, by omega⟩)
        refine ⟨slProj n F ⟨g', CFSG.Open.StatedAPI.mem_statedSL_of_det hg'det⟩,
          (Nat.card F : ℤ), ?_, fun c => liftSL_conj hg'det ?_⟩
        · intro h
          apply hpq1
          have h' : (((Nat.card F - 1 : ℕ) : ℕ) : ℤ) = (Nat.card F : ℤ) - 1 := by
            rw [Nat.cast_sub hq1.le, Nat.cast_one]
          rw [← h'] at h
          exact Int.natCast_dvd_natCast.1 h
        · rw [hg', hFr, zpow_natCast]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
