module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4
public import CFSG.RankThree.PartOne.Q1327C.BNoCube
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.RankThree.PartOne.K128.ReeShape

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)

@[expose] def regimeReeF4 (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ m : ℕ, idx.1 = .reeF4 m ∧ ¬ p ∣ (2 ^ (2 * m + 1)) ^ 4 - 1

@[expose] def regimeReeF4Inner (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ m : ℕ, idx.1 = .reeF4 m ∧ 5 ≤ p ∧ ¬ p ∣ 2 * m + 1

@[expose] def regimeReeF4Vac (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  regimeReeF4 idx p ∨ regimeReeF4Inner idx p

section Cat


theorem rankLE1_cat_reeF4 {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hnd : ¬ p ∣ (2 ^ (2 * m + 1)) ^ 4 - 1) :
    RankLE1 p (Cat ⟨.reeF4 m, hv⟩) := by
  obtain ⟨X, _, _, _, -, hX, -, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  have : Finite (ModGL F4.tag X) := finite_modGL
  have : Finite (F4.reeGamma X m) := Subtype.finite
  have hQ1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  have hfac : (2 ^ (2 * m + 1)) ^ 4 - 1 =
      (2 ^ (2 * m + 1) - 1) * (2 ^ (2 * m + 1) + 1) * ((2 ^ (2 * m + 1)) ^ 2 + 1) := by
    have h4 : 1 ≤ (2 ^ (2 * m + 1)) ^ 4 := Nat.one_le_pow _ _ hQ1
    zify [hQ1, h4]
    ring
  have h1 : ¬ p ∣ 2 ^ (2 * m + 1) - 1 := fun h => hnd (by
    rw [hfac]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
  have h2 : ¬ p ∣ 2 ^ (2 * m + 1) + 1 := fun h => hnd (by
    rw [hfac]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)
  have h4 : ¬ p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := fun h => hnd (by
    rw [hfac]
    exact dvd_mul_of_dvd_right h _)
  have hpQ : ¬ p ∣ 2 ^ (2 * m + 1) := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hsq : (2 ^ (2 * m + 1)) ^ 2 - 1 ∣ (2 ^ (2 * m + 1)) ^ 4 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow ((2 ^ (2 * m + 1)) ^ 2) 1 2
    rwa [one_pow, ← pow_mul (2 ^ (2 * m + 1)) 2 2] at h
  have hp5 : 5 ≤ p := five_le_of_not_dvd_sq_sub_one hp hp2 hpQ fun h => hnd (h.trans hsq)
  refine RankLE1.of_mulEquiv e.symm (rankLE1_of_pRank hp fun hdvd => ?_)
  rcases (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    m X hX).2 p hp (by omega) hdvd with h | h | h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h4
  · exact CFSG.RankThree.PartOne.K128.pRank_le_one_ree_phi6 hX hp hp5 h
  · exact CFSG.RankThree.PartOne.K128.pRank_le_one_ree_phi12 hX hp hp5 h

theorem crossCharFamAt_reeF4 : CrossCharFamAt .reeF4 regimeReeF4 := by
  rintro ⟨d, hv⟩ _ p hp hp2 - ⟨m, hd, hnd⟩
  change d = _ at hd
  subst hd
  obtain ⟨_, _, _, _, _, _, hS, _⟩ := exists_reeGamma_equiv_cat hv
  have : IsSimpleGroup (Cat ⟨.reeF4 m, hv⟩) := hS
  obtain ⟨-, -, -, hc, -⟩ := large_Ree_model_field_outer_group_and_inner_involutions _ 2
    (2 * m + 1) (reeTitsModel_cat_reeF4 hv)
  have : IsCyclic (Outer (Cat ⟨.reeF4 m, hv⟩)) := hc
  exact isLocallyBalancedAbs_of_rankLE1_of_simple (MulEquiv.refl _)
    (QuotientGroup.mk' (inner (Cat ⟨.reeF4 m, hv⟩))) hp
    (fun x hx _ => (QuotientGroup.eq_one_iff (N := inner (Cat ⟨.reeF4 m, hv⟩)) x).1 hx)
    (rankLE1_cat_reeF4 hv hp hp2 hnd)

theorem crossCharFamAt_reeF4_inner : CrossCharFamAt .reeF4 regimeReeF4Inner := by
  rintro ⟨d, hv⟩ _ p hp hp2 - ⟨m, hd, hp5, hf⟩
  change d = _ at hd
  subst hd
  obtain ⟨X, _, _, _, _, _, hS, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  have : IsSimpleGroup (Cat ⟨.reeF4 m, hv⟩) := hS
  have : Finite (ModGL F4.tag X) := finite_modGL
  have : Finite (F4.reeGamma X m) := Subtype.finite
  have : Finite (Cat ⟨.reeF4 m, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨-, -, -, -, hcard, -⟩ := large_Ree_model_field_outer_group_and_inner_involutions _ 2
    (2 * m + 1) (reeTitsModel_cat_reeF4 hv)
  have hcop : Nat.Coprime p (Nat.card (Outer (Cat ⟨.reeF4 m, hv⟩))) := by
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hf
  exact isLocallyBalancedAbs_of_rankLE2_of_simple (MulEquiv.refl _)
    (QuotientGroup.mk' (inner (Cat ⟨.reeF4 m, hv⟩))) hp hcop
    (fun x hx _ => (QuotientGroup.eq_one_iff (N := inner (Cat ⟨.reeF4 m, hv⟩)) x).1 hx)
    (rankLE2_of_noPowThree hp fun _ hE hc =>
      CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_ree_five (reeTitsModel_cat_reeF4 hv) hp
        hp5 hE hc)

theorem crossCharFamAt_reeF4_vac : CrossCharFamAt .reeF4 regimeReeF4Vac :=
  crossCharFamAt_reeF4.or crossCharFamAt_reeF4_inner

end Cat

end CFSG.HardMathSupport.Timmesfeld.CrossChar
