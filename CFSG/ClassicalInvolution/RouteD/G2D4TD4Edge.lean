module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Lin
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

section Facts

variable {p : ℕ} [Fact p.Prime]

theorem finite_galoisField_three (e : ℕ) (he : 1 ≤ e) : Finite (GaloisField p (3 * e)) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne'

theorem sigma_three_td4 (e : ℕ) (he : 1 ≤ e) (c : GaloisField p (3 * e)) :
    iterateFrobenius (GaloisField p (3 * e)) p e
      (iterateFrobenius (GaloisField p (3 * e)) p e
        (iterateFrobenius (GaloisField p (3 * e)) p e c)) = c := by
  have hK3 : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have := finite_galoisField_three (p := p) e he
  exact sigma_three_of_card hK3 (fun c => iterateFrobenius_def p e c) c

theorem two_ne_zero_galoisField_td4 (hp2 : p ≠ 2) (n : ℕ) : (2 : GaloisField p n) ≠ 0 := by
  have hK2 : ringChar (GaloisField p n) ≠ 2 := by
    rw [ringChar.eq (GaloisField p n) p]
    exact hp2
  exact Ring.two_ne_zero hK2

theorem neg_one_ne_one_galoisField_td4 (hp2 : p ≠ 2) (n : ℕ) : (-1 : (GaloisField p n)ˣ) ≠ 1 := by
  intro h
  have hK2 : ringChar (GaloisField p n) ≠ 2 := by
    rw [ringChar.eq (GaloisField p n) p]
    exact hp2
  exact Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val h)

theorem range_twistedIncl_eq (hp2 : p ≠ 2) (e : ℕ) (he : 1 ≤ e) :
    (twistedIncl (iterateFrobenius (GaloisField p (3 * e)) p e)).range =
      graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
        (iterateFrobenius (GaloisField p (3 * e)) p e) := by
  rw [← CFSG.ClassicalInvolution.RouteD.G2D4.map_twistedGroup_eq_graphFixedRootGroup p e hp2 he,
    twistedIncl, MonoidHom.range_comp, Subgroup.range_subtype]

theorem odd_natCard_of_two_ne_zero_td4 {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    Odd (Nat.card F) := by
  have hF : ringChar F ≠ 2 := by
    intro h
    apply h2
    have : CharP F 2 := ringChar.of_eq h
    exact_mod_cast CharP.cast_eq_zero F 2
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  exact Nat.odd_iff.2 (FiniteField.odd_card_of_char_ne_two hF)

end Facts

section Node

variable {p e : ℕ} [Fact p.Prime]

theorem noCommuting_node (hp2 : p ≠ 2) (he : 1 ≤ e) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) {i : Fin (Tag.rank .G2)}
    {Φ₀ : SL(2, F) →* twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)}
    (hΦ₀ : Function.Injective Φ₀)
    (hrange : rankOne (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i =
      Φ₀.range)
    (g₀ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) :
    conjSub g (conjSub g₀ Φ₀.range) ≠ conjSub g₀ Φ₀.range →
      ¬ Commutes (conjSub g₀ Φ₀.range) (conjSub g (conjSub g₀ Φ₀.range)) := by
  intro hne hcomm
  have hQ := (isUniqueInvolution_range_sl2 hodd hΦ₀).conj g₀
  have hJ := hQ.conj g
  set c₁ := g₀ * Φ₀ (-1) * g₀⁻¹ with hc₁
  have hperfA : ⁅Φ₀.range, Φ₀.range⁆ = Φ₀.range := by
    refine le_antisymm ((Subgroup.commutator_le).mpr fun x hx y hy => ?_)
      (CFSG.ClassicalInvolution.ModelFacts.fundPerfect_range_le_commutator
        (CFSG.ClassicalInvolution.sl2_isPerfect h4) Φ₀)
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hperf : ∀ n : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e),
      ⁅conjSub n Φ₀.range, conjSub n Φ₀.range⁆ = conjSub n Φ₀.range := fun n => by
    unfold conjSub
    rw [← Subgroup.map_commutator, hperfA]
  have hperfJ : ⁅conjSub g (conjSub g₀ Φ₀.range), conjSub g (conjSub g₀ Φ₀.range)⁆ =
      conjSub g (conjSub g₀ Φ₀.range) := by
    rw [← conjSub_mul]
    exact hperf _
  have hc12 : g * c₁ * g⁻¹ = c₁ :=
    CFSG.ClassicalInvolution.ModelFacts.trialityD4_eq_of_central_in_perfect p e hp2 he hperfJ
      hQ.sq hQ.ne_one hJ.ne_one hJ.mem (fun r hr => isUniqueInvolution_central hJ hr)
      (fun r hr => hcomm c₁ hQ.mem r hr)
  rw [hc12] at hJ
  rw [← hrange] at hQ hJ hne
  refine hne (conjSub_eq_of_nodes (sigma_three_td4 e he)
    (neg_one_ne_one_galoisField_td4 hp2 (3 * e)) (fun x => ?_) hQ hJ)
  rw [← range_twistedIncl_eq hp2 e he]
  exact ⟨x, rfl⟩

end Node

section Edge

variable {p e : ℕ} [Fact p.Prime]

theorem edge_of_chart (hp2 : p ≠ 2) (he : 1 ≤ e) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) {i : Fin (Tag.rank .G2)}
    {Φ₀ : SL(2, F) →* twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)}
    (hΦ₀ : Function.Injective Φ₀)
    (hrange : rankOne (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i =
      Φ₀.range)
    (H1₀ : ∀ x, x * Φ₀ (-1) = Φ₀ (-1) * x → LinAct Φ₀ x)
    (g₀ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))
    {R : Subgroup (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hRJ : R ≤ conjSub g (conjSub g₀ Φ₀.range)) (hR2 : IsPGroup 2 R)
    (hmax : ∀ T : Subgroup (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)),
      T ≤ conjSub g (conjSub g₀ Φ₀.range) → IsPGroup 2 T → R ≤ T → T = R)
    (hRN : R ≤ Subgroup.normalizer ((conjSub g₀ Φ₀.range : Subgroup _) : Set _)) :
    conjSub g (conjSub g₀ Φ₀.range) = conjSub g₀ Φ₀.range :=
  eq_of_sylow_le_normalizer_of_chart hodd h4 hΦ₀ H1₀ g₀ g
    (noCommuting_node hp2 he hodd h4 hΦ₀ hrange g₀ g) hRJ hR2 hmax hRN

theorem edge_node (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .trialityD4 0 p e)
    (i : Fin (Tag.rank .G2))
    (g₀ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))
    (h60 : 60 ≤ Nat.card (conjSub g₀ (rankOne (twistedRootGroup
      (iterateFrobenius (GaloisField p (3 * e)) p e)) i)))
    {R : Subgroup (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hRJ : R ≤ conjSub g (conjSub g₀ (rankOne (twistedRootGroup
      (iterateFrobenius (GaloisField p (3 * e)) p e)) i)))
    (hR2 : IsPGroup 2 R)
    (hmax : ∀ T : Subgroup (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)),
      T ≤ conjSub g (conjSub g₀ (rankOne (twistedRootGroup
        (iterateFrobenius (GaloisField p (3 * e)) p e)) i)) → IsPGroup 2 T → R ≤ T → T = R)
    (hRN : R ≤ Subgroup.normalizer ((conjSub g₀ (rankOne (twistedRootGroup
      (iterateFrobenius (GaloisField p (3 * e)) p e)) i) : Subgroup _) : Set _)) :
    conjSub g (conjSub g₀ (rankOne (twistedRootGroup
      (iterateFrobenius (GaloisField p (3 * e)) p e)) i)) =
      conjSub g₀ (rankOne (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i) := by
  have he : 1 ≤ e := hadm.2.1
  have hfin := finite_galoisField_three (p := p) e he
  have hσ := sigma_three_td4 (p := p) e he
  have hK1 := neg_one_ne_one_galoisField_td4 hp2 (3 * e)
  have hrange := range_twistedIncl_eq hp2 e he
  have hC₀ : graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
      (iterateFrobenius (GaloisField p (3 * e)) p e) ≤
      (twistedIncl (iterateFrobenius (GaloisField p (3 * e)) p e)).range := hrange.ge
  have hgF : ∀ g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e),
      twistedIncl (iterateFrobenius (GaloisField p (3 * e)) p e) g ∈
        graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * e))
          (iterateFrobenius (GaloisField p (3 * e)) p e) := fun g => hrange ▸ ⟨g, rfl⟩
  have h2K := two_ne_zero_galoisField_td4 hp2 (3 * e)
  have hcard : Nat.card (conjSub g₀ (rankOne (twistedRootGroup
      (iterateFrobenius (GaloisField p (3 * e)) p e)) i)) =
      Nat.card (rankOne (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) i) :=
    Subgroup.card_map_of_injective (MulAut.conj g₀).injective
  match i with
  | ⟨0, _⟩ =>
    have h2F : (2 : fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) ≠ 0 :=
      fun h => h2K (congrArg Subtype.val h)
    have hcl : Nat.card (rankOne (twistedRootGroup
        (iterateFrobenius (GaloisField p (3 * e)) p e)) (ng 0)) =
        p ^ e * ((p ^ e) ^ 2 - 1) :=
      natCard_rankOne_long 0 p e hadm
    have h4q : 4 ≤ p ^ e := by
      by_contra hlt
      have hlt : p ^ e < 4 := Nat.lt_of_not_le hlt
      rw [hcard, hcl] at h60
      interval_cases hpe : p ^ e <;> omega
    have h4 : 4 ≤ Nat.card (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) :=
      h4q.trans (ModelFacts.le_card_fixedField_iterateFrobenius he)
    have hrk := ModelFacts.rankOne_long_eq_range hσ
    rw [hrk] at hRJ hmax hRN ⊢
    exact edge_of_chart hp2 he (odd_natCard_of_two_ne_zero_td4 h2F) h4 (slLong_injective hσ) hrk
      (fun x hx => linAct_of_centralizes_long hσ hK1 h2F hC₀ hgF hx) g₀ g hRJ hR2 hmax hRN
  | ⟨1, _⟩ =>
    have hq2 : 2 ≤ p ^ e := by
      have := (Fact.out : p.Prime).two_le
      calc 2 ≤ p := this
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
    have h4 : 4 ≤ Nat.card (GaloisField p (3 * e)) := by
      rw [GaloisField.card p (3 * e) (by omega), pow_mul']
      exact four_le_pow_three hq2
    have hrk := ModelFacts.rankOne_short_eq_range hσ
    rw [hrk] at hRJ hmax hRN ⊢
    exact edge_of_chart hp2 he (odd_natCard_of_two_ne_zero_td4 h2K) h4 (slShort_injective hσ) hrk
      (fun x hx => linAct_of_centralizes_short hσ hK1 h2K hC₀ hgF hx) g₀ g hRJ hR2 hmax hRN

theorem eq_of_isMaxPGroup_le_normalizer_td4 (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .trialityD4 0 p e) :
    ∀ Q ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 0 p e Fact.out).D,
      60 ≤ Nat.card Q → ∀ g : (modelUniv .trialityD4 0 p e Fact.out).K,
        ∀ R : Subgroup (modelUniv .trialityD4 0 p e Fact.out).K,
          R ≤ conjSub g Q → IsPGroup 2 R →
          (∀ T : Subgroup (modelUniv .trialityD4 0 p e Fact.out).K,
            T ≤ conjSub g Q → IsPGroup 2 T → R ≤ T → T = R) →
          R ≤ Subgroup.normalizer (Q : Set (modelUniv .trialityD4 0 p e Fact.out).K) →
          conjSub g Q = Q := by
  intro Q hQ h60 g R hRJ hR2 hmax hRN
  obtain ⟨i, g₀, rfl⟩ := exists_conj_rankOne_node_of_trialityD4 0 p e hadm hQ
  exact edge_node hp2 hadm i g₀ g h60 hRJ hR2 hmax hRN

end Edge

end CFSG.ClassicalInvolution.G2D4Models
