module

public import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListDefs
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListLieModels
import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListRank
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace GL83.I243.CoverList

open TauCeti CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.Open (GriessAllModelsStatement)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (genericOrders_fst_pos genericOrders_snd_le
  genericOrders_fst_le_four exceptionalOrders_le center_torsion_le center_dvd_table torsBound
  torsBound_le_of_five_le eq_psu_four_three_of_nine_le tors lieModel_typeA)
open CFSG.AGLEmbeddingD2 (IsD2SeitzException)

theorem isQuasisimple_of_open {K : Type} [Group K] (hq : CFSG.Open.IsQuasisimple K) :
    CFSG.IsQuasisimple K :=
  ⟨⟨hq.1⟩, hq.2,
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq⟩

theorem torsion_center_le_sq (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {d : ValidLieTypeIndex}
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : Nat.card {z : Subgroup.center K // z ^ p = 1} ≤ p ^ 2 := by
  obtain ⟨t, n, p0, f, hm, -⟩ := exists_lieModel_spec d
  refine (center_torsion_le hGA hq e hm hp).trans ?_
  by_cases hp5 : 5 ≤ p
  · exact (torsBound_le_of_five_le hp5 t n p0 f).trans (Nat.le_self_pow two_ne_zero p)
  · rcases (show p = 3 ∨ p = 4 by have := hp.two_le; omega) with rfl | rfl
    · by_cases h9 : 9 ≤ torsBound 3 t n p0 f
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := eq_psu_four_three_of_nine_le h9
        simp [torsBound, genericOrders, exceptionalOrders, tors]
      · omega
    · exact absurd hp (by norm_num)

theorem ne_of_dvd_pow_sub_one {p p0 f : ℕ} (hp : p.Prime) (hf : 0 < f) (h : p ∣ p0 ^ f - 1) :
    p ≠ p0 := by
  rintro rfl
  have h1 : p ∣ p ^ f := dvd_pow_self p hf.ne'
  have h2 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have h3 : p ∣ 1 := by
    have := Nat.dvd_sub h1 h
    rwa [Nat.sub_sub_self h2] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 h3)

theorem ne_of_dvd_pow_add_one {p p0 f : ℕ} (hp : p.Prime) (hf : 0 < f) (h : p ∣ p0 ^ f + 1) :
    p ≠ p0 := by
  rintro rfl
  have h1 : p ∣ p ^ f := dvd_pow_self p hf.ne'
  exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 h))

theorem ge_five_cases {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {t : StatedLieTag} {n p0 f : ℕ}
    (hadm : StatedLieAdmissible t n p0 f)
    (h : p ∣ (genericOrders t n p0 f).1 * (genericOrders t n p0 f).2 *
      ((exceptionalOrders t n p0 f).1 * (exceptionalOrders t n p0 f).2)) :
    (t = .PSL ∧ p ∣ p0 ^ f - 1) ∨ (t = .PSU ∧ p ∣ p0 ^ f + 1) := by
  have hnd : ∀ x : ℕ, 0 < x → x ≤ 4 → ¬ p ∣ x := fun x h0 h4 hd => by
    have := Nat.le_of_dvd h0 hd
    omega
  obtain ⟨hb1, hb2⟩ := genericOrders_snd_le t n p0 f
  obtain ⟨⟨hc1, hc2⟩, ⟨hd1, hd2⟩⟩ := exceptionalOrders_le t n p0 f
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · by_cases hL : t = .PSL
      · subst hL
        exact Or.inl ⟨rfl, h.trans (Nat.gcd_dvd_right _ _)⟩
      by_cases hU : t = .PSU
      · subst hU
        exact Or.inr ⟨rfl, h.trans (Nat.gcd_dvd_right _ _)⟩
      exact (hnd _ (genericOrders_fst_pos hadm) (genericOrders_fst_le_four hL hU n p0 f) h).elim
    · exact (hnd _ hb1 (by omega) h).elim
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact (hnd _ hc1 hc2 h).elim
    · exact (hnd _ hd1 hd2 h).elim

theorem isD2SeitzException_shape {p : ℕ} {d : LieTypeIndex} (h : IsD2SeitzException p d) :
    (∃ (r : ℕ) (q : PrimePower), d = .A r q) ∨ (∃ (r : ℕ) (q : PrimePower), d = .twistedA r q) ∨
      (∃ (r : ℕ) (q : PrimePower), d = .B r q) ∨ d = .tits ∨ ∃ m : ℕ, d = .suzuki m := by
  rcases h with ⟨-, ⟨q, -, -, rfl⟩ | ⟨q, -, -, rfl⟩ | ⟨q, -, -, rfl⟩ | ⟨q, -, -, rfl | rfl⟩ | rfl⟩ |
    ⟨-, rfl | rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))

theorem isPCoverLieIndex_ge_five (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (d : ValidLieTypeIndex)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) : IsPCoverLieIndex p d.1 := by
  have hq' := isQuasisimple_of_open hq
  by_cases hA : ∃ (r : ℕ) (q : PrimePower), d.1 = .A r q
  · obtain ⟨r, q, hd⟩ := hA
    have hv : (LieTypeIndex.A r q).Valid := by rw [← hd]; exact d.2
    obtain rfl : d = ⟨.A r q, hv⟩ := Subtype.ext hd
    have h := hpZ.trans (center_dvd_table hGA hq' e (lieModel_typeA r q hv))
    rcases ge_five_cases hp hp5 (lieModel_typeA r q hv).1 h with ⟨-, h1⟩ | ⟨ht, -⟩
    · exact Or.inl ⟨r, q, rfl, by rw [PrimePower.card_def]; exact h1⟩
    · cases ht
  by_cases hU : ∃ (r : ℕ) (q : PrimePower), d.1 = .twistedA r q
  · obtain ⟨r, q, hd⟩ := hU
    have hv : (LieTypeIndex.twistedA r q).Valid := by rw [← hd]; exact d.2
    obtain rfl : d = ⟨.twistedA r q, hv⟩ := Subtype.ext hd
    have hm := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _))
    have h := hpZ.trans (center_dvd_table hGA hq' e hm)
    rcases ge_five_cases hp hp5 hm.1 h with ⟨ht, -⟩ | ⟨-, h1⟩
    · cases ht
    · exact Or.inr (Or.inl ⟨r, q, rfl, by rw [PrimePower.card_def]; exact h1⟩)
  exfalso
  obtain ⟨t, n, p0, f, hm, -, -, hA', hU'⟩ := exists_lieModel_spec d
  have h := hpZ.trans (center_dvd_table hGA hq' e hm)
  rcases ge_five_cases hp hp5 hm.1 h with ⟨ht, -⟩ | ⟨ht, -⟩
  · obtain ⟨r, q, hd⟩ := hA' ht
    exact hA ⟨r, q, hd⟩
  · obtain ⟨r, q, hd⟩ := hU' ht
    exact hU ⟨r, q, hd⟩

theorem lie_ge_five (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (d : ValidLieTypeIndex)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) :
    p ≠ d.1.characteristic ∧ ¬ IsD2SeitzException p d.1 ∧ IsPCoverLieIndex p d.1 := by
  obtain ⟨t, n, p0, f, hm, hp0, hf, hA, hU⟩ := exists_lieModel_spec d
  have hq' := isQuasisimple_of_open hq
  have h := hpZ.trans (center_dvd_table hGA hq' e hm)
  have hnot : ¬ IsD2SeitzException p d.1 := by
    intro hex
    have hp3 : p ≠ 3 := by omega
    have hp5' : p = 5 := by
      rcases hex with ⟨h3, -⟩ | ⟨h5, -⟩
      · exact absurd h3 hp3
      · exact h5
    have hex' : IsD2SeitzException 5 d.1 := hp5' ▸ hex
    rcases ge_five_cases hp hp5 hm.1 h with ⟨ht, -⟩ | ⟨ht, -⟩
    · obtain ⟨r, q, hd⟩ := hA ht
      rcases hex' with ⟨h3, -⟩ | ⟨-, hd' | hd'⟩
      · omega
      · rw [hd] at hd'
        nomatch hd'
      · rw [hd] at hd'
        nomatch hd'
    · obtain ⟨r, q, hd⟩ := hU ht
      rcases hex' with ⟨h3, -⟩ | ⟨-, hd' | hd'⟩
      · omega
      · rw [hd] at hd'
        nomatch hd'
      · rw [hd] at hd'
        nomatch hd'
  refine ⟨?_, hnot, isPCoverLieIndex_ge_five hGA hq d e hp hp5 hpZ⟩
  rw [← hp0]
  rcases ge_five_cases hp hp5 hm.1 h with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact ne_of_dvd_pow_sub_one hp hf h1
  · exact ne_of_dvd_pow_add_one hp hf h1

theorem three_dvd_card {q : PrimePower} (h : q.p = 3) : 3 ∣ q.card := by
  rw [PrimePower.card_def, h]
  exact dvd_pow_self 3 q.exponent_pos.ne'

theorem card_pos (q : PrimePower) : 0 < q.card := by
  rw [PrimePower.card_def]
  exact pow_pos q.prime_p.pos _

theorem three_ne_p_of_dvd_pred {q : PrimePower} (h : 3 ∣ q.card - 1) : 3 ≠ q.p := by
  intro h3
  have := three_dvd_card h3.symm
  have := card_pos q
  omega

theorem three_ne_p_of_dvd_succ {q : PrimePower} (h : 3 ∣ q.card + 1) : 3 ≠ q.p := by
  intro h3
  have := three_dvd_card h3.symm
  omega

theorem isThreeCoverIndex_twistedA {q : PrimePower} (hv : (LieTypeIndex.twistedA 3 q).Valid)
    (hq : q.card = 3) : GL83.I243.IsThreeCoverIndex (.lie ⟨.twistedA 3 q, hv⟩) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hv, hq, rfl⟩))))))

theorem isThreeCoverIndex_B {q : PrimePower} (hv : (LieTypeIndex.B 3 q).Valid)
    (hq : q.card = 3) : GL83.I243.IsThreeCoverIndex (.lie ⟨.B 3 q, hv⟩) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hv, hq, rfl⟩)))))))

theorem isThreeCoverIndex_G2 {q : PrimePower} (hv : (LieTypeIndex.G2 q).Valid)
    (hq : q.card = 3) : GL83.I243.IsThreeCoverIndex (.lie ⟨.G2 q, hv⟩) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, hv, hq, rfl⟩)))))))

theorem lie_three (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (d : ValidLieTypeIndex)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group)
    (h3 : 3 ∣ Nat.card (Subgroup.center K)) :
    (3 ≠ d.1.characteristic ∧ ¬ IsD2SeitzException 3 d.1 ∧ IsPCoverLieIndex 3 d.1) ∨
      GL83.I243.IsThreeCoverIndex (.lie d) ∨
      (GL83.I243.IsThreeLFourIndex (.lie d) ∧ ¬ 3 ^ 2 ∣ Nat.card (Subgroup.center K)) := by
  have hq' := isQuasisimple_of_open hq
  have htc := CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverLie_of_griess hGA d K ⟨hq', h3, ⟨e⟩⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    obtain ⟨h1, h2⟩ := htc
    by_cases hex : IsD2SeitzException 3 (.A r q)
    · rcases hex with ⟨-, ⟨q', -, -, hd⟩ | ⟨q', hq2, hqe, hd⟩ | ⟨q', -, -, hd⟩ |
        ⟨q', -, -, hd | hd⟩ | hd⟩ | ⟨h5, -⟩
      · obtain ⟨rfl, -⟩ := LieTypeIndex.A.inj hd
        omega
      · obtain ⟨rfl, rfl⟩ := LieTypeIndex.A.inj hd
        refine Or.inr (Or.inr ⟨⟨⟨.A 2 q, hv⟩, rfl, q, hq2, hqe, rfl⟩, ?_⟩)
        have hdiv := center_dvd_table hGA hq' e (lieModel_typeA 2 q hv)
        rw [hq2, hqe] at hdiv
        have h48 : Nat.card (Subgroup.center K) ∣ 48 := by
          simpa [genericOrders, exceptionalOrders] using hdiv
        intro h9
        have := h9.trans h48
        omega
      · nomatch hd
      · nomatch hd
      · nomatch hd
      · nomatch hd
      · omega
    · exact Or.inl
        ⟨by simpa [LieTypeIndex.characteristic_A] using three_ne_p_of_dvd_pred h2, hex,
          Or.inl ⟨r, q, rfl, h2⟩⟩
  | twistedA r q =>
    rcases htc with ⟨h1, h2⟩ | ⟨rfl, hq3⟩
    · refine Or.inl ⟨by simpa [LieTypeIndex.characteristic_twistedA] using
        three_ne_p_of_dvd_succ h2, fun hex => ?_, Or.inr (Or.inl ⟨r, q, rfl, h2⟩)⟩
      rcases hex with ⟨-, ⟨q', -, -, hd⟩ | ⟨q', -, -, hd⟩ | ⟨q', -, -, hd⟩ |
        ⟨q', -, -, hd | hd⟩ | hd⟩ | ⟨h5, -⟩
      · nomatch hd
      · nomatch hd
      · obtain ⟨rfl, -⟩ := LieTypeIndex.twistedA.inj hd
        omega
      · nomatch hd
      · nomatch hd
      · nomatch hd
      · omega
    · exact Or.inr (Or.inl (isThreeCoverIndex_twistedA hv hq3))
  | B r q =>
    obtain ⟨rfl, hq3⟩ := htc
    exact Or.inr (Or.inl (isThreeCoverIndex_B hv hq3))
  | G2 q => exact Or.inr (Or.inl (isThreeCoverIndex_G2 hv htc))
  | E6 q =>
    refine Or.inl ⟨by simpa [LieTypeIndex.characteristic_E6] using
      three_ne_p_of_dvd_pred htc, fun hex => ?_, Or.inr (Or.inr ⟨rfl, Or.inl ⟨q, rfl⟩⟩)⟩
    rcases isD2SeitzException_shape hex with
      ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | hd | ⟨_, hd⟩ <;> nomatch hd
  | twistedE6 q =>
    refine Or.inl ⟨by simpa [LieTypeIndex.characteristic_twistedE6] using
      three_ne_p_of_dvd_succ htc, fun hex => ?_, Or.inr (Or.inr ⟨rfl, Or.inr ⟨q, rfl⟩⟩)⟩
    rcases isD2SeitzException_shape hex with
      ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | hd | ⟨_, hd⟩ <;> nomatch hd
  | C r q => exact htc.elim
  | D r q => exact htc.elim
  | twistedD r q => exact htc.elim
  | E7 q => exact htc.elim
  | E8 q => exact htc.elim
  | F4 q => exact htc.elim
  | trialityD4 q => exact htc.elim
  | suzuki m => exact htc.elim
  | reeG2 m => exact htc.elim
  | reeF4 m => exact htc.elim
  | tits => exact htc.elim

theorem lie_rank (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (d : ValidLieTypeIndex)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) :
    CFSG.Open.pRank p (Subgroup.center K) ≤ 2 :=
  pRank_center_le_two_of_torsion hp.one_lt (torsion_center_le_sq hGA hq e hp hp2)

theorem lie_case (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) (d : ValidLieTypeIndex)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) :
    (p ≠ d.1.characteristic ∧ ¬ IsD2SeitzException p d.1 ∧ IsPCoverLieIndex p d.1) ∨
      (p = 3 ∧ (GL83.I243.IsThreeCoverIndex (.lie d) ∨
        (GL83.I243.IsThreeLFourIndex (.lie d) ∧ ¬ 3 ^ 2 ∣ Nat.card (Subgroup.center K)))) := by
  by_cases hp3 : p = 3
  · subst hp3
    rcases lie_three hGA hq d e hpZ with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, Or.inl h⟩
    · exact Or.inr ⟨rfl, Or.inr h⟩
  · have hp5 : 5 ≤ p := by
      rcases (show p = 4 ∨ 5 ≤ p by have := hp.two_le; omega) with rfl | h
      · exact absurd hp (by norm_num)
      · exact h
    exact Or.inl (lie_ge_five hGA hq d e hp hp5 hpZ)

end GL83.I243.CoverList
