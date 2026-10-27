module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatOdd

public section

namespace CFSG.SeitzReduction.E8Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (ProperFixedComponent IsAltType
  GLS3OddLieAutComponentsInput)
open scoped Nat

theorem ordE7_two_pow_eq {f : ℕ} (hf : 1 ≤ f) :
    CFSG.Open.ordE7 (2 ^ f) = (2 ^ f) ^ 63 * (((2 ^ f) ^ 18 - 1) * (((2 ^ f) ^ 14 - 1) *
      (((2 ^ f) ^ 12 - 1) * (((2 ^ f) ^ 10 - 1) * (((2 ^ f) ^ 8 - 1) * (((2 ^ f) ^ 6 - 1) *
      ((2 ^ f) ^ 2 - 1))))))) := by
  rw [CFSG.Open.ordE7, Nat.coprime_two_left.mpr (Timmesfeld.Orders.odd_two_pow_sub_one (by omega)),
    Nat.div_one]
  ring

theorem two_pow_lt_factorial_e7 {f : ℕ} (hf : 1 ≤ f) : 2 ^ (133 * f + 1) < (63 * f + 2)! := by
  induction f, hf using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h1 : (63 * n + 2)! * (63 * n + 2 + 1) ^ 63 ≤ (63 * n + 2 + 63)! :=
      Nat.factorial_mul_pow_le_factorial
    have h2 : 2 ^ 133 ≤ (63 * n + 2 + 1) ^ 63 :=
      calc 2 ^ 133 ≤ 66 ^ 63 := by norm_num
        _ ≤ (63 * n + 2 + 1) ^ 63 := Nat.pow_le_pow_left (by omega) 63
    calc 2 ^ (133 * (n + 1) + 1) = 2 ^ (133 * n + 1) * 2 ^ 133 := by ring
      _ < (63 * n + 2)! * 2 ^ 133 := Nat.mul_lt_mul_of_pos_right ih (by positivity)
      _ ≤ (63 * n + 2)! * (63 * n + 2 + 1) ^ 63 := Nat.mul_le_mul_left _ h2
      _ ≤ (63 * n + 2 + 63)! := h1
      _ = (63 * (n + 1) + 2)! := by ring_nf

section Orders


theorem card_of_lieModel_E7_two_bounds {D : Type} [Group D] {n f : ℕ}
    (h : LieModel D .E7 n 2 f) : 1 ≤ f ∧ ∃ A : ℕ, 1 ≤ A ∧ A < (2 ^ f) ^ 70 ∧
      Nat.card D = (2 ^ f) ^ 63 * A := by
  have hf : 1 ≤ f := (F4Pilot.statedLieAdmissible_of_lieModel h).2.1
  refine ⟨hf, _, ?_, ?_, (card_of_lieModel_E7_two h).trans (ordE7_two_pow_eq hf)⟩
  all_goals
    set q := 2 ^ f with hq
    have hq2 : 2 ≤ q := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hpos : ∀ d : ℕ, 1 ≤ d → 1 ≤ q ^ d - 1 := fun d hd => by
      have : 2 ≤ q ^ d := hq2.trans (Nat.le_self_pow (by omega) q)
      omega
    have hlt : ∀ d : ℕ, q ^ d - 1 < q ^ d := fun d =>
      Nat.sub_lt (pow_pos (by omega : 0 < q) d) one_pos
  · have h18 := hpos 18 (by norm_num)
    have h14 := hpos 14 (by norm_num)
    have h12 := hpos 12 (by norm_num)
    have h10 := hpos 10 (by norm_num)
    have h8 := hpos 8 (by norm_num)
    have h6 := hpos 6 (by norm_num)
    have h2 := hpos 2 (by norm_num)
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · calc (q ^ 18 - 1) * ((q ^ 14 - 1) * ((q ^ 12 - 1) * ((q ^ 10 - 1) * ((q ^ 8 - 1) *
          ((q ^ 6 - 1) * (q ^ 2 - 1)))))) <
          q ^ 18 * (q ^ 14 * (q ^ 12 * (q ^ 10 * (q ^ 8 * (q ^ 6 * q ^ 2))))) := by
          refine Nat.mul_lt_mul'' (hlt 18) (Nat.mul_lt_mul'' (hlt 14) (Nat.mul_lt_mul'' (hlt 12)
            (Nat.mul_lt_mul'' (hlt 10) (Nat.mul_lt_mul'' (hlt 8)
              (Nat.mul_lt_mul'' (hlt 6) (hlt 2))))))
      _ = q ^ 70 := by ring

theorem two_pow_le_card_of_lieModel_E7_two {D : Type} [Group D] {n f : ℕ}
    (h : LieModel D .E7 n 2 f) : 2 ^ 63 ≤ Nat.card D := by
  obtain ⟨hf, A, hA, -, hD⟩ := card_of_lieModel_E7_two_bounds h
  rw [hD]
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  calc 2 ^ 63 ≤ (2 ^ f) ^ 63 := Nat.pow_le_pow_left hq 63
    _ = (2 ^ f) ^ 63 * 1 := (mul_one _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ hA

theorem card_of_lieModel_E7_two_ne {D : Type} [Group D] {n f : ℕ} (h : LieModel D .E7 n 2 f)
    {m : ℕ} (hm : 2 ≤ m) : Nat.card D ≠ m ! / 2 := by
  intro hcard
  obtain ⟨hf, A, -, hAlt, hD⟩ := card_of_lieModel_E7_two_bounds h
  set q := 2 ^ f with hq
  have h2 : 2 ∣ m ! := Nat.dvd_factorial (by norm_num) hm
  have hm! : m ! = 2 * (q ^ 63 * A) := by
    rw [← hD, hcard, Nat.mul_div_cancel' h2]
  have hdvd : 2 ^ (63 * f + 1) ∣ m ! := ⟨A, by rw [hm!, hq]; ring⟩
  have hlt : 63 * f + 1 < m := by
    have h1 := Nat.emultiplicity_two_factorial_lt (show m ≠ 0 by omega)
    have h2 := le_emultiplicity_of_pow_dvd hdvd
    exact_mod_cast lt_of_le_of_lt h2 h1
  have hfac : (63 * f + 2)! ≤ m ! := Nat.factorial_le (by omega)
  have hbig := two_pow_lt_factorial_e7 hf
  have hsmall : m ! < 2 ^ (133 * f + 1) := by
    rw [hm!]
    calc 2 * (q ^ 63 * A) < 2 * (q ^ 63 * q ^ 70) :=
          Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left hAlt (by positivity))
            (by norm_num)
      _ = 2 ^ (133 * f + 1) := by rw [hq]; ring
  omega

end Orders

section Clauses


theorem catE7Alternating : CatE7Alternating := by
  intro S _ _ _ _ ⟨n, hn, ⟨e⟩⟩ σ hσ f D hD hD7
  have hσ2 : σ ^ 2 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσσ : ∀ y, σ (σ y) = y := fun y => by
    have := congrArg (fun ψ : MulAut S => ψ y) hσ2
    simpa [pow_two] using this
  set P : Subgroup S := D.map (fixedSubgroup σ).subtype with hPdef
  have hPF : P ≤ fixedSubgroup σ := map_subtype_le D
  have hPsub : P.subgroupOf (fixedSubgroup σ) = D :=
    comap_map_eq_self_of_injective (fixedSubgroup σ).subtype_injective D
  have hPne : P ≠ ⊤ := by
    intro htop
    have hσ1 : σ = 1 := by
      ext y
      exact hPF (htop ▸ mem_top y)
    rw [hσ1, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hPC : ProperFixedComponent σ P :=
    ⟨hσσ, hPF, hPsub ▸ LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD, hPne⟩
  have hcardP : Nat.card P = Nat.card D :=
    card_map_of_injective (fixedSubgroup σ).subtype_injective
  have hdvdS : Nat.card D ∣ Nat.card S := hcardP ▸ card_subgroup_dvd_card P
  have hSn : Nat.card S = n ! / 2 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  by_cases hn6 : n = 6
  · subst hn6
    have h1 := Nat.le_of_dvd (by rw [hSn]; decide) hdvdS
    have h2 := two_pow_le_card_of_lieModel_E7_two hD7
    rw [hSn, show (6 : ℕ)! / 2 = 360 by decide] at h1
    have h3 : (360 : ℕ) < 2 ^ 63 := by norm_num
    omega
  ·
    set L := P.subgroupOf (fixedSubgroup σ) with hLdef
    let eLD : L ≃* D := MulEquiv.subgroupCongr hPsub
    have hsD : IsSimpleGroup D := isSimpleGroup_of_lieModel_E7 hD7
    have hsL : IsSimpleGroup L := eLD.isSimpleGroup
    have hqL : IsQuasisimple L := (LocalAnalysis.ComponentInitial.isQuasisimple_congr eLD).2 hD.1
    have hZL : center L = ⊥ := F4Pilot.center_eq_bot_of_isQuasisimple hqL hsL
    obtain ⟨-, ⟨eZ⟩⟩ := hPC.fusionZStar_equiv_of_quasisimple hqL
    let eP : P ⧸ Open.fusionZStar P ≃* D :=
      (eZ.trans ((QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot)).trans
        eLD
    obtain ⟨hPC', ⟨eT⟩⟩ := hPC.map e
    have hAlt := CFSG.ComponentClassification.CatLeaf.isAltType_of_properFixedComponent_alternating
      hn hn6 hPC'
    obtain ⟨Ω, _, _, hΩ, ⟨eA⟩⟩ := IsAltType.of_mulEquiv (eP.symm.trans eT) hAlt
    have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    apply card_of_lieModel_E7_two_ne hD7 (m := Fintype.card Ω) (by omega)
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card]

@[expose] def E7NotOddLieInput : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), LieModel X .E7 0 2 f → ¬ OddLieType X

theorem catE7OddLie_of_inputs (hGLS : GLS3OddLieAutComponentsInput) (hX : E7NotOddLieInput) :
    CatE7OddLie := by
  intro S _ _ _ _ hodd σ hσ f D hD hD7
  obtain ⟨t, n, p, e, hp, hp2, hadm, hm⟩ := hodd
  have hZD : center D = ⊥ := center_eq_bot_of_lieModel_E7 hD.1 hD7
  rcases hGLS S t n p e hp hp2 hadm hm σ hσ D hD with ⟨τ', n', f', hadm', hm'⟩ | ⟨-, -, -, hL⟩
  · exact hX D f hD7 ⟨τ', n', p, f', hp, hp2, hadm',
      LieType.CurtisTits.lieModel_of_mulEquiv (F4Pilot.mulEquivCenterQuotient hZD) hm'⟩
  · have h1 := F4Pilot.card_of_lieModel_PSL_two_two_three hL
    have h2 := two_pow_le_card_of_lieModel_E7_two hD7
    rw [h1] at h2
    norm_num at h2

end Clauses

end CFSG.SeitzReduction.E8Pilot
