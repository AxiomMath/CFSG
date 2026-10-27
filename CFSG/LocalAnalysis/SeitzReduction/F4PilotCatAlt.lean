module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatCovers
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (ProperFixedComponent IsAltType)
open scoped Nat

theorem card_of_lieModel_PSp_three_two {D : Type} [Group D] {f : ℕ}
    (h : LieModel D .PSp 3 2 f) :
    Nat.card D = (2 ^ f) ^ 9 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)) := by
  have hcl := statedClassicalModel_of_lieModel_psp h
  have hf : 1 ≤ f := hcl.1.2.1
  have hgcd : Nat.gcd 2 (2 ^ f - 1) = 1 := by
    apply Nat.coprime_two_left.mpr
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  rw [(Timmesfeld.card_statedClassicalModel_two hcl).2.2.1 rfl, Open.ordBC, hgcd, Nat.div_one,
    show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide]
  simp [mul_assoc]

theorem two_pow_lt_factorial {f : ℕ} (hf : 1 ≤ f) : 2 ^ (21 * f + 1) < (9 * f + 2)! := by
  induction f, hf using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h1 : (9 * n + 2)! * (9 * n + 2 + 1) ^ 9 ≤ (9 * n + 2 + 9)! :=
      Nat.factorial_mul_pow_le_factorial
    have h2 : 2 ^ 21 ≤ (9 * n + 2 + 1) ^ 9 :=
      calc 2 ^ 21 ≤ 12 ^ 9 := by norm_num
        _ ≤ (9 * n + 2 + 1) ^ 9 := Nat.pow_le_pow_left (by omega) 9
    calc 2 ^ (21 * (n + 1) + 1) = 2 ^ (21 * n + 1) * 2 ^ 21 := by ring
      _ < (9 * n + 2)! * 2 ^ 21 := Nat.mul_lt_mul_of_pos_right ih (by positivity)
      _ ≤ (9 * n + 2)! * (9 * n + 2 + 1) ^ 9 := Nat.mul_le_mul_left _ h2
      _ ≤ (9 * n + 2 + 9)! := h1
      _ = (9 * (n + 1) + 2)! := by ring_nf

theorem two_pow_nine_le_card_of_lieModel_PSp_three_two {D : Type} [Group D] {f : ℕ}
    (h : LieModel D .PSp 3 2 f) : 2 ^ 9 ≤ Nat.card D := by
  have hf : 1 ≤ f := (statedClassicalModel_of_lieModel_psp h).1.2.1
  rw [card_of_lieModel_PSp_three_two h]
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hA : 1 ≤ ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1) := by
    have h2 : 2 ≤ (2 ^ f) ^ 2 := le_trans hq (Nat.le_self_pow (by norm_num) _)
    have h4 : 2 ≤ (2 ^ f) ^ 4 := le_trans hq (Nat.le_self_pow (by norm_num) _)
    have h6 : 2 ≤ (2 ^ f) ^ 6 := le_trans hq (Nat.le_self_pow (by norm_num) _)
    have : 1 ≤ (2 ^ f) ^ 2 - 1 := by omega
    have : 1 ≤ (2 ^ f) ^ 4 - 1 := by omega
    have : 1 ≤ (2 ^ f) ^ 6 - 1 := by omega
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc 2 ^ 9 ≤ (2 ^ f) ^ 9 := Nat.pow_le_pow_left hq 9
    _ = (2 ^ f) ^ 9 * 1 := (mul_one _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ hA

theorem card_of_lieModel_PSp_three_two_ne {D : Type} [Group D] {f : ℕ}
    (h : LieModel D .PSp 3 2 f) {m : ℕ} (hm : 2 ≤ m) : Nat.card D ≠ m ! / 2 := by
  intro hcard
  have hf : 1 ≤ f := (statedClassicalModel_of_lieModel_psp h).1.2.1
  have hD := card_of_lieModel_PSp_three_two h
  set q := 2 ^ f with hq
  set A := (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) with hA
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hAlt : A < q ^ 12 := by
    have h1 : q ^ 2 - 1 < q ^ 2 := Nat.sub_lt (by positivity) one_pos
    have h2 : q ^ 4 - 1 < q ^ 4 := Nat.sub_lt (by positivity) one_pos
    have h3 : q ^ 6 - 1 < q ^ 6 := Nat.sub_lt (by positivity) one_pos
    calc A = (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) := rfl
      _ < q ^ 2 * q ^ 4 * q ^ 6 := Nat.mul_lt_mul'' (Nat.mul_lt_mul'' h1 h2) h3
      _ = q ^ 12 := by ring
  have h2 : 2 ∣ m ! := Nat.dvd_factorial (by norm_num) hm
  have hm! : m ! = 2 * (q ^ 9 * A) := by
    rw [← hD, hcard, Nat.mul_div_cancel' h2]
  have hdvd : 2 ^ (9 * f + 1) ∣ m ! := ⟨A, by rw [hm!, hq]; ring⟩
  have hlt : 9 * f + 1 < m := by
    have h1 := Nat.emultiplicity_two_factorial_lt (show m ≠ 0 by omega)
    have h2 := le_emultiplicity_of_pow_dvd hdvd
    exact_mod_cast lt_of_le_of_lt h2 h1
  have hfac : (9 * f + 2)! ≤ m ! := Nat.factorial_le (by omega)
  have hbig := two_pow_lt_factorial hf
  have hsmall : m ! < 2 ^ (21 * f + 1) := by
    rw [hm!]
    calc 2 * (q ^ 9 * A) < 2 * (q ^ 9 * q ^ 12) :=
          Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left hAlt (by positivity))
            (by norm_num)
      _ = 2 ^ (21 * f + 1) := by rw [hq]; ring
  omega

theorem catSp6Alternating : CatSp6Alternating := by
  intro S _ _ _ _ ⟨n, hn, ⟨e⟩⟩ σ hσ f D hD hD6
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
    have h2 := two_pow_nine_le_card_of_lieModel_PSp_three_two hD6
    rw [hSn] at h1
    have : (6 : ℕ)! / 2 = 360 := by decide
    omega
  ·
    set L := P.subgroupOf (fixedSubgroup σ) with hLdef
    let eLD : L ≃* D := MulEquiv.subgroupCongr hPsub
    have hsD : IsSimpleGroup D := isSimpleGroup_of_lieModel_PSp hD6
    have hsL : IsSimpleGroup L := eLD.isSimpleGroup
    have hqL : IsQuasisimple L := (LocalAnalysis.ComponentInitial.isQuasisimple_congr eLD).2 hD.1
    have hZL : center L = ⊥ := center_eq_bot_of_isQuasisimple hqL hsL
    obtain ⟨-, ⟨eZ⟩⟩ := hPC.fusionZStar_equiv_of_quasisimple hqL
    let eP : P ⧸ Open.fusionZStar P ≃* D :=
      (eZ.trans ((QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot)).trans
        eLD
    obtain ⟨hPC', ⟨eT⟩⟩ := hPC.map e
    have hAlt := CFSG.ComponentClassification.CatLeaf.isAltType_of_properFixedComponent_alternating
      hn hn6 hPC'
    obtain ⟨Ω, _, _, hΩ, ⟨eA⟩⟩ := IsAltType.of_mulEquiv (eP.symm.trans eT) hAlt
    have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    apply card_of_lieModel_PSp_three_two_ne hD6 (m := Fintype.card Ω) (by omega)
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card]

end CFSG.SeitzReduction.F4Pilot
