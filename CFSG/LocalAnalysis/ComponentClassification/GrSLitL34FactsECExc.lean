module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenE6

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem card_fusionZStar_le {K : Type} [Group K] [Finite K] {α : MulAut K}
    (P : Subgroup (fixedSubgroup α)) : Nat.card (P ⧸ Open.fusionZStar P) ≤ Nat.card K := by
  calc Nat.card (P ⧸ Open.fusionZStar P) ≤ Nat.card P :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    _ ≤ Nat.card (fixedSubgroup α) := Subgroup.card_le_card_group P
    _ ≤ Nat.card K := Subgroup.card_le_card_group _

theorem cube_ne_G24 (q : ℕ) : q * (q ^ 2 - 1) ≠ 2 * 251596800 :=
  cube_ne (N := 795) (by norm_num) (by norm_num) q

theorem noOddPSL2_twistedE6
    {K : Type} [Group K] (hm : Blueprint.LieModel K .twistedE6 0 2 1) : NoOddPSL2 K := by
  intro α hα2 hαo P hP p m hp2 hL
  have htw : TwistedChevalleyModel K .E6 (2 ^ 1) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two le_rfl htw
  have : Finite (ModGL TwistTag.E6.tag M) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.E6 M σ.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨-, hF4⟩ :=
    even_twistedE6_outer_lieModel le_rfl hM σ hσ β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP
  exact not_psl2_of_card hp2 (fun q => (cube_ne_orders q).1) (card_F4_two hF4) hL

theorem noOddPSL2_F4
    {K : Type} [Group K] (hm : Blueprint.LieModel K .F4 0 2 1) : NoOddPSL2 K := by
  intro α hα2 hαo P hP p m hp2 hL
  have hu : UntwistedChevalleyModel K .F4 (2 ^ 1) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hu
  have : Finite (ModGL .F4 F) := finite_modGL
  have : Finite (ModGL ReeTag.F4.tag F) := finite_modGL
  have : Finite ↥(adjointGroup ReeTag.F4.tag F) := Subtype.finite
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .F4 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have : CharP F ReeTag.F4.prime := ‹CharP F 2›
  have hK := card_F4_two hm
  have hle := card_fusionZStar_le P
  rcases even_F4_outer_fixed le_rfl hF β hβ2 hβo with ⟨e', he', k, _, _, hk, ⟨Φ⟩⟩ | ⟨m', hfm, ⟨Φ⟩⟩
  · have : Finite (ModGL .F4 k) := finite_modGL
    have := (ExcSelector.adjointGroup_F4_even he' hk).1
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
      ((fixedSubgroupCongrEquiv e α).trans Φ) hP
    have hF4 := (lieModel_F4_of_mulEquiv he' hk E).2
    have hc := card_of_lieModel hF4
    simp only [lieOrderNumerator, lieOrderDivisor, mul_one] at hc
    rcases Nat.lt_or_ge e' 2 with he1 | he2
    · obtain rfl : e' = 1 := by omega
      exact not_psl2_of_card hp2 (fun q => (cube_ne_orders q).1) (by rw [hc]; norm_num) hL
    · exfalso
      have hq4 : 4 ≤ 2 ^ e' := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) he2)
      have h1 : ∀ j, 1 ≤ j → 1 ≤ (2 ^ e') ^ j - 1 := fun j hj => by
        have : 4 ≤ (2 ^ e') ^ j := le_trans hq4 (Nat.le_self_pow (by omega) _)
        omega
      have hbig : 4 ^ 24 * (4 ^ 12 - 1) ≤ Nat.card (↥P ⧸ Open.fusionZStar ↥P) := by
        rw [hc]
        calc 4 ^ 24 * (4 ^ 12 - 1) ≤ (2 ^ e') ^ 24 * ((2 ^ e') ^ 12 - 1) :=
              Nat.mul_le_mul (Nat.pow_le_pow_left hq4 24)
                (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq4 12) 1)
          _ ≤ (2 ^ e') ^ 24 * ((2 ^ e') ^ 12 - 1) * ((2 ^ e') ^ 8 - 1) * ((2 ^ e') ^ 6 - 1) *
              ((2 ^ e') ^ 2 - 1) := by
            refine Nat.le_mul_of_pos_right _ (h1 2 (by norm_num)) |>.trans' ?_
            refine Nat.le_mul_of_pos_right _ (h1 6 (by norm_num)) |>.trans' ?_
            exact Nat.le_mul_of_pos_right _ (h1 8 (by norm_num))
      rw [hK] at hle
      have := hbig.trans hle
      norm_num at this
  · obtain rfl : m' = 0 := by omega
    have hF2 : Nat.card F = 2 := by rw [hF]; rfl
    exact not_psl2_of_card hp2 (fun q => (cube_ne_orders q).2.1)
      (card_tits (lieModel_tits_of_isPComponent hF2 ((fixedSubgroupCongrEquiv e α).trans Φ) hP).2)
      hL

theorem noOddPSL2_G2
    {K : Type} [Group K] (hm : Blueprint.LieModel K .G2 0 2 2) : NoOddPSL2 K := by
  intro α hα2 hαo P hP p m hp2 hL
  have hu : UntwistedChevalleyModel K .G2 (2 ^ 2) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hu
  have : Finite (ModGL .G2 F) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .G2 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  have hK : Nat.card K = 251596800 := by
    have hc := card_of_lieModel hm
    simp only [lieOrderNumerator, lieOrderDivisor, mul_one] at hc
    rw [hc]
    norm_num
  have hle := card_fusionZStar_le P
  obtain ⟨e', he', k, _, _, hk, ⟨Φ⟩⟩ := even_G2_outer_fixed le_rfl hF β hβ2 hβo
  have : Finite (ModGL .G2 k) := finite_modGL
  set Ψ := (fixedSubgroupCongrEquiv e α).trans Φ
  rcases Nat.lt_or_ge e' 2 with he1 | he2
  · obtain rfl : e' = 1 := by omega
    have hk2 : Nat.card k = 2 := by simpa using hk
    have hL' := Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk2
    have hs : IsSimpleGroup ↥⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ := by
      rcases hL' with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact (ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 h).2
      all_goals exact absurd h (by norm_num)
    have hD : IsSimpleGroup (commutator ↥(adjointGroup .G2 k)) :=
      (commutatorSubtypeEquiv (adjointGroup .G2 k)).isSimpleGroup
    have hPeq := eq_commutator_of_isPComponent hD
      (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Ψ hP)
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP
      (((P.equivMapOfInjective Ψ.toMonoidHom Ψ.injective).trans
        (MulEquiv.subgroupCongr hPeq)).trans (commutatorSubtypeEquiv (adjointGroup .G2 k)))
    exact not_psl2_of_card hp2 (fun q => (cube_ne_orders q).2.2.1)
      (card_U33 (LieType.CurtisTits.lieModel_of_mulEquiv E.symm hL')) hL
  · have := (ExcSelector.adjointGroup_G2_even he' hk he2).1
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv Ψ hP
    have hG2 := (lieModel_G2_of_mulEquiv he2 hk E).2
    have hc := card_of_lieModel hG2
    simp only [lieOrderNumerator, lieOrderDivisor, mul_one] at hc
    rcases Nat.lt_or_ge e' 3 with he3 | he3
    · obtain rfl : e' = 2 := by omega
      exact not_psl2_of_card hp2 cube_ne_G24 (by rw [hc]; norm_num) hL
    · exfalso
      have hq8 : 8 ≤ 2 ^ e' := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) he3)
      have hbig : 8 ^ 6 * (8 ^ 6 - 1) ≤ Nat.card (↥P ⧸ Open.fusionZStar ↥P) := by
        rw [hc]
        have h2 : 1 ≤ (2 ^ e') ^ 2 - 1 := by
          have : 8 ≤ (2 ^ e') ^ 2 := le_trans hq8 (Nat.le_self_pow (by omega) _)
          omega
        calc 8 ^ 6 * (8 ^ 6 - 1) ≤ (2 ^ e') ^ 6 * ((2 ^ e') ^ 6 - 1) :=
              Nat.mul_le_mul (Nat.pow_le_pow_left hq8 6)
                (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq8 6) 1)
          _ ≤ (2 ^ e') ^ 6 * ((2 ^ e') ^ 6 - 1) * ((2 ^ e') ^ 2 - 1) :=
            Nat.le_mul_of_pos_right _ h2
      rw [hK] at hle
      have := hbig.trans hle
      norm_num at this

end CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover
