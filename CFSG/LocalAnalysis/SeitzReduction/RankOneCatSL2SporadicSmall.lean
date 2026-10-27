module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2SporadicBasic
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34Small
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.PairMcLOut
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy transportAut
  transportAut_mul_self transportAut_not_mem_inner fixSubTransportEquiv mem_inner_of_mulEquiv
  compsSatisfy_centralizer_of_mulEquiv isoInvariant_not_three_dvd isoInvariant_card_dvd
  isoInvariant_card_quotient_center compsSatisfy_of_isQuasisimple)
open CFSG.SeitzReduction.SporadicRefine (orderOf_eq_two_of_conj_of_simple
  fixedSubgroup_conj_eq_centralizerOf fixedSubgroup_eq_fixSub' nonempty_quotient_center_map_equiv)

section M11


theorem autTwoBound_M11 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .M11) {n : ℕ}
    (hn : 2 ≤ n) : AutTwoBound J n :=
  autTwoBound_of_mulEquiv hJ hna e (a := 4) (u := 495) (k := 2) (by decide)
    (Sporadic.Mathieu.card_M11.trans (by norm_num)) Sporadic.Schreier.at_m11_schreier.1
    (lt_two_mul_pow_four_of_le hn (by norm_num))

end M11

section M12


theorem autTwoBound_M12 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .M12) {n : ℕ}
    (hn : 2 ≤ n) : AutTwoBound J n :=
  autTwoBound_of_mulEquiv hJ hna e (a := 6) (u := 1485) (k := 4) (by decide)
    (Sporadic.Mathieu.card_M12.trans (by norm_num)) Sporadic.Schreier.at_m12_schreier.1
    (lt_two_mul_pow_four_of_le hn (by norm_num))

end M12

section J1


theorem autTwoBound_J1 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .J1) {n : ℕ}
    (hn : 2 ≤ n) : AutTwoBound J n :=
  autTwoBound_of_mulEquiv hJ hna e (a := 3) (u := 21945) (k := 1) (by decide)
    (Sporadic.J1.card_J1.trans (by norm_num)) Sporadic.Schreier.at_j1_schreier.1.le
    (lt_two_mul_pow_four_of_le hn (by norm_num))

end J1

section J2


theorem autTwoBound_J2 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .J2) {n : ℕ}
    (hn : 2 ≤ n) : AutTwoBound J n :=
  autTwoBound_of_mulEquiv hJ hna e (a := 7) (u := 4725) (k := 2) (by decide)
    (Sporadic.J2.card_J2.trans (by norm_num)) Sporadic.Schreier.AT_J2_Schreier.1
    (lt_two_mul_pow_four_of_le hn (by norm_num))

end J2

section J3


theorem autTwoBound_J3 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .J3) {n : ℕ}
    (hn : 2 ≤ n) : AutTwoBound J n :=
  autTwoBound_of_mulEquiv hJ hna e (a := 7) (u := 392445) (k := 2) (by decide)
    (Sporadic.J3.card_J3.trans (by norm_num))
    (Sporadic.Schreier.outer_card_le_of_equiv Sporadic.SmallOddCore.j3_outer_card_le
      Sporadic.Schreier.j3PermEquiv)
    (lt_two_mul_pow_four_of_le hn (by norm_num))

end J3

section McL


theorem autTwoBound_McL {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .McL) {n : ℕ}
    (hn : 2 ≤ n) : AutTwoBound J n :=
  autTwoBound_of_mulEquiv hJ hna e (a := 7) (u := 7016625) (k := 2) (by decide)
    (Sporadic.McL.card_McL.trans (by norm_num)) Sporadic.Schreier.McL_outer_card_le_two.1
    (lt_two_mul_pow_four_of_le hn (by norm_num))

end McL

section M22


theorem catSL2Hyp_false_M22 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.M22) {τ : MulAut J} {n : ℕ}
    (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, hDm, -⟩ := h
  have hn := two_le_of_lieModel_PSL_two_two hDm
  by_cases hin : τ ∈ (MulAut.conj : J →* MulAut J).range
  · obtain ⟨s, rfl⟩ := hin
    have hs := orderOf_eq_two_of_conj_of_simple hJ hna hτ
    let φ := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)
    have h : Nat.card (D.map φ.toMonoidHom) ∣ 384 :=
      compsSatisfy_centralizer_of_mulEquiv NativeSporadic.M22 (isoInvariant_card_dvd 384)
        ComponentClassification.RestrictedStd.Spor.m22_centralizerIn_comps e s hs _
        (LocalCores.isComponent_map_mulEquiv φ hD)
    rw [card_map_of_injective φ.injective] at h
    have h2 : Open.ordA 1 (2 ^ n) ∣ 384 := by
      rw [← card_of_lieModel_PSL_two_two hDm]
      exact (card_quotient_dvd_card _).trans h
    exact not_ordA_one_dvd_of_check (B := 9) hn (by norm_num) (by norm_num) (by decide) h2
  · have hσ2 : τ * τ = 1 := by rw [← sq, ← hτ, pow_orderOf_eq_one]
    let φ := (MulEquiv.subgroupCongr (fixedSubgroup_eq_fixSub' τ)).trans
      (fixSubTransportEquiv e τ)
    have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
      ComponentClassification.RestrictedStd.Spor.m22_outer_comps (transportAut e τ)
        (transportAut_mul_self e hσ2) (transportAut_not_mem_inner e hin) _
        (LocalCores.isComponent_map_mulEquiv φ hD)
    rw [card_map_of_injective φ.injective] at h
    exact h (three_dvd_card_of_lieModel hDm)

end M22

section M23


theorem catSL2Hyp_false_M23 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.M23) {τ : MulAut J} {n : ℕ}
    (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, hDm, -⟩ := h
  obtain ⟨s, rfl⟩ := mem_inner_of_mulEquiv e (fun β => by
    obtain ⟨h, hh⟩ := QuasithinUnique.Ch1.m23_all_inner β
    exact ⟨h, hh.symm⟩) τ
  have hs := orderOf_eq_two_of_conj_of_simple hJ hna hτ
  let φ := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)
  have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
    compsSatisfy_centralizer_of_mulEquiv NativeSporadic.M23 isoInvariant_not_three_dvd
      ComponentClassification.RestrictedStd.Spor.m23_centralizerIn_comps e s hs _
      (LocalCores.isComponent_map_mulEquiv φ hD)
  rw [card_map_of_injective φ.injective] at h
  exact h (three_dvd_card_of_lieModel hDm)

end M23

section M24


theorem catSL2Hyp_false_M24 {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.M24) {τ : MulAut J} {n : ℕ}
    (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, hDm, -⟩ := h
  obtain ⟨s, rfl⟩ := mem_inner_of_mulEquiv e (fun β => by
    obtain ⟨h, hh⟩ := QuasithinUnique.Ch1.m24_all_inner β
    exact ⟨h, hh.symm⟩) τ
  have hs := orderOf_eq_two_of_conj_of_simple hJ hna hτ
  let φ := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)
  have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
    compsSatisfy_centralizer_of_mulEquiv NativeSporadic.M24 isoInvariant_not_three_dvd
      ComponentClassification.RestrictedStd.Spor.m24_centralizerIn_comps e s hs _
      (LocalCores.isComponent_map_mulEquiv φ hD)
  rw [card_map_of_injective φ.injective] at h
  exact h (three_dvd_card_of_lieModel hDm)

end M24

section Ru


theorem catSL2Hyp_false_Ru {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Ru) {τ : MulAut J} {n : ℕ}
    (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, hDm, -⟩ := h
  set θ := e.trans Sporadic.RuSchreier.ruEquivP
  obtain ⟨s, rfl⟩ := mem_inner_of_mulEquiv θ Sporadic.RuSchreier.mulAut_inner τ
  have hs := orderOf_eq_two_of_conj_of_simple hJ hna hτ
  let φ := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)
  have h : ¬ 3 ∣ Nat.card (D.map φ.toMonoidHom) :=
    compsSatisfy_centralizer_of_mulEquiv Sporadic.RuSchreier.ruP isoInvariant_not_three_dvd
      ComponentClassification.RestrictedStd.Spor.ru_centralizerIn_comps θ s hs _
      (LocalCores.isComponent_map_mulEquiv φ hD)
  rw [card_map_of_injective φ.injective] at h
  exact h (three_dvd_card_of_lieModel hDm)

end Ru

section Ly


theorem catSL2Hyp_false_Ly {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a) (e : J ≃* NativeSporadic.Carrier .Ly) {τ : MulAut J}
    {n : ℕ} (h : CatSL2Hyp J τ n) : False := by
  obtain ⟨hτ, D, hD, hDm, -⟩ := h
  have hn := two_le_of_lieModel_PSL_two_two hDm
  have hall : ∀ β : MulAut (NativeSporadic.Carrier .Ly),
      ∃ h : NativeSporadic.Carrier .Ly, β = MulAut.conj h := by
    intro β
    have hβ : β ∈ ComponentClassification.OuterAutomorphisms.inner NativeSporadic.Ly := by
      rw [ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput]
      trivial
    obtain ⟨h, hh⟩ := hβ
    exact ⟨h, hh.symm⟩
  obtain ⟨s, rfl⟩ := mem_inner_of_mulEquiv e hall τ
  have hs := orderOf_eq_two_of_conj_of_simple hJ hna hτ
  obtain ⟨hq, -, ⟨eA⟩⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ s hs
  have hcardC : Nat.card (centralizer ({s} : Set J) ⧸ center (centralizer ({s} : Set J))) =
      19958400 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  let φ := MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)
  have h : Nat.card ((D.map φ.toMonoidHom) ⧸ center (D.map φ.toMonoidHom)) = 19958400 :=
    compsSatisfy_of_isQuasisimple hq (isoInvariant_card_quotient_center {19958400}) hcardC _
      (LocalCores.isComponent_map_mulEquiv φ hD)
  obtain ⟨ψ⟩ := nonempty_quotient_center_map_equiv φ D
  rw [← Nat.card_congr ψ.toEquiv, card_of_lieModel_PSL_two_two hDm] at h
  exact ordA_one_ne_of_check (B := 25) hn (by norm_num) (by decide) h

end Ly

end CFSG.SeitzReduction.RankOne
