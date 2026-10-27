module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Weir
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeClassical
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossOmega
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.NoE27Exc
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Inner
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Setup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (NoE27)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
  (I294Cross.orderOf_neg_natCast_one)
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev (NoE27.of_injective NoE27.of_surjective
  noE27_projSL noE27_projSU orderOf_card_zmod_three)

@[expose] def IsRankTwoIndex : LieTypeIndex → Prop
  | .A r q => (r = 3 ∨ r = 4) ∧ q.card % 3 = 2
  | .twistedA r q => (r = 3 ∨ r = 4) ∧ q.card % 3 = 1
  | .B r _ => r = 2
  | .G2 _ | .trialityD4 _ | .reeF4 _ => True
  | _ => False

@[expose] def NoE27Index (d : ValidLieTypeIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* (CFSGIndex.lie d).Group) →
    ∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E ≠ 27

section Transport

theorem noE27Index_of_model {d : ValidLieTypeIndex}
    (h : ∀ (K : Type) [Group K], (K ≃* (CFSGIndex.lie d).Group) →
      ∃ (M : Type) (_ : Group M), NoE27 M ∧ Nonempty (K ≃* M)) : NoE27Index d := by
  intro K _ _ ⟨e⟩ E hE h27
  obtain ⟨M, _, hM, ⟨f⟩⟩ := h K e
  exact NoE27.of_injective (φ := f.toMonoidHom) f.injective hM ⟨E, hE, h27⟩

theorem noE27Index_of_rankLE2 {d : ValidLieTypeIndex}
    (h : CFSG.LieType.SeitzGeneration.RankLE2 3 (CFSGIndex.lie d).Group) : NoE27Index d := by
  intro K _ _ ⟨e⟩ E hE h27
  have h9 := h (E.map e.toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hE _)
  rw [Subgroup.card_map_of_injective e.injective, h27] at h9
  norm_num at h9

end Transport

section Classical

theorem orderOf_card_zmod_three_one {q : ℕ} (hq : q % 3 = 1) : orderOf (q : ZMod 3) = 1 := by
  rw [orderOf_eq_one_iff, ← ZMod.natCast_mod, hq]
  rfl

theorem noE27_projSp_two {F : Type} [Field F] [Finite F] (hF : ¬ 3 ∣ Nat.card F) :
    NoE27 (StatedProj (StatedSp 2 F)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hF' : ¬ 3 ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hmod : Fintype.card F % 3 = 1 ∨ Fintype.card F % 3 = 2 := by omega
  have hSp : NoE27 ↥(StatedSp 2 F) := by
    refine CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev.Weir.noE27_of_sigma ?_
      fun P => CFSG.GroupTheory.WeirSylow.sylow_Sp (by decide) F hF' 2 P
    rcases hmod with h | h
    · rw [orderOf_card_zmod_three_one h]
      simp
    · rw [orderOf_card_zmod_three h]
      simp
  refine NoE27.of_surjective (QuotientGroup.mk'_surjective _) ?_ hSp
  refine CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.CrossOmega.not_dvd_card_ker_of_sq
    Nat.prime_three (by norm_num) _ fun x hx => ?_
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hx)
  have hc2 : c ^ 2 = 1 :=
    (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff (n := 2) (by norm_num) c).1 (by rw [hc]; exact x.2)
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hc, ← map_pow, hc2, map_one, Subgroup.coe_one]

end Classical

section Families


theorem noE27Index_of_isRankTwoIndex (d : ValidLieTypeIndex) (hch : d.1.characteristic ≠ 3)
    (hd : IsRankTwoIndex d.1) : NoE27Index d := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_A] using hch
    obtain ⟨hr, hq⟩ := hd
    refine noE27Index_of_model fun K _ e => ?_
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    have hF3 : ¬ 3 ∣ Nat.card F := by
      rw [hF]; exact not_three_dvd_prime_pow q.prime_p hp3
    have hFq : Nat.card F % 3 = 2 := by rw [hF, ← PrimePower.card_def]; exact hq
    refine ⟨_, _, noE27_projSL hF3 ?_ ?_, ⟨f⟩⟩
    · rcases hr with rfl | rfl <;> norm_num
    · rw [orderOf_card_zmod_three hFq]
      rcases hr with rfl | rfl <;> norm_num
  | twistedA r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_twistedA] using hch
    obtain ⟨hr, hq⟩ := hd
    refine noE27Index_of_model fun K _ e => ?_
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    have hq3 : ¬ 3 ∣ q.p ^ q.exponent := not_three_dvd_prime_pow q.prime_p hp3
    have hq1 : q.p ^ q.exponent % 3 = 1 := by rw [← PrimePower.card_def]; exact hq
    refine ⟨_, _, noE27_projSU hF hq3 (by omega) ?_ ?_, ⟨f⟩⟩
    · rcases hr with rfl | rfl <;> norm_num
    · rw [I294Cross.orderOf_neg_natCast_one hq1]
      rcases hr with rfl | rfl <;> norm_num
  | B r q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_B] using hch
    obtain rfl : r = 2 := hd
    refine noE27Index_of_model fun K _ e => ?_
    obtain ⟨-, F, _, _, hF, ⟨f⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    exact ⟨_, _, noE27_projSp_two (by rw [hF]; exact not_three_dvd_prime_pow q.prime_p hp3),
      ⟨f⟩⟩
  | G2 q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_G2] using hch
    refine noE27Index_of_model fun K _ e => ?_
    obtain ⟨F, _, _, hF, -, ⟨f⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
    refine ⟨_, _, CFSG.HardMathSupport.Dickson.Sec6.I1431.noE27_adjointG2 F ?_, ⟨e.trans f⟩⟩
    rw [hF, PrimePower.card_def]
    exact not_three_dvd_prime_pow q.prime_p hp3
  | trialityD4 q =>
    have hp3 : q.p ≠ 3 := by simpa [LieTypeIndex.characteristic_trialityD4] using hch
    exact noE27Index_of_rankLE2
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv hp3)
  | reeF4 m =>
    exact noE27Index_of_rankLE2
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_reeF4 hv)
  | C r q => exact hd.elim
  | D r q => exact hd.elim
  | twistedD r q => exact hd.elim
  | E6 q => exact hd.elim
  | E7 q => exact hd.elim
  | E8 q => exact hd.elim
  | F4 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | suzuki k => exact hd.elim
  | reeG2 k => exact hd.elim
  | tits => exact hd.elim

end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
