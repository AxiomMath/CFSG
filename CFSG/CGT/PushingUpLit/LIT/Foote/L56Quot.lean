module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeaklyClosed
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem card_map_mk_eq {N A : Subgroup X} [N.Normal] (h : A ⊓ N = ⊥) :
    Nat.card ↥(A.map (QuotientGroup.mk' N)) = Nat.card A := by
  let g : ↥A → ↥(A.map (QuotientGroup.mk' N)) := fun a =>
    ⟨QuotientGroup.mk' N (a : X), a, a.2, rfl⟩
  have hinj : Function.Injective g := by
    intro a b hab
    have h1 : QuotientGroup.mk' N (a : X) = QuotientGroup.mk' N (b : X) := congrArg Subtype.val hab
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h1
    have h2 : (a : X)⁻¹ * (b : X) ∈ N := QuotientGroup.eq.1 h1
    have h3 : (a : X)⁻¹ * (b : X) ∈ A ⊓ N := ⟨A.mul_mem (A.inv_mem a.2) b.2, h2⟩
    rw [h, Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.1 h3)
  have hsurj : Function.Surjective g := by
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)).symm

theorem odd_card_oddCore' (Y : Type*) [Group Y] [Finite Y] : Odd (Nat.card (CFSG.oddCore Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(CFSG.oddCore_eq_piCore Y).trans (CFSG.pPrimeCore_eq_piCore Y 2).symm]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem oddCore_le_center {Y : Type*} [Group Y] [Finite Y] (hq : CFSG.IsQuasisimple Y) :
    CFSG.oddCore Y ≤ Subgroup.center Y := by
  rcases LocalCores.quasisimple_normal_subgroups hq (CFSG.oddCore_normal (G := Y)) with h | h
  · exfalso
    have hodd : Odd (Nat.card Y) := by
      have := odd_card_oddCore' Y
      rwa [h, Subgroup.card_top] at this
    have hperf : Group.IsPerfect Y := hq.1
    have hnt : Nontrivial Y := by
      have : Nontrivial (Y ⧸ Subgroup.center Y) := hq.2.1.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
    exact Group.IsPerfect.not_isSolvable Y (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  · exact h

theorem commutator_le_of_weakly_closed {J T S O W : Subgroup X} [O.Normal] (hF : Frame J T)
    (htop : J ⊔ T = ⊤) (hS : ABGLocalTools.IsSylowOf 2 S (J ⊔ T)) (hTS : T ≤ S) (hOJ : O ≤ J)
    (hOS : O ≤ S)
    (hTW : T ≤ W) (_hWS : W ≤ S) (hWTO : W ≤ T ⊔ O)
    (hwc : ∀ y ∈ J, rightConjugate W y ≤ S → rightConjugate W y = W)
    (hq : CFSG.IsQuasisimple ↥(J.map (QuotientGroup.mk' O))) : ⁅J, T⁆ ≤ O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOT : T ⊓ O = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxO⟩
    have h1 : x ∈ T ⊓ J := ⟨hxT, hOJ hxO⟩
    rw [hF.inf_eq_bot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 h1
  have hOmap : O.map (QuotientGroup.mk' O) = ⊥ :=
    (Subgroup.map_eq_bot_iff O).2 (QuotientGroup.ker_mk' O).ge
  have hsup : J.map (QuotientGroup.mk' O) ⊔ T.map (QuotientGroup.mk' O) = ⊤ := by
    rw [← Subgroup.map_sup, htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O)]
  have hH : Hyp42 (J.map (QuotientGroup.mk' O)) (T.map (QuotientGroup.mk' O))
      (S.map (QuotientGroup.mk' O)) := by
    refine ⟨hF.map O hOJ, ?_, Subgroup.map_mono hTS, ?_⟩
    · rw [hsup, isSylowOf_iff]
      obtain ⟨-, hS2, hdvd⟩ := isSylowOf_iff.mp hS
      rw [htop, Subgroup.relIndex_top_right] at hdvd
      refine ⟨le_top, hS2.map _, ?_⟩
      rw [Subgroup.relIndex_top_right]
      exact fun hdvd' => hdvd (hdvd'.trans
        (Subgroup.index_map_dvd S (QuotientGroup.mk'_surjective O)))
    · rintro _ ⟨y, hy, rfl⟩ hle
      rw [← map_rightConjugate] at hle ⊢
      have hle' : rightConjugate T y ≤ S ⊔ O := by
        rw [← QuotientGroup.ker_mk' O, ← Subgroup.comap_map_eq]
        exact Subgroup.map_le_iff_le_comap.mp hle
      have hTy : rightConjugate T y ≤ S := hle'.trans (sup_le le_rfl hOS)
      have hOy : rightConjugate O y = O := by
        refine (rightConjugate_eq_self_iff O y).2 ?_
        rw [Subgroup.normalizer_eq_top_iff.2 ‹O.Normal›]
        trivial
      have hWy : rightConjugate W y ≤ S := by
        have h1 : rightConjugate W y ≤ rightConjugate T y ⊔ rightConjugate O y := by
          calc rightConjugate W y ≤ rightConjugate (T ⊔ O) y := Subgroup.map_mono hWTO
            _ = rightConjugate T y ⊔ rightConjugate O y := Subgroup.map_sup _ _ _
        rw [hOy] at h1
        exact h1.trans (sup_le hTy hOS)
      have hWeq := hwc y hy hWy
      have hTyW : rightConjugate T y ≤ W := by
        rw [← hWeq]
        exact Subgroup.map_mono hTW
      have hK : (rightConjugate T y).map (QuotientGroup.mk' O) ≤
          T.map (QuotientGroup.mk' O) := by
        calc (rightConjugate T y).map (QuotientGroup.mk' O)
            ≤ (T ⊔ O).map (QuotientGroup.mk' O) := Subgroup.map_mono (hTyW.trans hWTO)
          _ = T.map (QuotientGroup.mk' O) := by rw [Subgroup.map_sup, hOmap, sup_bot_eq]
      have hTyO : rightConjugate T y ⊓ O = ⊥ := by
        rw [← hOy, ← rightConjugate_inf, hOT, rightConjugate_bot]
      refine Subgroup.eq_of_le_of_card_ge hK ?_
      rw [card_map_mk_eq hTyO, card_map_mk_eq hOT, rightConjugate_card]
  have hc := lemma_4_2_oddCore hH
  have hperf' : ⁅J.map (QuotientGroup.mk' O), J.map (QuotientGroup.mk' O)⁆ =
      J.map (QuotientGroup.mk' O) := Subgroup.isPerfect_iff.1 hq.1
  have hP1 : ⁅(CFSG.oddCore ↥(J.map (QuotientGroup.mk' O))).map
      (J.map (QuotientGroup.mk' O)).subtype, J.map (QuotientGroup.mk' O)⁆ = ⊥ := by
    refine le_bot_iff.1 (Subgroup.commutator_le.2 fun a ha b hb => ?_)
    obtain ⟨n, hn, rfl⟩ := ha
    have hcen := Subgroup.mem_center_iff.1 (oddCore_le_center hq hn) ⟨b, hb⟩
    refine Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2 ?_)
    exact (congrArg Subtype.val hcen).symm
  have h1 : ⁅⁅J.map (QuotientGroup.mk' O), T.map (QuotientGroup.mk' O)⁆,
      J.map (QuotientGroup.mk' O)⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono hc le_rfl).trans hP1.le)
  have h2 : ⁅⁅T.map (QuotientGroup.mk' O), J.map (QuotientGroup.mk' O)⁆,
      J.map (QuotientGroup.mk' O)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (T.map (QuotientGroup.mk' O))]
    exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := J.map (QuotientGroup.mk' O)) (H₂ := J.map (QuotientGroup.mk' O))
    (H₃ := T.map (QuotientGroup.mk' O)) h1 h2
  rw [hperf'] at h3
  rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h3
  exact h3

end CFSG.CGT.PushingUpLit.LIT.Foote
