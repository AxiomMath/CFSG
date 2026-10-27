module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2S6Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6All
public import CFSG.Timmesfeld.Final.Simple

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace KForm.Mod

theorem exists_noncomm_alternatingGroup_six :
    ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : center (alternatingGroup (Fin 6)) = ⊤ := by
    rw [eq_top_iff']
    intro a
    rw [Subgroup.mem_center_iff]
    intro b
    exact h b a
  have hb : center (alternatingGroup (Fin 6)) = ⊥ := alternatingGroup.center_eq_bot (by simp)
  have h1 : Nat.card (alternatingGroup (Fin 6)) = 1 := by
    rw [← Subgroup.card_top (G := alternatingGroup (Fin 6)), ← hc, hb, Subgroup.card_bot]
  rw [KForm.card_alternatingGroup_six] at h1
  omega

theorem fusionOddCore_eq_center_of_quasisimple {J : Type*} [Group J] [Finite J]
    (hq : CFSG.IsQuasisimple J)
    (e : J ⧸ fusionOddCore J ≃* alternatingGroup (Fin 6)) : fusionOddCore J = center J := by
  have hne : fusionOddCore J ≠ ⊤ := by
    intro h
    have h1 : Nat.card (J ⧸ fusionOddCore J) = 1 := by
      rw [← Subgroup.index_eq_card, h, Subgroup.index_top]
    rw [Nat.card_congr e.toEquiv, KForm.card_alternatingGroup_six] at h1
    omega
  apply le_antisymm
  · exact CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
      ⟨hq.1.commutator_eq_top, hq.2.1⟩ _ hne
  · intro z hz
    have hc : e (QuotientGroup.mk z) ∈ center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨b, rfl⟩ := e.surjective a
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg (fun x => e (QuotientGroup.mk x)) (Subgroup.mem_center_iff.1 hz b)
    rw [alternatingGroup.center_eq_bot (by simp)] at hc
    have h1 : (QuotientGroup.mk z : J ⧸ fusionOddCore J) = 1 :=
      e.injective ((Subgroup.mem_bot.1 hc).trans (map_one e).symm)
    exact (QuotientGroup.eq_one_iff z).1 h1

theorem eq_bot_of_isPGroup_two_of_odd_card {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hp : IsPGroup 2 H) (ho : Odd (Nat.card H)) : H = ⊥ := by
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at ho
  have hn0 : n = 0 := by
    by_contra hn0
    exact (Nat.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 (dvd_pow_self 2 hn0))
  rw [hn0, pow_zero] at hn
  exact Subgroup.eq_bot_of_card_eq H hn

end KForm.Mod

theorem oddLieA6TwoComponent_holds :
    OddLieA6TwoComponent := by
  intro S _ _ hodd σ hσ J hJ hquot
  obtain ⟨e⟩ := hquot
  by_cases hna : ∃ a b : S, a * b ≠ b * a
  swap
  · exfalso
    push Not at hna
    obtain ⟨a, b, hab⟩ := KForm.Mod.exists_noncomm_alternatingGroup_six
    apply hab
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg (fun t => e (QuotientGroup.mk t)) (Subtype.ext (Subtype.ext (hna _ _)))
  haveI hsimp : IsSimpleGroup S := by
    obtain ⟨t, n, p, f, -, -, -, hm⟩ := hodd
    exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel hm
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    omega
  have hsub : J.IsSubnormal := by
    obtain ⟨K, -, h, -⟩ := hJ
    exact h
  have hq : CFSG.IsQuasisimple ↥J :=
    CFSG.ComponentClassification.CatLeaf.fixedTwoComponentsQuasisimple_of_oddLieType hna hodd σ
      hσσ hσ1 J hJ
  have hOZ : fusionOddCore ↥J = center ↥J :=
    KForm.Mod.fusionOddCore_eq_center_of_quasisimple hq e
  have e' : ↥J ⧸ center ↥J ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hOZ.symm).trans e
  have h2 : IsPGroup 2 ↥(center ↥J) :=
    CFSG.ComponentClassification.CatLeafProof.oddLieA6ComponentCentre_holds S hna hodd σ hσ J
      ⟨hq, hsub⟩ ⟨e'⟩
  have hodd2 : Odd (Nat.card ↥(center ↥J)) := by
    rw [← hOZ]
    exact EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore ↥J
  have hbot : fusionOddCore ↥J = ⊥ :=
    hOZ.trans (KForm.Mod.eq_bot_of_isPGroup_two_of_odd_card h2 hodd2)
  exact ⟨((QuotientGroup.quotientBot (G := ↥J)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hbot.symm).trans e))⟩

end CFSG.EvenSporadicStandard.M24Std
