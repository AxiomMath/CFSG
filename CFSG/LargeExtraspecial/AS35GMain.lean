module

public import CFSG.LargeExtraspecial.AS35GAbelian
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SmallIndex

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherTheorem3 CFSG.SignalizerFunctor.Helpers

namespace AschTI

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem lemma47Conclusion (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G}
    (hgM : g ∉ S.M) (hgz : g * S.z * g⁻¹ ∈ S.M) :
    Lemma47Conclusion S.QG (S.tiP g) (S.QG ⊔ S.tiP g) := by
  have hP2 := isPGroup_tiP S g
  have hPN := tiP_le_normalizer S g
  have h2 : IsPGroup 2 (S.QG ⊔ S.tiP g : Subgroup G) :=
    S.isPGroup_QG.to_sup_of_normal_left' hP2 hPN
  have hF : Frame S.QG (S.tiP g) := ⟨hPN, tiP_inf_QG S hTI hgM, hP2⟩
  have hSF : SylowFrame S.QG (S.tiP g) (S.QG ⊔ S.tiP g) :=
    { toFrame := hF
      sylow := isSylowOf_self h2
      sylow_normalizer := isSylowOf_self (h2.to_le inf_le_left) }
  have hH : Hyp43 S.QG (S.tiP g) (S.tiP g)
      ((S.QG ⊔ S.tiP g) ⊓ normalizer (S.tiP g : Set G)) :=
    { le := le_inf le_sup_right le_normalizer
      le_normalizer := inf_le_right
      le_sup := inf_le_left
      sylow := isSylowOf_self hP2
      inf_eq_bot := fun y hy hyH => by
        have hyN : y ∉ normalizer (S.tiP g : Set G) := fun h => hyH ⟨mem_sup_left hy, h⟩
        have hyC : y ∉ normalizer (S.Qa g : Set G) := by
          rw [normalizer_Qa]
          intro hyt
          have hyR : y ∈ S.QG ⊓ normalizer (S.tiP g : Set G) := by
            rw [QG_inf_normalizer_tiP S hTI hgM hgz]
            exact ⟨hy, hyt⟩
          exact hyN hyR.2
        have hle : S.tiP g ⊓ rightConjugate (S.tiP g) y ≤ rightConjugate (S.Qa g) y :=
          inf_le_right.trans (rightConjugate_le_rightConjugate inf_le_left y)
        have h := two_subgroup_inf_conjugate_eq_bot (S.Qa g) _ (tightlyEmbedded_Qa S hTI g)
          (hP2.to_le inf_le_left) y hyC hle
        have hsub : S.tiP g ⊓ rightConjugate (S.tiP g) y ≤ S.Qa g :=
          inf_le_left.trans inf_le_left
        rwa [inf_eq_left.mpr hsub] at h }
  have hrel : (S.tiP g).relIndex ((S.QG ⊔ S.tiP g) ⊓
      ((S.QG ⊔ S.tiP g) ⊓ normalizer (S.tiP g : Set G))) ≤ Nat.card (S.tiP g) := by
    rw [inf_left_idem]
    set K := (S.QG ⊔ S.tiP g) ⊓ normalizer (S.tiP g : Set G) with hK
    obtain ⟨hdec, hbot, -⟩ := AschbacherTheorem3.lemma_4_1 hF le_rfl le_sup_right
    have hcard := card_sup_of_le_normalizer (A := S.tiP g) (B := K ⊓ S.QG)
      (inf_le_left.trans inf_le_right) hbot
    rw [← hdec] at hcard
    have hmul := Subgroup.relIndex_mul_card (S.tiP g) K
    rw [inf_eq_left.mpr (le_inf le_sup_right le_normalizer), hcard] at hmul
    have hle : Nat.card (K ⊓ S.QG : Subgroup G) ≤ Nat.card (S.tiP g) := by
      have h := Subgroup.card_le_of_le
        (show K ⊓ S.QG ≤ S.QG ⊓ normalizer (S.tiP g : Set G) from fun x hx => ⟨hx.2, hx.1.2⟩)
      rwa [QG_inf_normalizer_tiP S hTI hgM hgz, card_tiR_eq_card_tiP S hTI hgM hgz] at h
    have hpos : 0 < Nat.card (S.tiP g) := Nat.card_pos
    have h1 : (S.tiP g).relIndex K * Nat.card (S.tiP g) ≤
        Nat.card (S.tiP g) * Nat.card (S.tiP g) := by
      rw [hmul]
      exact Nat.mul_le_mul_left _ hle
    exact Nat.le_of_mul_le_mul_right h1 hpos
  exact lemma_4_7_statement G S.QG (S.tiP g) (S.QG ⊔ S.tiP g) (S.tiP g) _ hSF hH hrel

theorem false_of_ti (hn : 3 ≤ S.width) (hTI : ∀ g : G, S.QG ⊓ S.Qa g ≠ ⊥ → g ∈ S.M) {g : G}
    (hgM : g ∉ S.M) (hgz : g * S.z * g⁻¹ ∈ S.M) : False := by
  rcases lemma47Conclusion S hTI hgM hgz with h | ⟨h, -⟩ | ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, h⟩
  · exact false_of_relativeWeakClosure_eq S hTI hgM hgz h
  · exact false_of_isCyclic S hn hTI hgM hgz h
  · exact false_of_isMulCommutative S hn hTI hgM hgz h
  · exact false_of_relIndex_eq_two S hn hTI hgM hgz h

end AschTI

namespace S14

theorem aschbacherTIInput : AschbacherTIInput := by
  intro G _ _ S hn hTI _ _ _ g hgM hgz
  exact (AschTI.false_of_ti S hn hTI hgM hgz).elim

end S14

end CFSG.LargeExtraspecial
