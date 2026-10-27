module

public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G]

theorem dsbReduce_charTwo [Finite G] {Li Lj S T : Subgroup G}
    (hK : CharTwo (Li ⊔ S ⊔ borelOf Lj S))
    (hLi : S ≤ Subgroup.normalizer (Li : Set G))
    (hBLi : borelOf Lj S ≤ Subgroup.normalizer (Li : Set G))
    (hLj : S ≤ Subgroup.normalizer (Lj : Set G))
    (hTS : T ≤ S) (hST : S ≤ Subgroup.normalizer (T : Set G))
    (hBT : borelOf Lj S ≤ Subgroup.normalizer (T : Set G)) :
    CharTwo (Li ⊔ T ⊔ borelOf Lj S) := by
  have hHK : Li ⊔ T ⊔ borelOf Lj S ≤ Li ⊔ S ⊔ borelOf Lj S :=
    sup_le (sup_le (le_sup_left.trans le_sup_left) (hTS.trans (le_sup_right.trans le_sup_left)))
      le_sup_right
  have hLiN : Li ≤ Subgroup.normalizer ((Li ⊔ T ⊔ borelOf Lj S : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer
  have hSN : S ≤ Subgroup.normalizer ((Li ⊔ T ⊔ borelOf Lj S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (F1.le_normalizer_sup hLi hST) (F1.le_normalizer_borelOf hLj)
  have hBN : borelOf Lj S ≤ Subgroup.normalizer ((Li ⊔ T ⊔ borelOf Lj S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (F1.le_normalizer_sup hBLi hBT) Subgroup.le_normalizer
  have hKN : Li ⊔ S ⊔ borelOf Lj S ≤
      Subgroup.normalizer ((Li ⊔ T ⊔ borelOf Lj S : Subgroup G) : Set G) :=
    sup_le (sup_le hLiN hSN) hBN
  exact CFSG.QuasithinUnique.CharTwo.of_normal hK hHK
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mpr hKN)

theorem dsbReduce_hyp111R [Finite G] {L1 L2 S T : Subgroup G} (h : Hyp111R L1 L2 S)
    (hTS : T ≤ S) (hT1 : T ⊓ L1 = S ⊓ L1) (hT2 : T ⊓ L2 = S ⊓ L2)
    (hST : S ≤ Subgroup.normalizer (T : Set G))
    (hBT : bigB L1 L2 S ≤ Subgroup.normalizer (T : Set G)) :
    Hyp111R L1 L2 T := by
  have hTp : IsPGroup 2 T := h.hyp.h1.pgroup.to_le hTS
  have hB1 : borelOf L1 T = borelOf L1 S := by
    unfold borelOf
    rw [hT1]
  have hB2 : borelOf L2 T = borelOf L2 S := by
    unfold borelOf
    rw [hT2]
  have hBT1 : borelOf L1 S ≤ Subgroup.normalizer (T : Set G) :=
    (show borelOf L1 S ≤ bigB L1 L2 S from le_sup_left.trans le_sup_left).trans hBT
  have hBT2 : borelOf L2 S ≤ Subgroup.normalizer (T : Set G) :=
    (show borelOf L2 S ≤ bigB L1 L2 S from le_sup_right.trans le_sup_left).trans hBT
  have hO2 : pCoreOf 2 (L1 ⊔ L2 ⊔ T) = ⊥ := by
    have hG' : L1 ⊔ L2 ⊔ T ≤ L1 ⊔ L2 ⊔ S := sup_le_sup_left hTS _
    have hL1 : L1 ≤ Subgroup.normalizer ((pCoreOf 2 (L1 ⊔ L2 ⊔ T) : Subgroup G) : Set G) :=
      (le_sup_left.trans le_sup_left).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L1 ⊔ L2 ⊔ T))
    have hL2 : L2 ≤ Subgroup.normalizer ((pCoreOf 2 (L1 ⊔ L2 ⊔ T) : Subgroup G) : Set G) :=
      (le_sup_right.trans le_sup_left).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L1 ⊔ L2 ⊔ T))
    have hSG : S ≤ Subgroup.normalizer ((L1 ⊔ L2 ⊔ T : Subgroup G) : Set G) :=
      F1.le_normalizer_sup (F1.le_normalizer_sup h.hyp.h1.normalizes h.hyp.h2.normalizes) hST
    have hS' : S ≤ Subgroup.normalizer ((pCoreOf 2 (L1 ⊔ L2 ⊔ T) : Subgroup G) : Set G) :=
      CFSG.Quasithin.F7.le_normalizer_pCoreOf_of_le_normalizer hSG
    have hN : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer ((pCoreOf 2 (L1 ⊔ L2 ⊔ T) : Subgroup G) : Set G) :=
      sup_le (sup_le hL1 hL2) hS'
    have hle : pCoreOf 2 (L1 ⊔ L2 ⊔ T) ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 (L1 ⊔ L2 ⊔ T)).trans hG') hN
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L1 ⊔ L2 ⊔ T))
    rw [h.hyp.o2] at hle
    exact le_bot_iff.mp hle
  have hA1 : Hyp111At L1 L2 T :=
    { finite := inferInstance
      pgroup := hTp
      normalizes := hTS.trans h.hyp.h1.normalizes
      sylow := by
        rw [hT1]
        exact h.hyp.h1.sylow
      listed := h.hyp.h1.listed
      borel_le := by
        rw [hB2]
        exact h.hyp.h1.borel_le
      charTwo := by
        rw [hB2]
        exact dsbReduce_charTwo h.hyp.h1.charTwo h.hyp.h1.normalizes h.hyp.h1.borel_le
          h.hyp.h2.normalizes hTS hST hBT2 }
  have hA2 : Hyp111At L2 L1 T :=
    { finite := inferInstance
      pgroup := hTp
      normalizes := hTS.trans h.hyp.h2.normalizes
      sylow := by
        rw [hT2]
        exact h.hyp.h2.sylow
      listed := h.hyp.h2.listed
      borel_le := by
        rw [hB1]
        exact h.hyp.h2.borel_le
      charTwo := by
        rw [hB1]
        exact dsbReduce_charTwo h.hyp.h2.charTwo h.hyp.h2.normalizes h.hyp.h2.borel_le
          h.hyp.h1.normalizes hTS hST hBT1 }
  exact ⟨⟨hA1, hA2, hO2⟩, (by rw [hT1]; exact h.r1), (by rw [hT2]; exact h.r2)⟩

end Helpers

theorem leafDSBReduce : LeafDSBReduce := by
  intro G _ _ L1 L2 S h
  have hR : Hyp111R L1 L2 S := h.hyp
  have hT : (S ⊓ L1) ⊔ (S ⊓ L2) ≤ S := sup_le inf_le_left inf_le_left
  have hT1 : ((S ⊓ L1) ⊔ (S ⊓ L2)) ⊓ L1 = S ⊓ L1 := by
    have hR2 : IsPGroup 2 (((S ⊓ L1) ⊔ (S ⊓ L2)) ⊓ L1 : Subgroup G) :=
      hR.hyp.h1.pgroup.to_le (inf_le_left.trans hT)
    exact (F1.eq_of_isSylowTwoOf_le hR.hyp.h1.sylow inf_le_right hR2
      (le_inf le_sup_left inf_le_right)).symm
  have hT2 : ((S ⊓ L1) ⊔ (S ⊓ L2)) ⊓ L2 = S ⊓ L2 := by
    have hR2 : IsPGroup 2 (((S ⊓ L1) ⊔ (S ⊓ L2)) ⊓ L2 : Subgroup G) :=
      hR.hyp.h2.pgroup.to_le (inf_le_left.trans hT)
    exact (F1.eq_of_isSylowTwoOf_le hR.hyp.h2.sylow inf_le_right hR2
      (le_inf le_sup_right inf_le_right)).symm
  have hST : S ≤ Subgroup.normalizer (((S ⊓ L1) ⊔ (S ⊓ L2) : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (F1.le_normalizer_inf_of_le hR.hyp.h1.normalizes)
      (F1.le_normalizer_inf_of_le hR.hyp.h2.normalizes)
  have hBT : bigB L1 L2 S ≤ Subgroup.normalizer (((S ⊓ L1) ⊔ (S ⊓ L2) : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (F1.bigB_le_normalizer_sylow hR).1 (F1.bigB_le_normalizer_sylow hR).2
  have hR' : Hyp111R L1 L2 ((S ⊓ L1) ⊔ (S ⊓ L2)) :=
    dsbReduce_hyp111R hR hT hT1 hT2 hST hBT
  exact ⟨⟨hR', h.ns1, h.s3⟩, (by rw [hT1, hT2])⟩

end CFSG.GH74.QTGen4.DSGen4
