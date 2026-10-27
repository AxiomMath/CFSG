module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGFiveMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.Walter.PSL2Facts.Even
import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup

namespace KGFive

variable {G : Type} [Group G]

theorem false_of_sl2_two {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1))
    (h : CFSG.IsQuasisimple Q ∨ (Nat.card Q).Prime) : False := by
  have hcard : Nat.card Q = 2 ^ 1 * 3 ^ 1 := by
    rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      GaloisField.card 2 1 one_ne_zero]
    norm_num
  rcases h with ⟨-, hs, a, b, hab⟩ | hp
  · haveI := Fintype.ofFinite Q
    have hsolv : Group.IsSolvable Q :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])
    haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hs
    haveI : Group.IsSolvable (Q ⧸ Subgroup.center Q) := inferInstance
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance a b)
  · rw [hcard] at hp
    norm_num at hp

theorem cgsIn_le_aschbacherC (X T : Subgroup G) : CFSG.Quasithin.cgsIn X T ≤ aschbacherC X T := by
  refine iSup_le fun C => iSup_le fun hCT => iSup_le fun hC0 => iSup_le fun hCc => ?_
  rw [inf_comm]
  exact le_iSup₂_of_le C ⟨hCT, hC0, hCc⟩ le_rfl

variable [Finite G]

theorem isChiBlock_of_isBlockOfInX {X Y : Subgroup G} (h : CFSG.CGT.PushingUp.IsBlockOfInX X Y) :
    IsChiBlock X Y := by
  obtain ⟨hYX, hYs, hshort, htype⟩ := h
  refine ⟨(CFSG.Open.IsSubnormal.iff_subgroupOf hYX).2 hYs, ?_, ?_⟩
  · intro N hN hP
    have hle : CFSG.RankThree.PartOne.oResidualTwo ↥Y ≤ N := sInf_le ⟨hN, hP⟩
    rw [hshort.residual_eq] at hle
    exact top_le_iff.mp hle
  · rcases htype with ⟨n, hn, φ, -⟩ | ⟨n, hn, φ, -⟩
    · exact Or.inl ⟨2 * n + 1, by omega, odd_two_mul_add_one n, ⟨φ⟩⟩
    · by_cases hn1 : n = 1
      · subst hn1
        exact (false_of_sl2_two φ hshort.quotient_type).elim
      · exact Or.inr ⟨n, by omega,
          ⟨φ.trans (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm⟩⟩

end KGFive

theorem kfact282_holds : KFact282 := by
  intro G _ _ X T hK hF hT hT1
  have hTS : CFSG.QuasithinUnique.IsSylowTwoOf T X := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  by_contra hXM
  obtain ⟨Y, hY, hYM⟩ := CFSG.CGT.PushingUpLit.AschbacherLocalFactorization.relative
    CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
    (CFSG.AGLEmbedding.LocalCGT.kProper_of_isKGroup hK)
    (CFSG.AGLEmbedding.LocalCGT.isCharacteristicP_of_charTwo hF)
    (CFSG.AGLEmbedding.LocalCGT.isSylowOf_of_isSylowTwoOf hTS)
    ((CFSG.AGLEmbedding.LocalCGT.centralizer_inf_le_cgsIn hTS.2.1 hT1).trans
      ((KGFive.cgsIn_le_aschbacherC X T).trans le_sup_right))
    (fun B hB0 hBS hBc => (CFSG.AGLEmbedding.LocalCGT.normalizer_inf_le_cgsIn B hB0 hBS hBc).trans
      ((KGFive.cgsIn_le_aschbacherC X T).trans le_sup_right)) hXM
  have hYc : IsChiBlock X Y := KGFive.isChiBlock_of_isBlockOfInX hY
  exact hYM ((le_iSup₂_of_le Y hYc le_rfl : Y ≤ chiBlockProduct X).trans le_sup_left)

theorem kgStep5Sylow_holds : KGStep5Sylow :=
  kgStep5Sylow_of_kfact282 kfact282_holds

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
