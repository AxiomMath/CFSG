module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LemmaH
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.HexadZ3
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclOf
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfOf
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafM22

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Ch4
  CFSG.Quasithin.H13.Ch4.E443 CFSG.QuasithinUnique CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.M22 CFSG.Blueprint
open scoped IsMulCommutative

theorem conclK'_of_threeA6
    {K : Type} [Group K] [Finite K] {L V MK : Subgroup K}
    (hK : KConf K L V MK) (e : K ⧸ Subgroup.center K ≃* NativeSporadic.Carrier .M22)
    (hZ3 : Nat.card ↥(Subgroup.center K) = 3)
    (h3 : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 6)))
    (hFF : ∃ _ : IsMulCommutative ↥V,
      IsFFModule (V := ↥V) (autOn (Subgroup.normalizer (V : Set K)) V)) :
    ConclK' K L V MK := by
  classical
  obtain ⟨hperf, hcent, ⟨φ⟩⟩ := h3
  have hVcard : Nat.card V = 2 ^ 4 := hK.card_V_of_threeA6 e hZ3 ⟨hperf, hcent, ⟨φ⟩⟩
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have hsimple : IsSimpleGroup ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
      have := Hex.alt6_simple
      exact φ.isSimpleGroup
    refine ⟨hperf, hsimple, ?_⟩
    obtain ⟨x, y, hxy⟩ := Hex.alt6_nonabelian
    exact ⟨φ.symm x, φ.symm y,
      fun h => hxy (by simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg φ h)⟩
  have hshape : Shape443 (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hperf, hcent, ⟨φ⟩⟩)))))
  have hcardQ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 := by
    have hmul := Subgroup.card_mul_index (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
    have hidx : (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).index = 360 := by
      rw [Subgroup.index, Nat.card_congr φ.toEquiv, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    rw [hcent, hidx] at hmul
    rw [← hmul]
  refine Or.inl ⟨hq, hshape, Or.inl ⟨hFF, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro hLie
    have h1 := LieModel.card_psl_three_two hLie
    rw [hcardQ] at h1
    norm_num at h1
  ·
    intro hLie
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (hLie.statedClassicalModel (by decide))
    rw [hcardQ] at h1
    norm_num at h1
  ·
    intro _ hcard
    rw [hVcard] at hcard
    norm_num at hcard
  ·
    intro _ hcard
    rw [hVcard] at hcard
    norm_num at hcard

theorem KConf.conclK'_M22
    {K : Type} [Group K] [Finite K] {L V MK : Subgroup K} (hK : KConf K L V MK)
    (e : K ⧸ Subgroup.center K ≃* NativeSporadic.Carrier .M22) : ConclK' K L V MK := by
  by_cases h3A6 : Nat.card ↥(Subgroup.center K) = 3 ∧
      (Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
        Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
          Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 6)))
  · obtain ⟨hZ3, hprem⟩ := h3A6
    exact conclK'_of_threeA6 hK e hZ3 hprem (hK.isFFModule_of_threeA6 e hZ3 hprem)
  · exact ConclK.toPrime (KConf.conclK_M22 hK e (fun hZ3 hprem => h3A6 ⟨hZ3, hprem⟩))

theorem for'_M22
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    For' (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .M22)) := by
  intro G _ _ T M L B Tp VB K hHyp hP
  obtain ⟨e⟩ := hP
  have hk : KConf ↥K
      ((perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))).subgroupOf K)
      (VB.subgroupOf K) (M.subgroupOf K) := hHyp.kConf h37 h38 h39
  exact hHyp.concl443B'_of_conclK' (KConf.conclK'_M22 hk e)

end CFSG.SectionRank.QTK.Insp443

end
