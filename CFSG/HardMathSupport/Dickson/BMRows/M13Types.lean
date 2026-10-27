module

public import CFSG.HardMathSupport.Dickson.BMRows.M13L33Invol
public import CFSG.HardMathSupport.Dickson.BMRows.Types
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporRows

public section

namespace CFSG.HardMathSupport.Dickson.BMRows.M13Types

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Dickson.BMRows.M13L33

theorem catalogIs_k2_of_psl {T : Type} [Group T]
    (e : T ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) :
    catalogIs T (k2 13) := by
  obtain ⟨q, _, hqc, ⟨φ⟩⟩ := exists_primePower_card_eq (ZMod 3)
  have hq3 : q.card = 3 := by rw [hqc, Nat.card_zmod]
  have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [hq3]
    omega
  refine ⟨.lie ⟨.A 2 q, hv⟩, Or.inr ⟨rfl, hq3⟩, ⟨?_⟩⟩
  exact (e.trans (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr
    (Fin 3) φ)).trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm

theorem kLevel_goodL33 : ∀ (T : Type) [Group T], GoodL33 T → kLevel 13 T ≤ 2 := by
  intro T _ ⟨e⟩
  exact kLevel_le_two_of_catalogIs (catalogIs_k2_of_psl (e.trans slEquivPsl)) fun _ h => h

section Aut


theorem typeOK_goodL33 : ∀ (T : Type) [Group T], GoodL33 T → I1416Rows.TypeOK 13 T := by
  intro T _ ⟨e⟩ _ ha _
  rw [card_mulAut_of_equiv_sl e] at ha
  revert ha
  norm_num

theorem qtypeOK_goodL33 : ∀ (T : Type) [Group T], GoodL33 T → I1416QRows.QTypeOK 13 T := by
  intro T _ ⟨e⟩
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [card_of_equiv_sl e]; norm_num)
  refine I1416QRows.qtypeOK_of_not_sq_dvd_aut (by norm_num) ?_
  rw [card_mulAut_of_equiv_sl e]
  norm_num

theorem ctypeOK_goodL33 (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    ∀ (T : Type) [Group T], GoodL33 T → Chev2Rows.CTypeOK 13 T := by
  intro T _ ⟨e⟩
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [card_of_equiv_sl e]; norm_num)
  exact Chev2Rows.ctypeOK_of_card_eq hb (card_of_equiv_sl e)

end Aut

end CFSG.HardMathSupport.Dickson.BMRows.M13Types
