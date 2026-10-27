module

public import CFSG.GH74.KGroups.L28
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.Presented
public import CFSG.Adapters.StatedSmallProjOrders
public import Certificates.Certificate17371
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Leaf

public section

namespace CFSG.HardMathSupport.Dickson.I271

open TauCeti CFSG.Open CFSG.CosetTable CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.ClassicalModels
  CFSG.Assembly.LowTwoRank CFSG.Adapters

section Chev


theorem isChevSimple_three_of_equiv_P9 {T : Type} [Group T]
    (e : T ≃* ↥(CFSG.GH74.KGroups.L28.QP.originalSubgroup)) : IsChevSimple 3 T := by
  obtain ⟨e1⟩ := CFSG.GH74.KGroups.L28.equiv_psl_P
  let q : PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
  haveI : Fact q.p.Prime := ⟨Nat.prime_two⟩
  have hv : (LieTypeIndex.A 1 q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q, PrimePower.card_def]
  let eF := finiteFieldEquivGaloisField CFSG.Quasithin.GF8 2 3 (by norm_num)
    CFSG.GH74.KGroups.L28.card_GF8
  let eP := projectiveSpecialLinearFieldEquiv eF (Fin 2)
  let eC := linearCatalogCandidateEquivPSL 1 q hv
  exact Or.inr ⟨.lie ⟨LieTypeIndex.A 1 q, hv⟩, by simp [ambiguousChev, q, PrimePower.card_def],
    ⟨e.trans (e1.symm.trans (eP.trans eC.symm))⟩⟩

theorem card_P9 : Nat.card ↥(CFSG.GH74.KGroups.L28.QP.originalSubgroup) = 504 := by
  rw [CFSG.GH74.KGroups.card_group CFSG.GH74.KGroups.L28.QP CFSG.GH74.KGroups.L28.QP_ok,
    CFSG.GH74.KGroups.L28.QP_valid.2]

theorem isSimpleGroup_of_equiv_P9 {T : Type} [Group T]
    (e : T ≃* ↥(CFSG.GH74.KGroups.L28.QP.originalSubgroup)) : IsSimpleGroup T := by
  obtain ⟨e1⟩ := CFSG.GH74.KGroups.L28.equiv_psl_P
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) CFSG.Quasithin.GF8) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
      (by rw [CFSG.GH74.KGroups.L28.card_GF8]; norm_num)
  exact (e.trans e1.symm).isSimpleGroup_congr.2 inferInstance

theorem nonabelian_of_equiv_P9 {T : Type} [Group T]
    (e : T ≃* ↥(CFSG.GH74.KGroups.L28.QP.originalSubgroup)) : ∃ a b : T, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  haveI := isSimpleGroup_of_equiv_P9 e
  letI : CommGroup T := { (inferInstance : Group T) with mul_comm := hc }
  have hp := IsSimpleGroup.prime_card (α := T)
  have h1 : Nat.card T = 504 := by rw [Nat.card_congr e.toEquiv]; exact card_P9
  rw [h1] at hp
  norm_num at hp

theorem leafType_three_of_equiv_P9 {T : Type} [Group T]
    (e : T ≃* ↥(CFSG.GH74.KGroups.L28.QP.originalSubgroup)) : LeafType 3 T := by
  refine Or.inl ⟨isChevSimple_three_of_equiv_P9 e, ?_, ?_⟩
  · intro h
    obtain ⟨F, _, _, hF, ⟨e'⟩⟩ := h
    have h1 : Nat.card T = 504 := by rw [Nat.card_congr e.toEquiv]; exact card_P9
    have h2 : Nat.card (StatedProj (StatedSL 2 F)) = 9828 := by
      rw [CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd (by rw [hF]; decide), hF]
      norm_num
    rw [Nat.card_congr e'.toEquiv, h2] at h1
    omega
  · rintro ⟨f⟩
    have h1 : Nat.card T = 504 := by rw [Nat.card_congr e.toEquiv]; exact card_P9
    rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup] at h1
    simp [Nat.factorial] at h1

end Chev

section Recognition


open CFSG.GH74.KGroups.L28 CFSG.HardMathSupport.Dickson.I271.L28Presentation
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest

theorem l28Words_pa_pb : ∀ w ∈ l28Words, evalW (![pa, pb] : Fin 2 → Equiv.Perm (Fin 9)) w = 1 := by
  decide +kernel

theorem closure_range_pa_pb : Subgroup.closure (Set.range (![pa, pb] : Fin 2 → Equiv.Perm (Fin 9))) =
    QP.originalSubgroup := by
  rw [QP_closure]
  congr 1
  ext g
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem nonempty_mulEquiv_P9_of_rels {G : Type} [Group G] (g : Fin 2 → G)
    (hrels : ∀ w ∈ l28Words, evalW g w = 1) (hcard : Nat.card ↥(Subgroup.closure (Set.range g)) = 504) :
    Nonempty (↥(Subgroup.closure (Set.range g)) ≃* ↥(QP.originalSubgroup)) := by
  obtain ⟨hfin, hP⟩ := Certificates.certificate17371
  have hN₂ : 504 ≤ Nat.card ↥(Subgroup.closure (Set.range (![pa, pb] : Fin 2 → Equiv.Perm (Fin 9)))) := by
    rw [closure_range_pa_pb, card_P9]
  obtain ⟨e⟩ := CFSG.AGLEmbeddingD2.Wilson.Census228Spor.nonempty_mulEquiv_of_presented g
    (![pa, pb] : Fin 2 → Equiv.Perm (Fin 9)) l28Words hrels l28Words_pa_pb hfin 504 (by omega)
    hcard.ge hN₂
  exact ⟨e.trans (MulEquiv.subgroupCongr closure_range_pa_pb)⟩

end Recognition

end CFSG.HardMathSupport.Dickson.I271
