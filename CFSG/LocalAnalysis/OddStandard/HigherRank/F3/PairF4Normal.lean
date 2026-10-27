module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Levi
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalToral
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4C3
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.StandardType.RootCentExc
  CFSG.ComponentClassification.CatLeafProof

section Ambient

variable {F : Type} [Field F]


theorem f4_pinnedX_commute_rootSL2 {α : Fin (Tag.rank .F4) → ℤ} (hα : IsRoot .F4 α)
    (h : iform α thetaF4 = 0) (c : F) (A : SL2 F) :
    pinnedX .F4 F α c * rootSL2 .F4 F thetaF4 A = rootSL2 .F4 F thetaF4 A * pinnedX .F4 F α c := by
  have hL := (exceptional_Lang_root_rank_one_torus_transport .F4 F isRoot_thetaF4).1
  have hmem : rootSL2 .F4 F thetaF4 A ∈
      rootSubgroup .F4 F thetaF4 ⊔ rootSubgroup .F4 F (-thetaF4) := by
    rw [← hL]
    exact ⟨A, rfl⟩
  have h' : iform α (-thetaF4) = 0 := by
    rw [show (-thetaF4 : Fin (Tag.rank .F4) → ℤ) = (-1 : ℤ) • thetaF4 by simp,
      iform_smul_right, h, mul_zero]
  have hle : rootSubgroup .F4 F thetaF4 ⊔ rootSubgroup .F4 F (-thetaF4) ≤
      Subgroup.centralizer {pinnedX .F4 F α c} := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
    · rintro _ ⟨b, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (pinnedX_commute_of_iform_eq_zero_F4 hα isRoot_thetaF4 iform_thetaF4_self h c b).symm
    · rintro _ ⟨b, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (pinnedX_commute_of_iform_eq_zero_F4 hα isRoot_neg_thetaF4 iform_neg_thetaF4_self h'
        c b).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hmem)).symm

theorem f4_leviGens_commute_rootSL2 {x : ModGL .F4 F}
    (hx : x ∈ Subgroup.closure (leviGens .F4 F JF4)) (A : SL2 F) :
    x * rootSL2 .F4 F thetaF4 A = rootSL2 .F4 F thetaF4 A * x := by
  have hle : Subgroup.closure (leviGens .F4 F JF4) ≤
      Subgroup.centralizer ((rootSL2 .F4 F thetaF4).range : Set (ModGL .F4 F)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ ⟨B, rfl⟩
      rw [← pinnedX_single]
      exact (f4_pinnedX_commute_rootSL2 (isRoot_single _ j) (iform_single_eq_zero_of_mem_F4 hj) c
        B).symm
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ ⟨B, rfl⟩
      rw [← pinnedX_neg_single]
      exact (f4_pinnedX_commute_rootSL2 (IsRoot.neg (isRoot_single _ j))
        (iform_neg_single_eq_zero_of_mem_F4 hj) c B).symm
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) _ ⟨A, rfl⟩).symm

theorem f4_toralRootGroup_le_normalizer (hF : ringChar F ≠ 2) :
    toralRootGroup .F4 F (corootDiagF4 thetaF4 (-1 : Fˣ)) ≤
      Subgroup.normalizer (Subgroup.closure (leviGens .F4 F JF4) : Set (ModGL .F4 F)) := by
  have hL := (exceptional_Lang_root_rank_one_torus_transport .F4 F isRoot_thetaF4).1
  refine sup_le (torusGroup_le_normalizer_leviGens JF4) (iSup₂_le fun σ hσ => ?_)
  obtain ⟨hσr, hσ1⟩ := hσ
  have hev : Even (iform thetaF4 σ / 2) := by
    refine even_of_neg_one_zpow_eq_one hF ?_
    rw [← rootChar_corootDiagF4 isRoot_thetaF4 iform_thetaF4_self]
    exact hσ1
  have hR : ∀ y ∈ rootRankOneGroup .F4 F thetaF4,
      y ∈ Subgroup.normalizer (Subgroup.closure (leviGens .F4 F JF4) : Set (ModGL .F4 F)) := by
    rintro _ ⟨A, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact f4_leviGens_commute_rootSL2 hy A
  rcases eq_or_iform_eq_zero_of_even_F4 hσr hev with rfl | rfl | h0
  · exact fun y hy => hR y (by rw [hL]; exact Subgroup.mem_sup_left hy)
  · exact fun y hy => hR y (by rw [hL]; exact Subgroup.mem_sup_right hy)
  · exact (rootSubgroup_le_subsystemGroup (mem_parabolicRoots_F4 hσr h0)).trans
      Subgroup.le_normalizer

theorem f4_toralCentralizer_le_normalizer (hF : ringChar F ≠ 2)
    {g : ModGL .F4 F} (hg : g ∈ toralCentralizer .F4 F (corootDiagF4 thetaF4 (-1 : Fˣ))) :
    g ∈ Subgroup.normalizer (Subgroup.closure (leviGens .F4 F JF4) : Set (ModGL .F4 F)) :=
  f4_toralRootGroup_le_normalizer hF
    (toralCentralizer_le_toralRootGroup_of_sign (τ := .F4) (Or.inr (Or.inl rfl)) hF
      (corootDiagF4_neg_one_sign thetaF4) hg)

theorem f4LeviC3_eq_JF4 : f4LeviC3 = JF4 := by
  ext j
  simp only [f4LeviC3, JF4, Set.mem_range, Set.mem_setOf_eq]
  revert j
  decide

theorem f4_map_subtype_layer :
    (⨆ k, CFSG.LieType.CurtisTits.rankOne (f4Datum F).rootGroup (c3Node k)).map
        (adjointGroup .F4 F).subtype = Subgroup.closure (leviGens .F4 F JF4) := by
  rw [map_subtype_iSup_c3, f4LeviC3_eq_JF4]
  rfl

theorem f4_normal_c3_centralizer (hF : ringChar F ≠ 2)
    (N : Subgroup ↥(adjointGroup .F4 F))
    (hN : N.map (adjointGroup .F4 F).subtype = Subgroup.closure (leviGens .F4 F JF4))
    (u : ↥(adjointGroup .F4 F))
    (hu : (u : ModGL .F4 F) = rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : Fˣ))) :
    (N.subgroupOf (Subgroup.centralizer ({u} : Set ↥(adjointGroup .F4 F)))).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have hg : (((g : Subgroup.centralizer ({u} : Set ↥(adjointGroup .F4 F))) :
      ↥(adjointGroup .F4 F)) : ModGL .F4 F) ∈
      toralCentralizer .F4 F (corootDiagF4 thetaF4 (-1 : Fˣ)) :=
    Subgroup.mem_subgroupOf.1 ((SetLike.ext_iff.1
      (CFSG.ClassicalInvolution.ModelFacts.centralizer_eq_subgroupOf_toralCentralizer _ u hu) _).1
      g.2)
  have hgn := f4_toralCentralizer_le_normalizer hF hg
  have hx' : (((x : Subgroup.centralizer ({u} : Set ↥(adjointGroup .F4 F))) :
      ↥(adjointGroup .F4 F)) : ModGL .F4 F) ∈ Subgroup.closure (leviGens .F4 F JF4) := by
    rw [← hN]
    exact ⟨_, hx, rfl⟩
  have h2 := (Subgroup.mem_normalizer_iff.1 hgn _).1 hx'
  rw [← hN] at h2
  obtain ⟨y, hy, hyeq⟩ := h2
  have hyg : y = ((g : ↥(adjointGroup .F4 F)) * (x : ↥(adjointGroup .F4 F)) *
      (g : ↥(adjointGroup .F4 F))⁻¹) := Subtype.ext (by simpa using hyeq)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hyg]
  exact hy

end Ambient

end CFSG.OddStandard.HigherRank.F3
