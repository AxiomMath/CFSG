module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TablesHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2EUp
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyOdd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166E6FourCent
public import CFSG.LieType.Chevalley.ParabolicSylowSubsystem

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.ExceptionalCover
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Timmesfeld.ExceptionalOrders

theorem lieModel_adjointGroup_E6 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    CFSG.Blueprint.LieModel (adjointGroup .E6 F) .E6 0 2 n := by
  refine Or.inr (Or.inl ⟨rfl, by decide, ?_⟩)
  refine ⟨?_, CFSG.SignalizerFunctorTheorem.CatalogBridge.untwistedChevalleyModel_adjointGroup
    (τ := .E6) (K := F) hF⟩
  exact ⟨Nat.prime_two, hn, rfl⟩

theorem hasLabel_adjointGroup_E6 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    HasLabel (adjointGroup .E6 F) (· = ⟨.E6, 0, n⟩) := by
  have hLie := lieModel_adjointGroup_E6 hF hn
  have hZ : Subgroup.center (adjointGroup .E6 F) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨lab, hlab, htag, hrank, _, hdeg, hraw⟩ :=
    CFSG.StandardType.exists_label_rawDatum_of_lieModel (S := adjointGroup .E6 F) hZ hLie
  have hlab' : lab = ⟨.E6, 0, n⟩ := by
    obtain ⟨t, r, k⟩ := lab
    have ht : t = .E6 := by
      cases t <;> simp only [CFSG.StandardType.markTag] at htag ⊢
      all_goals try rfl
      all_goals try split_ifs at htag
      all_goals simp_all
    subst ht
    have hr : r = 0 := hlab.2
    subst hr
    have hk : k = n := by simpa [CFSG.StandardType.markDeg] using hdeg
    subst hk
    rfl
  subst hlab'
  have hq : CFSG.IsQuasisimple (adjointGroup .E6 F) :=
    CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 F
  refine hasLabel_of_quasisimple_rawDatum hq hlab ?_
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F' ⟨e⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot |>.trans e⟩

theorem evenRank_adjointGroup_E6_two {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) :
    evenRank (adjointGroup .E6 F) = 5 := by
  have hlab : CFSG.LocalAnalysis.GLTheoremA.Rk2IsLabel (adjointGroup .E6 F) ⟨.E6, 0, 2⟩ :=
    hasLabel_adjointGroup_E6 (n := 2) (by simpa using hF) (by norm_num)
  have hcenter : Subgroup.center (adjointGroup .E6 F) = ⊥ := center_adjointGroup_eq_bot
  have hlow : 5 ≤ evenRank (adjointGroup .E6 F) :=
    CFSG.LocalAnalysis.GLTheoremA.rk2_low_e6_two_of_center_eq_bot (adjointGroup .E6 F)
      ⟨.E6, 0, 2⟩ hlab rfl rfl hcenter
  have hup : evenRank (adjointGroup .E6 F) ≤ 5 :=
    (rk2_eUpAt_of_tables rk2KRank rk2Upper_holds hlab).e6_two rfl hcenter
  omega


@[expose] def e6FourB : Subgroup (adjointGroup Tag.E6 K) :=
  (torusGroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K)

@[expose] def e6FourX : adjointGroup Tag.E6 K :=
  ⟨rootDiagUnit Tag.E6 e6FourToralParam, e6FourToralElement_mem_adjointGroup⟩

@[expose] def e6FourJ : Subgroup (adjointGroup Tag.E6 K) :=
  (subsystemGroup Tag.E6 K setD).subgroupOf (adjointGroup Tag.E6 K)

theorem isElemAbelian_e6FourB : IsElemAbelian 3 e6FourB := by
  refine ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext (Subtype.ext ?_)), ?_⟩
  · have ha : ((a : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K :=
      Subgroup.mem_subgroupOf.mp a.2
    have hb : ((b : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K :=
      Subgroup.mem_subgroupOf.mp b.2
    exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ha)
      (torusGroup_le_diagonalGroup hb)
  · intro x hxmem
    have hx : ((x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hxmem)
    have h3 : Nat.card Kˣ = 3 := by
      rw [Nat.card_units, show Nat.card K = 4 by rw [Nat.card_eq_fintype_card]; decide]
    have hx3 : ((x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ^ 3 = 1 := by
      have h := CFSG.LieType.Chevalley.ParSylow.torusGroup_pow_card_units
        (τ := Tag.E6) (K := K) hx
      rwa [h3] at h
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hx3

theorem e6FourX_mem_e6FourB : e6FourX ∈ e6FourB :=
  Subgroup.mem_subgroupOf.mpr e6FourToralElement_mem_torusGroup

private def e6FourNode0 : Fin Tag.E6.rank := ⟨0, by decide⟩

theorem e6FourToralParam_ne_one : e6FourToralParam ≠ 1 := by
  intro h
  have hχ := rootChar_e6FourToralParam (Pi.single e6FourNode0 (1 : ℤ))
  rw [h] at hχ
  have hone : rootChar (1 : Fin Tag.E6.rank → Kˣ) (Pi.single e6FourNode0 (1 : ℤ)) = 1 :=
    CFSG.RankThree.PartOne.KE.CTTorus.rootChar_one _
  rw [hone] at hχ
  have h3 : (3 : ℤ) ∣ ∑ k, e6FourToralExponent k *
      cartanCoord (Pi.single e6FourNode0 (1 : ℤ)) k := by
    rw [← omegaUnit_zpow_eq_one_iff, ← hχ]
  have hsum : ∑ k, e6FourToralExponent k *
      cartanCoord (Pi.single e6FourNode0 (1 : ℤ)) k = -1 := by
    decide
  rw [hsum] at h3
  norm_num at h3

theorem e6FourX_ne_one : e6FourX ≠ 1 := by
  intro h
  have h1 : rootDiagUnit Tag.E6 e6FourToralParam = 1 :=
    congrArg (fun y : adjointGroup Tag.E6 K => (y : ModGL Tag.E6 K)) h
  exact e6FourToralParam_ne_one (rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm))


theorem subsystemGroup_le_adjointGroup_E6 :
    subsystemGroup Tag.E6 K setD ≤ adjointGroup Tag.E6 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, -, c, rfl | rfl⟩
  · exact xUnit_mem_adjointGroup i c
  · exact yUnit_mem_adjointGroup i c

noncomputable def e6FourJ_equiv_statedOmega :
    e6FourJ ≃* StatedOmega (StatedQuadPlus 4 K) :=
  (Subgroup.subgroupOfEquivOfLe subsystemGroup_le_adjointGroup_E6).trans
    (psiDEquiv.trans
      (CFSG.ClassicalGroups.Orthogonal.statedOmegaEquiv
        (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K)
        (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus
          (n := 4) (K := K) (by norm_num))).symm)

theorem isQuasisimple_e6FourJ : CFSG.IsQuasisimple e6FourJ :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv e6FourJ_equiv_statedOmega.symm
    (CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadPlus (K := K) (n := 4) (by norm_num))

theorem subsingleton_scalars_statedOmega_quadPlus :
    (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf
      (StatedOmega (StatedQuadPlus 4 K)) = ⊥ := by
  refine CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
    (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K)
    (CFSG.LieType.Universal.Spin.exists_map_ne_zero_of_hypPair
      (CFSG.LieType.Universal.Spin.quadPlus 4 K)
      (CFSG.ClassicalGroups.Orthogonal.plusPair K ⟨0, by omega⟩))

noncomputable def statedProj_statedOmega_quadPlus_equiv :
    StatedProj (StatedOmega (StatedQuadPlus 4 K)) ≃*
      StatedOmega (StatedQuadPlus 4 K) :=
  (QuotientGroup.quotientMulEquivOfEq subsingleton_scalars_statedOmega_quadPlus).trans
    QuotientGroup.quotientBot

theorem center_e6FourJ : Subgroup.center e6FourJ = ⊥ := by
  have hc : Subgroup.center (StatedOmega (StatedQuadPlus 4 K)) = ⊥ := by
    rw [CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus (n := 4) (by norm_num),
      subsingleton_scalars_statedOmega_quadPlus]
  exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e6FourJ_equiv_statedOmega hc

theorem statedClassicalModel_e6FourJ :
    CFSG.Open.StatedClassicalModel
      (e6FourJ ⧸ Subgroup.center e6FourJ) .POmegaPlus 4 2 2 := by
  have hcard : Nat.card K = 4 := by
    rw [Nat.card_eq_fintype_card]; decide
  refine ⟨⟨Nat.prime_two, by norm_num, by norm_num⟩, K, inferInstance, inferInstance,
    ?_, ?_⟩
  · simpa using hcard
  · exact ⟨((QuotientGroup.quotientMulEquivOfEq center_e6FourJ).trans
        QuotientGroup.quotientBot).trans
        (e6FourJ_equiv_statedOmega.trans statedProj_statedOmega_quadPlus_equiv.symm)⟩

theorem hasLabel_e6FourJ : HasLabel e6FourJ (· = ⟨.D, 4, 2⟩) :=
  hasLabel_of_statedClassicalModel_POmegaPlus isQuasisimple_e6FourJ
    statedClassicalModel_e6FourJ


theorem e6FourJ_mult :
    (Subgroup.center e6FourJ = ⊥ ∧ TrivialMultiplierT e6FourJ) ∧
      Odd (Nat.card (Subgroup.center e6FourJ)) ∧
      12 ≤ twoRank e6FourJ ∧
      (∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ (2 * 2) - 1 →
        r ∣ Nat.card (e6FourJ ⧸ Subgroup.center e6FourJ)) :=
  omegaPlusEightFour_mult hasLabel_e6FourJ
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

theorem dvd_e6FourJ : 5 * 3 ∣ Nat.card (e6FourJ ⧸ Subgroup.center e6FourJ) := by
  have h := e6FourJ_mult.2.2.2
  have h15 : 2 ^ (2 * 2) - 1 = 15 := by norm_num
  have h3 : 3 ∣ Nat.card (e6FourJ ⧸ Subgroup.center e6FourJ) :=
    h 3 Nat.prime_three (by norm_num) (by rw [h15]; norm_num)
  have h5 : 5 ∣ Nat.card (e6FourJ ⧸ Subgroup.center e6FourJ) :=
    h 5 Nat.prime_five (by norm_num) (by rw [h15]; norm_num)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h5 h3

theorem e6Four_JShape {lab : GLALabel}
    (hlab : HasLabel (adjointGroup Tag.E6 K) (fun l : GLALabel => l = lab)) :
    JShape lab (3 ∣ Nat.card (Subgroup.center (adjointGroup Tag.E6 K))) ⟨.D, 4, 2⟩ := by
  have hlabE6 : HasLabel (adjointGroup Tag.E6 K) (· = ⟨.E6, 0, 2⟩) := by
    have hcard : Nat.card K = 4 := by rw [Nat.card_eq_fintype_card]; decide
    exact hasLabel_adjointGroup_E6 (F := K) (n := 2) (by rw [hcard]; norm_num) (by norm_num)
  have hcenter : Subgroup.center (adjointGroup Tag.E6 K) = ⊥ := center_adjointGroup_eq_bot
  have he : 4 ≤ evenRank (adjointGroup Tag.E6 K) := by
    have hcard : Nat.card K = 4 := by rw [Nat.card_eq_fintype_card]; decide
    rw [evenRank_adjointGroup_E6_two (F := K) hcard]
    norm_num
  rcases label_eq_or_BC he hlab hlabE6 with hEq | ⟨ht, ht', -, -⟩
  · subst hEq
    simp [JShape]
  · exact absurd ht' (by simp)


theorem e6FourJ_le_centralizer :
    e6FourJ ≤ Subgroup.centralizer ({e6FourX} : Set (adjointGroup Tag.E6 K)) := by
  intro j hj
  have hj' : (j : ModGL Tag.E6 K) ∈ toralCentralizer Tag.E6 K e6FourToralParam :=
    subsystemGroup_le_toralCentralizer_e6FourToralParam (Subgroup.mem_subgroupOf.mp hj)
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  apply Subtype.ext
  have hc := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hj').2)
    (rootDiagUnit Tag.E6 e6FourToralParam) rfl
  exact hc.symm


end CFSG.LocalAnalysis.GLTheoremA.Y10F

