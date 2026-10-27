module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentGrp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentKey
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
public import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmMinusStdGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om7
public import CFSG.Assembly.OpenBridges

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem layer_eq_of_fixedSpace_eight (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 5) {y : ↥(orthDerived Q)} (hy3 : orderOf y = 3)
    (hfix : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * 4) :
    GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))) =
        (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) ∧
      IsComponentOf ((supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q))
        (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3' : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy3] at h
    exact congrArg Subtype.val h
  have hyO : (y : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup y.2
  have hx := oddOrderIsometry_three hQ hyO hy3'
  let W := fixedSpace (y : V ≃ₗ[ZMod 2] V)
  have hWdim : finrank (ZMod 2) W = 8 := hfix
  have hT : ∃ U : Submodule (ZMod 2) W, finrank (ZMod 2) U = 3 ∧
      ∀ u ∈ U, (Q.comp W.subtype) u = 0 :=
    CFSG.StandardType.OrthRestOdd.exists_totallySingular_three (Q.comp W.subtype)
      hx.polarBilin_fixed_nondegenerate (by rw [hWdim])
  have hAq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)) :=
    hx.isQuasisimple_supportedFixedDerived hT
  have hAΩ : supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V) ≤ orthDerived Q :=
    hx.supportedFixedDerived_le_orthDerived
  set D : Subgroup ↥(orthDerived Q) :=
    (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) with hD
  have hDq : CFSG.IsQuasisimple ↥D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAΩ).symm hAq
  have hDC : D ≤ Subgroup.centralizer ({y} : Set ↥(orthDerived Q)) := fun g hg =>
    mem_centralizer_of_mem_isometryCentralizer
      (supportedFixedDerived_le_isometryCentralizer (Subgroup.mem_subgroupOf.1 hg))
  have hcomm := commutator_centralizer_le_supportedFixedDerived hQ hy3 (by rw [hfix, hdim])
  exact glaLayer_eq_of_commutator_le hDC hcomm hDq

theorem not_smallOrd_layer_of_fixedSpace_eight (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 5) {y : ↥(orthDerived Q)} (hy3 : orderOf y = 3)
    (hfix : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * 4) :
    ¬ HStdExcl.SmallOrd (GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlayer := (layer_eq_of_fixedSpace_eight hQ hdim hy3 hfix).1
  have hy3' : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy3] at h
    exact congrArg Subtype.val h
  have hyO : (y : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup y.2
  have hx := oddOrderIsometry_three hQ hyO hy3'
  let W := fixedSpace (y : V ≃ₗ[ZMod 2] V)
  have hWdim : finrank (ZMod 2) W = 2 * 4 := hfix
  have hndW : (polarBilin (Q.comp W.subtype)).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  have hAΩ : supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V) ≤ orthDerived Q :=
    hx.supportedFixedDerived_le_orthDerived
  have hcardA : Nat.card ↥(supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)) =
      Nat.card ↥(orthDerived (Q.comp W.subtype)) :=
    Nat.card_congr (restrictDerivedEquiv hx).toEquiv
  have hcardLayer : Nat.card ↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) =
      Nat.card ↥(orthDerived (Q.comp W.subtype)) := by
    rw [hlayer]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAΩ).toEquiv]
    exact hcardA
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hT : ∃ U : Submodule (ZMod 2) W, finrank (ZMod 2) U = 3 ∧
      ∀ u ∈ U, (Q.comp W.subtype) u = 0 :=
    CFSG.StandardType.OrthRestOdd.exists_totallySingular_three (Q.comp W.subtype)
      hndW (by rw [hWdim])
  have hcenterW : Subgroup.center ↥(orthDerived (Q.comp W.subtype)) = ⊥ :=
    CFSG.RankThree.PartOne.center_orthDerived_eq_bot hndW hT
  have hcenterA : Subgroup.center ↥(supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)) = ⊥ :=
    CFSG.AGLEmbedding.center_eq_bot_of_mulEquiv (restrictDerivedEquiv hx) hcenterW
  have hcenterLayer :
      Subgroup.center ↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) = ⊥ := by
    rw [hlayer]
    exact CFSG.AGLEmbedding.center_eq_bot_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hAΩ) hcenterA
  have h7 : 7 ∣ Nat.card ↥(orthDerived (Q.comp W.subtype)) := by
    by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp W.subtype)
    · exact seven_dvd_card_orthDerived_plus_eight hndW hWdim hplus
    · exact seven_dvd_card_orthDerived_minus_eight hndW hWdim hplus
  intro hs
  unfold HStdExcl.SmallOrd at hs
  have hquot : Nat.card (↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) ⧸
      Subgroup.center ↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))))) =
      Nat.card ↥(GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q)))) :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hcenterLayer).trans
      QuotientGroup.quotientBot).toEquiv
  rw [hquot, hcardLayer] at hs
  rcases hs with h | h <;> rw [h] at h7 <;> norm_num at h7


set_option maxHeartbeats 800000 in
theorem isCompl_blockSpace_iSup_erase {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A]
    [DecidableEq (Hyperplane A 3)] (hp : Nat.Prime 3) (hpF : (3 : ZMod 2) ≠ 0)
    (hA : IsElemAbelian 3 A) {D0 : Hyperplane A 3} :
    IsCompl (blockSpace A D0.1)
      (fixedSpaceOf A ⊔ ⨆ D : {D : Hyperplane A 3 // D ≠ D0}, blockSpace A D.1.1) := by
  classical
  have hsplit : (⨆ D : Hyperplane A 3, blockSpace A D.1) =
      blockSpace A D0.1 ⊔ ⨆ D : {D : Hyperplane A 3 // D ≠ D0}, blockSpace A D.1.1 := by
    apply le_antisymm
    · refine iSup_le fun D => ?_
      by_cases hD : D = D0
      · subst hD
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup (fun E : {E : Hyperplane A 3 // E ≠ D0} =>
          blockSpace A E.1.1) ⟨D, hD⟩)
    · refine sup_le (le_iSup (fun D => blockSpace A D.1) D0) ?_
      exact iSup_le fun D => le_iSup (fun E => blockSpace A E.1) D.1
  have htop : blockSpace A D0.1 ⊔
      (fixedSpaceOf A ⊔ ⨆ D : {D : Hyperplane A 3 // D ≠ D0}, blockSpace A D.1.1) = ⊤ := by
    have h1 := sup_fixedSpaceOf_iSup_blockSpace A hp hpF hA
    rw [hsplit] at h1
    rw [← h1]
    ac_rfl
  have hinf : blockSpace A D0.1 ⊓
      (fixedSpaceOf A ⊔ ⨆ D : {D : Hyperplane A 3 // D ≠ D0}, blockSpace A D.1.1) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hpv : projBlock A hp hpF hA D0 v = v := projBlock_apply_of_mem A hp hpF hA D0 hv.1
    obtain ⟨c, hc, u, hu, rfl⟩ := Submodule.mem_sup.mp hv.2
    have hc0 : projBlock A hp hpF hA D0 c = 0 := projBlock_apply_fixed A hp hpF hA D0 hc
    have hu0 : projBlock A hp hpF hA D0 u = 0 := by
      refine Submodule.iSup_induction
        (fun D : {D : Hyperplane A 3 // D ≠ D0} => blockSpace A D.1.1)
        (motive := fun u => projBlock A hp hpF hA D0 u = 0) hu ?_ ?_ ?_
      · intro D w hw
        exact projBlock_apply_of_mem_block A hp hpF hA (D := D0) (E := D.1)
          D.2 hw
      · simp
      · intro x y hx hy
        rw [map_add, hx, hy, add_zero]
    have hzero : c + u = 0 := by
      rw [← hpv, map_add, hc0, hu0, add_zero]
    rw [hzero, Submodule.mem_bot]
  exact ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr htop⟩

set_option maxHeartbeats 800000 in
theorem four_blocks_impossible (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 5)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    {Bb : Subgroup ↥(orthDerived Q)} [Fintype ↥(orthImage Bb)]
    (h : SmallModel ↥(orthDerived Q) Bb)
    (h4 : (blockSet (orthImage Bb)).card = 4) : False := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V ≃ₗ[ZMod 2] V) := CFSG.LargeExtraspecial.O62.finite_linearEquiv
  haveI : DecidableEq (Hyperplane (orthImage Bb) 3) := Classical.decEq _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A : Subgroup (V ≃ₗ[ZMod 2] V) := orthImage Bb
  have hAe : IsElemAbelian 3 A := isElemAbelian_orthImage (Ã := Bb) h.elem
  have hAcard : Nat.card ↥A = 3 ^ 4 := by
    change Nat.card ↥(Bb.map (orthDerived Q).subtype) = 3 ^ 4
    rw [Subgroup.card_map_of_injective (orthDerived Q).subtype_injective,
      card_eq_three_pow_four_of_smallModel_minus_five hQ hdim hminus h]
  have hB : ∀ a : ↥A, ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[ZMod 2] V) u) ((a : V ≃ₗ[ZMod 2] V) v) = polarBilin Q u v :=
    fun a => polar_orthImage (Ã := Bb) a
  have hfaith : ∀ a : ↥A, (∀ v : V, (a : V ≃ₗ[ZMod 2] V) v = v) → a = 1 := by
    rintro ⟨a, ha⟩ hfix
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ha
    have hb1 : b = 1 := Subtype.ext (LinearEquiv.ext fun v => by
      simpa using hfix v)
    exact Subtype.ext (by simpa using congrArg Subtype.val hb1)
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpF : (3 : ZMod 2) ≠ 0 := by decide
  have hall : (⨅ D ∈ blockSet A, D.1) = ⊥ := iInf_blockSet_eq_bot hp hpF hAe hfaith
  obtain ⟨D0, hD0mem, hdimD0⟩ := exists_plane_block_of_card_four hQ hAe hdim hB h4
  obtain ⟨yA, hyS, hyD0⟩ := exists_mem_iInf_erase_not_mem hAcard h4 hD0mem hall
  have hyA1 : yA ≠ 1 := fun h1 => hyD0 (h1 ▸ D0.1.one_mem)
  have hSyz : (⨅ D : {D // D ∈ (blockSet A).erase D0}, D.1.1) = Subgroup.zpowers yA :=
    iInf_erase_eq_zpowers hAe hAcard h4 hD0mem hall hyS hyA1
  obtain ⟨y, hyB, hyval⟩ := Subgroup.mem_map.1 yA.2
  have hyval' : (y : V ≃ₗ[ZMod 2] V) = ((yA : ↥A) : V ≃ₗ[ZMod 2] V) := hyval
  have hy1 : y ≠ 1 := by
    intro h1
    apply hyA1
    exact Subtype.ext (by rw [← hyval']; exact congrArg Subtype.val h1)
  have hy3 : orderOf y = 3 := by
    have hy3A : yA ^ 3 = 1 := by
      have := pow_orderOf_eq_one yA
      rw [orderOf_eq_prime (Subtype.ext (by simpa using hAe.2 yA yA.2)) hyA1] at this
      exact this
    have hy3lin : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := by
      have h2 : ((yA ^ 3 : ↥A) : V ≃ₗ[ZMod 2] V) = 1 := by rw [hy3A]; rfl
      have h3 : ((yA : ↥A) : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := by
        simpa using h2
      rwa [← hyval'] at h3
    rw [orderOf_eq_prime (Subtype.ext hy3lin) hy1]
  let P : Submodule (ZMod 2) V := blockSpace A D0.1
  let W : Submodule (ZMod 2) V :=
    fixedSpaceOf A ⊔ ⨆ D : {D : Hyperplane A 3 // D ≠ D0}, blockSpace A D.1.1
  have hcompl : IsCompl P W := isCompl_blockSpace_iSup_erase hp hpF hAe
  have hdimP : finrank (ZMod 2) P = 2 := hdimD0
  have hWdim : finrank (ZMod 2) W = 8 := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hdimP, hdim] at h
    omega
  have hyC : ∀ c ∈ fixedSpaceOf A, (y : V ≃ₗ[ZMod 2] V) c = c := by
    intro c hc
    rw [hyval']
    exact (mem_fixedSpaceOf A).1 hc yA
  have hyW : ∀ w ∈ W, (y : V ≃ₗ[ZMod 2] V) w = w := by
    intro w hw
    obtain ⟨c, hc, u, hu, rfl⟩ := Submodule.mem_sup.mp hw
    have hu' : (y : V ≃ₗ[ZMod 2] V) u = u := by
      refine Submodule.iSup_induction
        (fun D : {D : Hyperplane A 3 // D ≠ D0} => blockSpace A D.1.1)
        (motive := fun u => (y : V ≃ₗ[ZMod 2] V) u = u) hu ?_ ?_ ?_
      · intro D w hw
        rw [hyval']
        by_cases hD : D.1 ∈ blockSet A
        · exact (mem_blockSpace A).1 hw |>.1 yA (hyS D.1 (Finset.mem_erase.2 ⟨D.2, hD⟩))
        · have hbot : blockSpace A D.1.1 = ⊥ := blockSpace_eq_bot_of_not_mem_blockSet hD
          rw [hbot, Submodule.mem_bot] at hw
          rw [hw, map_zero]
      · exact map_zero _
      · intro x x' hx hx'
        rw [map_add, hx, hx']
    rw [map_add, hyC c hc, hu']
  let F : Submodule (ZMod 2) V := fixedSpace (y : V ≃ₗ[ZMod 2] V)
  have hWeq : W ≤ F := by
    intro w hw
    rw [show F = fixedSpace (y : V ≃ₗ[ZMod 2] V) from rfl,
      CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace]
    exact hyW w hw
  have htop : F ⊔ P = ⊤ := by
    rw [eq_top_iff, ← hcompl.sup_eq_top]
    calc P ⊔ W ≤ P ⊔ F := sup_le_sup_left hWeq P
      _ = F ⊔ P := sup_comm ..
  let I : Submodule (ZMod 2) V := F ⊓ P
  have hmod : 10 + finrank (ZMod 2) I = finrank (ZMod 2) F + 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq F P
    rw [htop, finrank_top, hdim, hdimP] at h
    simpa [I] using h
  have hy3lin : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy3] at this
    exact congrArg Subtype.val this
  have hyO : (y : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup y.2
  have hEven : Even (finrank (ZMod 2) F) :=
    even_finrank_fixedSpace (oddOrderIsometry_three hQ hyO hy3lin) (by decide)
  have hinfle : finrank (ZMod 2) I ≤ 2 := by
    calc finrank (ZMod 2) I ≤ finrank (ZMod 2) P :=
          Submodule.finrank_mono (show I ≤ P from inf_le_right)
      _ = 2 := hdimP
  have hfix8 : finrank (ZMod 2) F = 8 := by
    have hne1 : finrank (ZMod 2) I ≠ 1 := by
      intro h1
      rw [h1] at hmod
      obtain ⟨k, hk⟩ := hEven
      omega
    have hcases : finrank (ZMod 2) I = 0 ∨ finrank (ZMod 2) I = 2 := by
      interval_cases finrank (ZMod 2) I
      · exact Or.inl rfl
      · exact absurd rfl hne1
      · exact Or.inr rfl
    rcases hcases with h0 | h2
    · omega
    · exfalso
      have h10 : finrank (ZMod 2) F = 10 := by omega
      have htopfix : F = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [h10, hdim]
      have hy1lin : (y : V ≃ₗ[ZMod 2] V) = 1 := by
        apply LinearEquiv.ext
        intro v
        have hv : v ∈ F := by
          rw [htopfix]
          exact Submodule.mem_top
        rw [show F = fixedSpace (y : V ≃ₗ[ZMod 2] V) from rfl,
          CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace] at hv
        exact hv
      have ha1 : (⟨(y : V ≃ₗ[ZMod 2] V), Subgroup.mem_map_of_mem _ hyB⟩ : ↥A) = 1 :=
        hfaith _ (fun v => by rw [hy1lin]; rfl)
      exact hy1 (Subtype.ext (by simpa using congrArg Subtype.val ha1))
  have hyfix8 : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * 4 := by
    rw [hfix8]
  have hyfixW : fixedSpace (y : V ≃ₗ[ZMod 2] V) = W := by
    have hEq : W = F :=
      Submodule.eq_of_le_of_finrank_eq hWeq (by rw [hWdim, hfix8])
    exact hEq.symm
  have hlayer := layer_eq_of_fixedSpace_eight hQ hdim hy3 hyfix8
  have hnsmall := not_smallOrd_layer_of_fixedSpace_eight hQ hdim hy3 hyfix8
  have hT : ∃ U : Submodule (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)),
      finrank (ZMod 2) U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace (y : V ≃ₗ[ZMod 2] V)).subtype) u = 0 :=
    CFSG.StandardType.OrthRestOdd.exists_totallySingular_three
      (Q.comp (fixedSpace (y : V ≃ₗ[ZMod 2] V)).subtype)
      (oddOrderIsometry_three hQ hyO hy3lin).polarBilin_fixed_nondegenerate (by rw [hfix8])
  have hcent : Bb ⊓ Subgroup.centralizer
      (GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers y := by
    apply le_antisymm
    · intro b hb'
      obtain ⟨hbB, hbc⟩ := Subgroup.mem_inf.1 hb'
      have hcomm : (⟨b, hbB⟩ : ↥Bb) * ⟨y, hyB⟩ = ⟨y, hyB⟩ * ⟨b, hbB⟩ :=
        h.elem.1.is_comm.comm ⟨b, hbB⟩ ⟨y, hyB⟩
      have hcomm' : (b : ↥(orthDerived Q)) * y = y * b := by
        have h := congrArg (fun z : ↥Bb => (z : ↥(orthDerived Q))) hcomm
        simpa using h
      have hbW : ∀ w ∈ fixedSpace (y : V ≃ₗ[ZMod 2] V), (b : V ≃ₗ[ZMod 2] V) w = w := by
        refine
          CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.apply_eq_of_commute_supportedFixedDerived_gen
            (oddOrderIsometry_three hQ hyO hy3lin) hT ?_ ?_
        · refine mem_isometryCentralizer.2
            ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (orthDerived_le_orthogonalGroup b.2),
              fun v => ?_⟩
          have h := congrArg (fun f : ↥(orthDerived Q) => (f : V ≃ₗ[ZMod 2] V) v) hcomm'
          simpa using h
        · intro g hg
          have hgle : supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V) ≤ orthDerived Q :=
            (oddOrderIsometry_three hQ hyO hy3lin).supportedFixedDerived_le_orthDerived
          have hgG : (⟨g, hgle hg⟩ : ↥(orthDerived Q)) ∈
              (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) :=
            Subgroup.mem_subgroupOf.2 hg
          have hmem : (⟨g, hgle hg⟩ : ↥(orthDerived Q)) ∈
              GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))) := by
            rw [hlayer.1]
            exact hgG
          have h := congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hbc _ hmem)
          simpa using h.symm
      let bA : ↥A := ⟨(b : V ≃ₗ[ZMod 2] V), Subgroup.mem_map_of_mem _ hbB⟩
      have hbD : ∀ D : {D // D ∈ (blockSet A).erase D0}, bA ∈ D.1.1 := by
        intro D
        refine mem_of_forall_mem_blockSpace hp hpF hAe (D := D.1)
          (Finset.mem_erase.1 D.2).2 ?_
        intro v hv
        have hwF : v ∈ F := by
          rw [show F = W from hyfixW]
          exact le_sup_of_le_right (le_iSup
            (fun E : {E : Hyperplane A 3 // E ≠ D0} => blockSpace A E.1.1)
            ⟨D.1, (Finset.mem_erase.1 D.2).1⟩) hv
        exact hbW v hwF
      have hbS : bA ∈ (⨅ D : {D // D ∈ (blockSet A).erase D0}, D.1.1) :=
        Subgroup.mem_iInf.mpr hbD
      rw [hSyz] at hbS
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hbS
      refine Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩
      have hk' : ((yA : ↥A) : V ≃ₗ[ZMod 2] V) ^ k = (b : V ≃ₗ[ZMod 2] V) := by
        have h := congrArg (fun z : ↥A => (z : V ≃ₗ[ZMod 2] V)) hk
        simpa using h
      simpa [hyval'] using hk'
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_inf.2 ⟨hyB, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [hlayer.1] at hg
      exact (Subgroup.mem_centralizer_iff.1 (hlayer.2.1 hg) y (Set.mem_singleton y)).symm
  refine hnsmall (h.small y hyB hy1 ?_)
  refine ⟨?_, hcent⟩
  rw [hlayer.1]
  exact hlayer.2
end CFSG.LocalAnalysis.GLTheoremA.T171S

end
