module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166OmBlocks3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Build
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Iso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2EUp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TablesHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperShared
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimpleBasic
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSp
public import CFSG.ClassicalInvolution.SmallOrth.PlusFourMain
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapParam
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GroupTheory.GeneratorBounds
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviAssembly
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviCard
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.Quasithin.Background.F918D5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Subgroup CFSG.Open
open CFSG.SeitzReduction.OmegaPilot CFSG.SeitzReduction.SymplecticPilot
open CFSG.StandardType CFSG.StandardType.InnerDiagA CFSG.StandardType.LinSemisimple
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2]

namespace DFour

theorem JOmega_eq_omegaLeviSL_subgroupOf (hF : 4 ≤ Nat.card F) :
    OmegaSiegel.JOmega (F := F) hF =
      (omegaLeviSL F 4).subgroupOf (StatedOmega (StatedQuadPlus 4 F)) := by
  apply le_antisymm
  · intro x hx
    rw [OmegaSiegel.JOmega_eq, Subgroup.mem_map] at hx
    obtain ⟨A, hA, rfl⟩ := hx
    rw [OmegaSiegel.SLGL] at hA
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hA
    rw [Subgroup.mem_subgroupOf, omegaLeviSL, Subgroup.mem_map]
    refine ⟨leviEmbedSL F 4 a, ?_, rfl⟩
    exact MonoidHom.mem_range.2 ⟨a, rfl⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [omegaLeviSL, Subgroup.mem_map] at hx
    obtain ⟨C, hC, hCx⟩ := hx
    rw [siegelLevi] at hC
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hC
    rw [OmegaSiegel.JOmega_eq, Subgroup.mem_map]
    refine ⟨Matrix.SpecialLinearGroup.toGL a, ?_, ?_⟩
    · rw [OmegaSiegel.SLGL]
      exact MonoidHom.mem_range.2 ⟨a, rfl⟩
    · apply Subtype.ext
      rw [← hCx]
      rfl

theorem JOmega_le_centralizer_xOmega (hF : 4 ≤ Nat.card F) (s : Fˣ) :
    OmegaSiegel.JOmega (F := F) hF ≤
      Subgroup.centralizer ({OmegaSiegel.xOmega (F := F) s} :
        Set (StatedOmega (StatedQuadPlus 4 F))) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [OmegaSiegel.JOmega_eq, Subgroup.mem_map] at hx
  obtain ⟨A, hA, rfl⟩ := hx
  rw [OmegaSiegel.SLGL] at hA
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hA
  have hx' : OmegaSiegel.xOmega (F := F) s =
      OmegaSiegel.leviOmega (F := F) hF (OmegaSiegel.xGL (F := F) s) :=
    OmegaSiegel.xOmega_eq_leviOmega_xGL hF s
  rw [hx', ← map_mul, ← map_mul]
  have hcomm : Matrix.SpecialLinearGroup.toGL a * OmegaSiegel.xGL (F := F) s =
      OmegaSiegel.xGL (F := F) s * Matrix.SpecialLinearGroup.toGL a := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, OmegaSiegel.xGL, TauCeti.diagGL_coe]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
  exact congrArg (fun z => OmegaSiegel.leviOmega (F := F) hF z) hcomm

private theorem SOmega_ne_bot (hF : 4 ≤ Nat.card F) : OmegaSiegel.SOmega (F := F) hF ≠ ⊥ := by
  intro hbot
  have hij : (0 : Fin 4) ≠ 1 := by decide
  have hlt : (0 : Fin 4) < 1 := by decide
  have hT : Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection hij (1 : F)) ∈ OmegaSiegel.SGL (F := F) :=
    Subgroup.mem_map.2 ⟨_, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.transvection_mem_unitriangular
      hlt 1, rfl⟩
  have hTΩ : OmegaSiegel.leviOmega (F := F) hF (Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection hij (1 : F))) ∈ OmegaSiegel.SOmega (F := F) hF :=
    Subgroup.mem_map.2 ⟨_, hT, rfl⟩
  rw [hbot] at hTΩ
  have h1 : OmegaSiegel.leviOmega (F := F) hF (Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection hij (1 : F))) = 1 := Subgroup.mem_bot.1 hTΩ
  have h2 : Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection hij (1 : F)) = Matrix.SpecialLinearGroup.toGL 1 :=
    OmegaSiegel.leviOmega_injective hF (by simpa using h1)
  have h3 : Matrix.SpecialLinearGroup.transvection hij (1 : F) = 1 :=
    Matrix.SpecialLinearGroup.toGL_injective (by simpa using h2)
  have h00 : ((Matrix.SpecialLinearGroup.transvection hij (1 : F) :
      Matrix (Fin 4) (Fin 4) F)) 0 1 = (1 : F) := by
    rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
      Matrix.one_apply_ne hij, Matrix.single_apply]
    simp [hij]
  rw [h3, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hij] at h00
  exact one_ne_zero h00.symm

theorem four_le_evenRank_statedOmega_quadPlus (hF : 4 ≤ Nat.card F) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hdvd : q ∣ Nat.card F - 1) {n : ℕ} (hpow : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    4 ≤ evenRank (StatedOmega (StatedQuadPlus 4 F)) := by
  have hloc : IsTwoLocal
      (Subgroup.normalizer (OmegaSiegel.SOmega (F := F) hF : Set
        (StatedOmega (StatedQuadPlus 4 F)))) :=
    ⟨_, SOmega_ne_bot hF, OmegaSiegel.isPGroup_two_SOmega hF hpow, rfl⟩
  have hle : 4 ≤ CFSG.Open.pRank q
      (Subgroup.normalizer (OmegaSiegel.SOmega (F := F) hF : Set
        (StatedOmega (StatedQuadPlus 4 F)))) :=
    CFSG.SectionRank.le_pRank hq.one_lt (OmegaSiegel.BOmega_le_normalizer_SOmega hF q)
      (OmegaSiegel.isElemAbelian_BOmega hF q hdvd) (OmegaSiegel.card_BOmega hF q hq hdvd)
  exact hle.trans (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank q hq hq2 _ hloc)

private noncomputable def eParamD4 (q : ℕ) :
    (Fin 3 → rootsOfUnity q F) →* (Fin 4 → rootsOfUnity q F) where
  toFun e := ![e 0 * e 2, e 1 * e 2, e 2, e 2]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' e e' := by
    funext i
    fin_cases i <;> simp [mul_assoc, mul_left_comm, mul_comm]

private theorem eParamD4_injective (q : ℕ) : Function.Injective (eParamD4 (F := F) q) := by
  intro e e' h
  have h0 : e 0 * e 2 = e' 0 * e' 2 := by simpa [eParamD4] using congrFun h 0
  have h1 : e 1 * e 2 = e' 1 * e' 2 := by simpa [eParamD4] using congrFun h 1
  have h2 : e 2 = e' 2 := by simpa [eParamD4] using congrFun h 2
  funext i
  fin_cases i <;> simp_all

private noncomputable def ED4 (q : ℕ) : Subgroup (GL (Fin 4) F) :=
  ((OmegaSiegel.diagTorusGL (F := F) q).comp (eParamD4 (F := F) q)).range

private theorem ED4_le_BGL (q : ℕ) : ED4 (F := F) q ≤ OmegaSiegel.BGL (F := F) q := by
  rintro _ ⟨e, rfl⟩
  exact MonoidHom.mem_range.2 ⟨eParamD4 (F := F) q e, rfl⟩

private theorem card_ED4 (q : ℕ) (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1) :
    Nat.card (ED4 (F := F) q) = q ^ 3 := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hinj : Function.Injective
      ((OmegaSiegel.diagTorusGL (F := F) q).comp (eParamD4 (F := F) q)) :=
    (OmegaSiegel.diagTorusGL_injective q).comp (eParamD4_injective q)
  rw [ED4, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj]
  rw [show Nat.card ↥(⊤ : Subgroup (Fin 3 → rootsOfUnity q F)) =
      Nat.card (Fin 3 → rootsOfUnity q F) from
    Nat.card_congr Subgroup.topEquiv.toEquiv]
  rw [Nat.card_pi]
  simp only [CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := F) (d := q) hdvd]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem isElemAbelian_ED4 (q : ℕ) (hdvd : q ∣ Nat.card F - 1) :
    IsElemAbelian q (ED4 (F := F) q) := by
  have h := (OmegaPair.isElemAbelian_top_pi_rootsOfUnity (K := F) 3 q hdvd).map
    ((OmegaSiegel.diagTorusGL (F := F) q).comp (eParamD4 (F := F) q))
  change IsElemAbelian q
    ((OmegaSiegel.diagTorusGL (F := F) q).comp (eParamD4 (F := F) q)).range
  rw [Subgroup.map_top] at h
  exact h

private noncomputable def ED4Omega (hF : 4 ≤ Nat.card F) (q : ℕ) :
    Subgroup (StatedOmega (StatedQuadPlus 4 F)) :=
  (ED4 (F := F) q).map (OmegaSiegel.leviOmega (F := F) hF)

private theorem card_ED4Omega (hF : 4 ≤ Nat.card F) (q : ℕ) (hq : q.Prime)
    (hdvd : q ∣ Nat.card F - 1) : Nat.card (ED4Omega (F := F) hF q) = q ^ 3 := by
  rw [ED4Omega, Subgroup.card_map_of_injective (OmegaSiegel.leviOmega_injective hF)]
  exact card_ED4 q hq hdvd

private theorem isElemAbelian_ED4Omega (hF : 4 ≤ Nat.card F) (q : ℕ) (hdvd : q ∣ Nat.card F - 1) :
    IsElemAbelian q (ED4Omega (F := F) hF q) :=
  (isElemAbelian_ED4 (F := F) q hdvd).map (OmegaSiegel.leviOmega (F := F) hF)

private theorem ED4Omega_le_BOmega (hF : 4 ≤ Nat.card F) (q : ℕ) :
    ED4Omega (F := F) hF q ≤ OmegaSiegel.BOmega (F := F) hF q :=
  Subgroup.map_mono (ED4_le_BGL q)

theorem hasLabel_statedOmega_quadPlus_four {n : ℕ} (hn : 2 ≤ n)
    (hFcard : Nat.card F = 2 ^ n) :
    HasLabel (StatedOmega (StatedQuadPlus 4 F)) (fun l : GLALabel => l = ⟨.D, 4, n⟩) := by
  have hq : CFSG.IsQuasisimple (StatedOmega (StatedQuadPlus 4 F)) :=
    CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadPlus (by norm_num)
  have hZ : Subgroup.center (StatedOmega (StatedQuadPlus 4 F)) =
      (StatedScalars (Fin 4 ⊕ Fin 4) F).subgroupOf (StatedOmega (StatedQuadPlus 4 F)) :=
    CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus (by norm_num)
  have hSCproj : StatedClassicalModel
      (StatedProj (StatedOmega (StatedQuadPlus 4 F))) .POmegaPlus 4 2 n :=
    ⟨⟨Nat.prime_two, by omega, by norm_num⟩, F, inferInstance, inferInstance,
      hFcard, ⟨MulEquiv.refl _⟩⟩
  exact hasLabel_of_statedClassicalModel_POmegaPlus hq
    (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hZ).symm hSCproj)

private noncomputable def eSLJ (hF : 4 ≤ Nat.card F) :
    Matrix.SpecialLinearGroup (Fin 4) F ≃* OmegaSiegel.JOmega (F := F) hF :=
  (MonoidHom.ofInjective (f := (OmegaSiegel.leviOmega (F := F) hF).comp
      Matrix.SpecialLinearGroup.toGL)
    ((OmegaSiegel.leviOmega_injective hF).comp
      Matrix.SpecialLinearGroup.toGL_injective)).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, OmegaSiegel.JOmega_eq, OmegaSiegel.SLGL]))

theorem isQuasisimple_JOmega (hF : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple (OmegaSiegel.JOmega (F := F) hF) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MulEquiv.subgroupCongr (JOmega_eq_omegaLeviSL_subgroupOf hF)).symm
    (isQuasisimple_omegaLeviSL_subgroupOf hF)

theorem hasLabel_JOmega (hF : 4 ≤ Nat.card F) {n : ℕ} (hn : 2 ≤ n)
    (hFcard : Nat.card F = 2 ^ n) :
    HasLabel (OmegaSiegel.JOmega (F := F) hF) (fun l : GLALabel => l = ⟨.D, 3, n⟩) := by
  have hJq : CFSG.IsQuasisimple (OmegaSiegel.JOmega (F := F) hF) := isQuasisimple_JOmega hF
  have hquot : (OmegaSiegel.JOmega (F := F) hF ⧸
      Subgroup.center (OmegaSiegel.JOmega (F := F) hF)) ≃*
      StatedProj (StatedSL 4 F) :=
    (QuotientGroup.congr (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F))
      (Subgroup.center (OmegaSiegel.JOmega (F := F) hF)) (eSLJ hF)
      (Subgroup.map_center_eq (eSLJ hF))).symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 F)
  have hadm : StatedLieAdmissible .PSL 4 2 n :=
    ⟨Nat.prime_two, by omega, by norm_num, by simp, by simp⟩
  have hSC : StatedClassicalModel
      (OmegaSiegel.JOmega (F := F) hF ⧸
        Subgroup.center (OmegaSiegel.JOmega (F := F) hF)) .PSL 4 2 n :=
    ⟨hadm, F, inferInstance, inferInstance, hFcard, ⟨hquot⟩⟩
  exact hasLabel_of_statedClassicalModel_PSL4_D hJq hSC

@[expose] noncomputable def eGenTriple (s : Fˣ) : Fin 3 → Fin 4 → Fˣ :=
  ![fun _ => s, ![s, 1, 1, 1], ![1, s, 1, 1]]

@[expose] noncomputable def eTripleOmega (hF : 4 ≤ Nat.card F) (s : Fˣ) :
    Fin 3 → StatedOmega (StatedQuadPlus 4 F) :=
  fun k => OmegaSiegel.leviOmega (F := F) hF (InnerDiagA.diagGL (eGenTriple s k))

@[expose] noncomputable def ED4Gen (hF : 4 ≤ Nat.card F) (s : Fˣ) :
    Subgroup (StatedOmega (StatedQuadPlus 4 F)) :=
  Subgroup.closure (Set.range (eTripleOmega (F := F) hF s))

private theorem closure_std_rootsOfUnity (q : ℕ) [NeZero q] {sμ : rootsOfUnity q F}
    (hs : orderOf (sμ : Fˣ) = q) :
    Subgroup.closure ({![sμ, 1, 1], ![1, sμ, 1], ![1, 1, sμ]} :
      Set (Fin 3 → rootsOfUnity q F)) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have hprim : IsPrimitiveRoot (sμ : Fˣ) q := by
    simpa only [hs] using IsPrimitiveRoot.orderOf (sμ : Fˣ)
  have hmem : ∀ i : Fin 3, ∃ k : ℤ, sμ ^ k = f i := by
    intro i
    have h : (f i : Fˣ) ∈ Subgroup.zpowers (sμ : Fˣ) := by
      rw [IsPrimitiveRoot.zpowers_eq hprim]
      exact (f i).2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  choose k hk using hmem
  have hf : f = (![sμ, 1, 1] : Fin 3 → rootsOfUnity q F) ^ (k 0) *
      (![1, sμ, 1] : Fin 3 → rootsOfUnity q F) ^ (k 1) *
      (![1, 1, sμ] : Fin 3 → rootsOfUnity q F) ^ (k 2) := by
    funext i
    fin_cases i
    · apply Subtype.ext
      change (f 0 : Fˣ) = (sμ : Fˣ) ^ (k 0) * (1 : Fˣ) ^ (k 1) * (1 : Fˣ) ^ (k 2)
      simp only [one_zpow, mul_one]
      exact congrArg Subtype.val (hk 0).symm
    · apply Subtype.ext
      change (f 1 : Fˣ) = (1 : Fˣ) ^ (k 0) * (sμ : Fˣ) ^ (k 1) * (1 : Fˣ) ^ (k 2)
      simp only [one_zpow, one_mul, mul_one]
      exact congrArg Subtype.val (hk 1).symm
    · apply Subtype.ext
      change (f 2 : Fˣ) = (1 : Fˣ) ^ (k 0) * (1 : Fˣ) ^ (k 1) * (sμ : Fˣ) ^ (k 2)
      simp only [one_zpow, one_mul, mul_one]
      exact congrArg Subtype.val (hk 2).symm
  rw [hf]
  set S : Set (Fin 3 → rootsOfUnity q F) := {![sμ, 1, 1], ![1, sμ, 1], ![1, 1, sμ]}
  have h0 : ![sμ, 1, 1] ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [S])
  have h1 : ![1, sμ, 1] ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [S])
  have h2 : ![1, 1, sμ] ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [S])
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.zpow_mem _ h0 (k 0)) (Subgroup.zpow_mem _ h1 (k 1)))
    (Subgroup.zpow_mem _ h2 (k 2))

private theorem map_std_rootsOfUnity_eq (hF : 4 ≤ Nat.card F) {q : ℕ} [NeZero q]
    {sμ : rootsOfUnity q F} {s : Fˣ} (hsμ : (sμ : Fˣ) = s) :
    ((OmegaSiegel.leviOmega (F := F) hF).comp
        ((OmegaSiegel.diagTorusGL (F := F) q).comp (eParamD4 (F := F) q)))
        ![sμ, 1, 1] = eTripleOmega (F := F) hF s 1 ∧
    ((OmegaSiegel.leviOmega (F := F) hF).comp
        ((OmegaSiegel.diagTorusGL (F := F) q).comp (eParamD4 (F := F) q)))
        ![1, sμ, 1] = eTripleOmega (F := F) hF s 2 ∧
    ((OmegaSiegel.leviOmega (F := F) hF).comp
        ((OmegaSiegel.diagTorusGL (F := F) q).comp (eParamD4 (F := F) q)))
        ![1, 1, sμ] = eTripleOmega (F := F) hF s 0 := by
  have hbridge : ∀ t : Fin 4 → Fˣ,
      OmegaSiegel.leviOmega (F := F) hF (TauCeti.diagGL t) =
        OmegaSiegel.leviOmega (F := F) hF (InnerDiagA.diagGL t) :=
    fun t => congrArg (OmegaSiegel.leviOmega (F := F) hF)
      (WitSp.innerDiagA_diagGL_eq (m := 3) t).symm
  have key : ∀ (g : Fin 3 → rootsOfUnity q F) (t : Fin 4 → Fˣ),
      (∀ i, ((eParamD4 (F := F) q g) i : Fˣ) = t i) →
      ((OmegaSiegel.leviOmega (F := F) hF).comp
        ((OmegaSiegel.diagTorusGL (F := F) q).comp (eParamD4 (F := F) q))) g =
        OmegaSiegel.leviOmega (F := F) hF (InnerDiagA.diagGL t) := by
    intro g t hgt
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, OmegaSiegel.diagTorusGL,
      MonoidHom.comp_apply]
    rw [show ((rootsOfUnity q F).subtype.compLeft (Fin 4)) (eParamD4 (F := F) q g) = t
      from funext hgt]
    exact hbridge t
  refine ⟨?_, ?_, ?_⟩
  · rw [eTripleOmega]
    exact key ![sμ, 1, 1] ![s, 1, 1, 1] (fun i => by fin_cases i <;> simp [eParamD4, hsμ])
  · rw [eTripleOmega]
    exact key ![1, sμ, 1] ![1, s, 1, 1] (fun i => by fin_cases i <;> simp [eParamD4, hsμ])
  · rw [eTripleOmega]
    exact key ![1, 1, sμ] (fun _ => s) (fun i => by fin_cases i <;> simp [eParamD4, hsμ])

private theorem ED4Gen_eq_ED4Omega (hF : 4 ≤ Nat.card F) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card F - 1) {s : Fˣ} (hs : orderOf s = q) :
    ED4Gen (F := F) hF s = ED4Omega (F := F) hF q := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  set sμ : rootsOfUnity q F := ⟨s, by
    rw [mem_rootsOfUnity q s, ← hs]; exact pow_orderOf_eq_one s⟩ with hsμdef
  have hsμ : (sμ : Fˣ) = s := rfl
  have hord : orderOf (sμ : Fˣ) = q := hs
  set Φ : (Fin 3 → rootsOfUnity q F) →* StatedOmega (StatedQuadPlus 4 F) :=
    (OmegaSiegel.leviOmega (F := F) hF).comp
      ((OmegaSiegel.diagTorusGL (F := F) q).comp (eParamD4 (F := F) q)) with hΦ
  have hE : ED4Omega (F := F) hF q = Φ.range := by
    have heq := MonoidHom.range_comp (OmegaSiegel.leviOmega (F := F) hF)
      ((OmegaSiegel.diagTorusGL (F := F) q).comp (eParamD4 (F := F) q))
    rw [ED4Omega, ED4, ← heq, ← hΦ]
  have h := map_std_rootsOfUnity_eq (F := F) hF (q := q) (sμ := sμ) (s := s) hsμ
  have hgen : ED4Gen (F := F) hF s = Subgroup.closure (Φ '' ({![sμ, 1, 1], ![1, sμ, 1],
      ![1, 1, sμ]} : Set (Fin 3 → rootsOfUnity q F))) := by
    rw [ED4Gen]
    congr 1
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      fin_cases k
      · exact ⟨![1, 1, sμ], by simp, h.2.2⟩
      · exact ⟨![sμ, 1, 1], by simp, h.1⟩
      · exact ⟨![1, sμ, 1], by simp, h.2.1⟩
    · rintro ⟨g, hg, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨1, h.1.symm⟩
      · exact ⟨2, h.2.1.symm⟩
      · exact ⟨0, h.2.2.symm⟩
  rw [hgen, hE, ← MonoidHom.map_closure, closure_std_rootsOfUnity q hord,
    Subgroup.map_top]

theorem card_ED4Gen (hF : 4 ≤ Nat.card F) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card F - 1) {s : Fˣ} (hs : orderOf s = q) :
    Nat.card (ED4Gen (F := F) hF s) = q ^ 3 := by
  rw [ED4Gen_eq_ED4Omega hF hq hdvd hs]
  exact card_ED4Omega hF q hq hdvd

theorem isElemAbelian_ED4Gen (hF : 4 ≤ Nat.card F) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card F - 1) {s : Fˣ} (hs : orderOf s = q) :
    IsElemAbelian q (ED4Gen (F := F) hF s) := by
  rw [ED4Gen_eq_ED4Omega hF hq hdvd hs]
  exact isElemAbelian_ED4Omega hF q hdvd

theorem ED4Gen_le_BOmega (hF : 4 ≤ Nat.card F) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card F - 1) {s : Fˣ} (hs : orderOf s = q) :
    ED4Gen (F := F) hF s ≤ OmegaSiegel.BOmega (F := F) hF q := by
  rw [ED4Gen_eq_ED4Omega hF hq hdvd hs]
  exact ED4Omega_le_BOmega hF q

private theorem eTripleOmega_zero_eq (hF : 4 ≤ Nat.card F) (s : Fˣ) :
    eTripleOmega (F := F) hF s 0 = OmegaSiegel.xOmega (F := F) s := by
  rw [eTripleOmega, OmegaSiegel.xOmega_eq_leviOmega_xGL hF]
  exact congrArg (OmegaSiegel.leviOmega (F := F) hF)
    (WitSp.innerDiagA_diagGL_eq (m := 3) (fun _ => s))

theorem xOmega_mem_ED4Gen (hF : 4 ≤ Nat.card F) (s : Fˣ) :
    OmegaSiegel.xOmega (F := F) s ∈ ED4Gen (F := F) hF s := by
  rw [← eTripleOmega_zero_eq hF s]
  exact Subgroup.subset_closure ⟨0, rfl⟩

private theorem eigClass_eGenTriple {s : Fˣ} (hs1 : s ≠ 1) :
    eigClass (eGenTriple s) 2 = ({2, 3} : Finset (Fin 4)) := by
  ext j
  simp only [eigClass, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  fin_cases j
  · constructor
    · intro h
      exact (hs1 (by simpa [eGenTriple] using h 1)).elim
    · intro h
      simp at h
  · constructor
    · intro h
      exact (hs1 (by simpa [eGenTriple] using h 2)).elim
    · intro h
      simp at h
  · constructor
    · intro _
      simp
    · intro _
      intro k
      fin_cases k <;> simp [eGenTriple]
  · constructor
    · intro _
      simp
    · intro _
      intro k
      fin_cases k <;> simp [eGenTriple]

private theorem range_leviOmega_comp_toGL (hF : 4 ≤ Nat.card F) :
    ((OmegaSiegel.leviOmega (F := F) hF).comp Matrix.SpecialLinearGroup.toGL).range =
      OmegaSiegel.JOmega (F := F) hF := by
  rw [MonoidHom.range_comp, OmegaSiegel.JOmega_eq, OmegaSiegel.SLGL]

private theorem eTripleOmega_ggInducedPairs (hF : 4 ≤ Nat.card F) (s : Fˣ) :
    ∀ k, (eTripleOmega (F := F) hF s k, InnerDiagA.diagGL (eGenTriple s k)) ∈
      CFSG.StandardType.LinFusion.ggInducedPairs
        ((OmegaSiegel.leviOmega (F := F) hF).comp Matrix.SpecialLinearGroup.toGL) := by
  intro k u
  change OmegaSiegel.leviOmega (F := F) hF (InnerDiagA.diagGL (eGenTriple s k)) *
      OmegaSiegel.leviOmega (F := F) hF (Matrix.SpecialLinearGroup.toGL u) *
      (OmegaSiegel.leviOmega (F := F) hF (InnerDiagA.diagGL (eGenTriple s k)))⁻¹ =
    OmegaSiegel.leviOmega (F := F) hF (Matrix.SpecialLinearGroup.toGL
      (InnerDiagA.conjSL (InnerDiagA.diagGL (eGenTriple s k)) u))
  rw [← map_mul, ← map_inv, ← map_mul]
  exact congrArg (OmegaSiegel.leviOmega (F := F) hF)
    (WitSp.toGL_conjSL (m := 3) (InnerDiagA.diagGL (eGenTriple s k)) u).symm

private noncomputable def eBlockD4 (hF : 4 ≤ Nat.card F) {s : Fˣ} (hs1 : s ≠ 1) :
    Matrix.SpecialLinearGroup (Fin 2) F ≃*
      (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
        (eigClass (eGenTriple s) 2)).map
        ((OmegaSiegel.leviOmega (F := F) hF).comp Matrix.SpecialLinearGroup.toGL) := by
  rw [eigClass_eGenTriple hs1]
  exact (CFSG.SeitzReduction.LinearPilot.blockSpecialLinearEquivOfCardTwo
      (K := F) (I := ({2, 3} : Finset (Fin 4))) (by decide)).trans
    (Subgroup.equivMapOfInjective _ _
      ((OmegaSiegel.leviOmega_injective hF).comp
        Matrix.SpecialLinearGroup.toGL_injective))

private theorem isQuasisimple_blockD4 (hF : 4 ≤ Nat.card F) {s : Fˣ} (hs1 : s ≠ 1) :
    CFSG.Open.IsQuasisimple ↥((CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
      (eigClass (eGenTriple s) 2)).map
      ((OmegaSiegel.leviOmega (F := F) hF).comp Matrix.SpecialLinearGroup.toGL)) :=
  CFSG.Open.IsQuasisimple.of_mulEquiv (eBlockD4 hF hs1).symm
    (CFSG.ClassicalGroups.Orthogonal.Small.isQuasisimple_specialLinearGroup_two
      (K := F) hF)

private theorem center_blockD4 (hF : 4 ≤ Nat.card F) {s : Fˣ} (hs1 : s ≠ 1) :
    Subgroup.center ↥((CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
      (eigClass (eGenTriple s) 2)).map
      ((OmegaSiegel.leviOmega (F := F) hF).comp Matrix.SpecialLinearGroup.toGL)) = ⊥ := by
  rw [← Subgroup.map_center_eq (eBlockD4 hF hs1),
    CFSG.SeitzReduction.LinearPilot.center_specialLinearGroup_two_eq_bot, Subgroup.map_bot]

private theorem q_dvd_blockD4 (hF : 4 ≤ Nat.card F) {q : ℕ} (hdvd : q ∣ Nat.card F - 1)
    {s : Fˣ} (hs1 : s ≠ 1) :
    q ∣ Nat.card (↥((CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
      (eigClass (eGenTriple s) 2)).map
      ((OmegaSiegel.leviOmega (F := F) hF).comp Matrix.SpecialLinearGroup.toGL)) ⧸
      Subgroup.center ↥((CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
        (eigClass (eGenTriple s) 2)).map
        ((OmegaSiegel.leviOmega (F := F) hF).comp Matrix.SpecialLinearGroup.toGL))) := by
  have hZ := center_blockD4 hF hs1
  have h1 : Nat.card (↥((CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
      (eigClass (eGenTriple s) 2)).map
      ((OmegaSiegel.leviOmega (F := F) hF).comp Matrix.SpecialLinearGroup.toGL)) ⧸
      Subgroup.center ↥((CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
        (eigClass (eGenTriple s) 2)).map
        ((OmegaSiegel.leviOmega (F := F) hF).comp Matrix.SpecialLinearGroup.toGL))) =
      Nat.card ↥((CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
        (eigClass (eGenTriple s) 2)).map
        ((OmegaSiegel.leviOmega (F := F) hF).comp Matrix.SpecialLinearGroup.toGL)) := by
    rw [hZ]
    exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv
  rw [h1]
  have h2 : Nat.card ↥((CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
      (eigClass (eGenTriple s) 2)).map
      ((OmegaSiegel.leviOmega (F := F) hF).comp Matrix.SpecialLinearGroup.toGL)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (Nat.card_congr (eBlockD4 hF hs1).toEquiv).symm
  rw [h2, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hfac : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
    rw [show (1 : ℕ) = 1 ^ 2 by norm_num, Nat.sq_sub_sq]
    ring
  rw [hfac]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hdvd (Nat.card F + 1)) (Nat.card F)

theorem glaPLayer_JOmega_inf_centralizer_ED4Gen_ne_bot (hF : 4 ≤ Nat.card F) {q : ℕ}
    (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1) {s : Fˣ} (hs : orderOf s = q) :
    GLAPLayer q (OmegaSiegel.JOmega (F := F) hF ⊓
      Subgroup.centralizer (ED4Gen (F := F) hF s : Set
        (StatedOmega (StatedQuadPlus 4 F)))) ≠ ⊥ := by
  classical
  have hm2 : Nat.card F ≠ 2 := by omega
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    exact hq.ne_one hs.symm
  set ψ : Matrix.SpecialLinearGroup (Fin 4) F →* StatedOmega (StatedQuadPlus 4 F) :=
    (OmegaSiegel.leviOmega (F := F) hF).comp Matrix.SpecialLinearGroup.toGL with hψ
  set b : Fin 3 → StatedOmega (StatedQuadPlus 4 F) := eTripleOmega (F := F) hF s with hb
  have hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F) := by
    intro x hx
    rw [hψ] at hx
    have hx0 : OmegaSiegel.leviOmega (F := F) hF (Matrix.SpecialLinearGroup.toGL x) = 1 := by
      simpa [MonoidHom.comp_apply] using hx
    have hx1 : x = 1 :=
      ((OmegaSiegel.leviOmega_injective hF).comp
        Matrix.SpecialLinearGroup.toGL_injective) (by simpa using hx0)
    rw [hx1]
    exact Subgroup.one_mem _
  have hb' : ∀ k, (b k, InnerDiagA.diagGL (eGenTriple s k)) ∈
      CFSG.StandardType.LinFusion.ggInducedPairs ψ := by
    intro k
    rw [hψ, hb]
    exact eTripleOmega_ggInducedPairs hF s k
  have h2 : 2 ≤ (eigClass (eGenTriple s) 2).card := by
    rw [eigClass_eGenTriple hs1]
    decide
  have h22 : (eigClass (eGenTriple s) 2).card ≠ 2 ∨ Nat.card F ≠ 2 :=
    Or.inr hm2
  have hcomp := CFSG.StandardType.LinSemisimple.isComponentOf_map_blockSpecialLinear
    (ψ := ψ) hker (d := eGenTriple s) (b := b) hb' 2 h2 h22
  have hH : ψ.range ⊓ Subgroup.centralizer (Set.range b) =
      OmegaSiegel.JOmega (F := F) hF ⊓ Subgroup.centralizer
        (ED4Gen (F := F) hF s : Set (StatedOmega (StatedQuadPlus 4 F))) := by
    rw [hψ, hb, range_leviOmega_comp_toGL, ED4Gen, Subgroup.centralizer_closure]
  have hsn : IsSubnormal ((CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
      (eigClass (eGenTriple s) 2)).map ψ)
      (OmegaSiegel.JOmega (F := F) hF ⊓ Subgroup.centralizer
        (ED4Gen (F := F) hF s : Set (StatedOmega (StatedQuadPlus 4 F)))) := by
    rw [← hH]
    exact CFSG.Assembly.isSubnormal_iff_open.1 hcomp.2.1
  exact glaPLayer_ne_bot_of_isSubnormal_quasisimple hq hsn
    (isQuasisimple_blockD4 hF hs1) (q_dvd_blockD4 hF hdvd hs1)

end DFour

end CFSG.LocalAnalysis.GLTheoremA.Y10F
