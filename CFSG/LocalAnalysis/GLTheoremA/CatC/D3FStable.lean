module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FGraphC
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.HardMathSupport.Lang.Triality.HeightLayers
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.RationalToralSignDiagramTheta
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FLayer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieFrame
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem d3f_commute {G : Type*} [Group G] {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 3 E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  have h := hE.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val h

variable {K : Type} [Field K] [Finite K]


theorem unitN_zero_of_mem_pos {x : ↥(adjointGroup Tag.D4 K)}
    (hx : (x : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K) : x ∈ unitN Tag.D4 K 0 := by
  rw [mem_unitN]
  have : (((0 + 1 : ℕ) : ℤ)) = 1 := by norm_num
  rw [this, heightSeries_one]
  exact hx

theorem chev_card_le_stable [CharP K 3] (α : MulAut ↥(adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hnot : α ∉ Inn ↥(adjointGroup Tag.D4 K))
    (hU : ((posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K)).map α.toMonoidHom =
      (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K))
    (A : Subgroup ↥(adjointGroup Tag.D4 K))
    (hAU : A ≤ (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K))
    (hcomm : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u) (hfix : ∀ a ∈ A, α a = a) :
    Nat.card A ≤ Nat.card K ^ 4 := by
  classical
  obtain ⟨σ, ε, la, hσ3, hε3, hinner, hr⟩ := exists_layerAct_of_stable α hα3 _ rfl hU
  have hA0 : A ≤ unitN Tag.D4 K 0 := fun x hx =>
    unitN_zero_of_mem_pos (Subgroup.mem_subgroupOf.1 (hAU hx))
  by_cases hσ : σ = 1
  · subst hσ
    have hε0 : ε ≠ 0 := fun h => hnot (hinner rfl h)
    have hε : ε = 1 ∨ ε = 2 := by omega
    exact card_le_of_graph la hε hr hα3 hA0 hcomm hfix
  · have h := card_pow_le_of_sigma_ne_one hσ3 hσ la A hA0 hfix
    have h' : Nat.card A ^ 3 ≤ (Nat.card K ^ 4) ^ 3 := by rwa [← pow_mul]
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h'

theorem chev_card_le [CharP K 3] (α : MulAut ↥(adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hnot : α ∉ Inn ↥(adjointGroup Tag.D4 K))
    (A : Subgroup ↥(adjointGroup Tag.D4 K)) (hA : CFSG.Open.IsElemAbelian 3 A)
    (hfix : ∀ a ∈ A, α a = a) : Nat.card A ≤ Nat.card K ^ 4 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  obtain ⟨S, hAS, hSα⟩ := exists_stable_sylow_fixing α hα3 A hA hfix
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨P₀, hP₀⟩ := (exceptional_ordinary_Sylow_opposition Tag.D4 K 3 w₀ hw₀).1
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (adjointGroup Tag.D4 K) P₀ S
  set U₀ : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K) with hU₀
  have hS : (S : Subgroup ↥(adjointGroup Tag.D4 K)) = U₀.map (MulAut.conj x).toMonoidHom := by
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hP₀]
    rfl
  have hmemS : ∀ y, y ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)) ↔ x⁻¹ * y * x ∈ U₀ := by
    intro y
    rw [hS]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hu
    · intro hy
      exact ⟨x⁻¹ * y * x, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hαS : ∀ y ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)), α y ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)) := by
    intro y hy
    have := Subgroup.mem_map_of_mem α.toMonoidHom hy
    rwa [hSα] at this
  set α' : MulAut ↥(adjointGroup Tag.D4 K) := (MulAut.conj x)⁻¹ * α * MulAut.conj x with hα'
  have hα'apply : ∀ y, α' y = x⁻¹ * α (x * y * x⁻¹) * x := by
    intro y
    simp [hα', MulAut.conj_apply, MulAut.conj_inv_apply]
  have hα'3 : α' ^ 3 = 1 := by
    have : α' ^ 3 = (MulAut.conj x)⁻¹ * α ^ 3 * MulAut.conj x := by
      have h := conj_pow (a := (MulAut.conj x)⁻¹) (b := α) (i := 3)
      rwa [inv_inv] at h
    rw [this, hα3]; group
  have hnot' : α' ∉ Inn ↥(adjointGroup Tag.D4 K) := by
    rintro ⟨y, hy⟩
    apply hnot
    refine ⟨x * y * x⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hy, hα']
    group
  have hU' : U₀.map α'.toMonoidHom = U₀ := by
    have hle : U₀.map α'.toMonoidHom ≤ U₀ := by
      rintro _ ⟨u, hu, rfl⟩
      have h1 : x * u * x⁻¹ ∈ (S : Subgroup ↥(adjointGroup Tag.D4 K)) := by
        rw [hmemS]; simpa [mul_assoc] using hu
      have h2 := hαS _ h1
      rw [hmemS] at h2
      change α' u ∈ U₀
      rw [hα'apply]
      exact h2
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective α'.injective]
  set A' : Subgroup ↥(adjointGroup Tag.D4 K) := A.map (MulAut.conj x)⁻¹.toMonoidHom with hA'
  have hA'U : A' ≤ U₀ := by
    rintro _ ⟨a, ha, rfl⟩
    have := (hmemS a).1 (hAS ha)
    change (MulAut.conj x)⁻¹ a ∈ U₀
    rw [MulAut.conj_inv_apply]
    exact this
  have hA'comm : ∀ u ∈ A', ∀ w ∈ A', u * w = w * u := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    change (MulAut.conj x)⁻¹ a * (MulAut.conj x)⁻¹ b = (MulAut.conj x)⁻¹ b * (MulAut.conj x)⁻¹ a
    rw [← map_mul, ← map_mul, d3f_commute hA ha hb]
  have hA'fix : ∀ a ∈ A', α' a = a := by
    rintro _ ⟨a, ha, rfl⟩
    change α' ((MulAut.conj x)⁻¹ a) = (MulAut.conj x)⁻¹ a
    rw [hα'apply, MulAut.conj_inv_apply]
    have : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
    rw [this, hfix a ha]
  have hcard : Nat.card A' = Nat.card A := Subgroup.card_map_of_injective (MulAut.conj x)⁻¹.injective
  rw [← hcard]
  exact chev_card_le_stable α' hα'3 hnot' hU' A' hA'U hA'comm hA'fix

end CFSG.LocalAnalysis.GLTheoremA
