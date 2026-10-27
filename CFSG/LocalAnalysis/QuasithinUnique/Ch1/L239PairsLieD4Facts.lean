module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Rel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
public import CFSG.LieType.Chevalley.GraphFixedParabolicSelfCentralizing
public import CFSG.LieType.Chevalley.GraphFixedParabolicNormalizer
public import CFSG.LieType.Chevalley.GraphFixedSimpleComplement
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsCases
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A3Components
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
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section Tools

variable {G : Type*} [Group G]

theorem comm_sandwich {A y B g : G} (hA : Commute A g) (hB : Commute B g)
    (hAy : Commute A ⁅y, g⁆) : ⁅A * y * B, g⁆ = ⁅y, g⁆ := by
  have e1 : B * g * B⁻¹ = g := by rw [hB.eq, mul_inv_cancel_right]
  have e2 : g * A⁻¹ * g⁻¹ = A⁻¹ := by
    have := (hA.symm.inv_right).eq
    rw [this, mul_inv_cancel_right]
  have e3 : A * ⁅y, g⁆ * A⁻¹ = ⁅y, g⁆ := by rw [hAy.eq, mul_inv_cancel_right]
  have h1 : ⁅A * y * B, g⁆ = A * y * (B * g * B⁻¹) * y⁻¹ * A⁻¹ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  have h2 : A * y * g * y⁻¹ * A⁻¹ * g⁻¹ = A * ⁅y, g⁆ * (g * A⁻¹ * g⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [h1, e1, h2, e2, e3]

theorem commute_of_add {M : Type*} [AddCommGroup M] (x : M → G)
    (hadd : ∀ c d, x (c + d) = x c * x d) (a b : M) : Commute (x a) (x b) := by
  rw [Commute, SemiconjBy, ← hadd, ← hadd, add_comm]

theorem zero_of_add' {M : Type*} [AddCommGroup M] (x : M → G)
    (hadd : ∀ c d, x (c + d) = x c * x d) : x 0 = 1 := by
  simpa using hadd 0 0

theorem comm_mem_of_left {Q R : Subgroup G} {m q : G} (hm : m ∈ R) (hq : q ∈ Q) :
    ⁅m, q⁆ ∈ ⁅Q, R⁆ := by
  rw [← commutatorElement_inv q m]
  exact (⁅Q, R⁆).inv_mem (Subgroup.commutator_mem_commutator hq hm)

theorem mem_of_weight {F : Type*} [Field F] {E : Subgroup G} {x : F → G}
    (hadd : ∀ c d, x (c + d) = x c * x d) {h : G} {w : F} (hw : w ≠ 1)
    (hconj : ∀ s, h * x s * h⁻¹ = x (w * s)) (hE : ∀ s, ⁅h, x s⁆ ∈ E) (c : F) : x c ∈ E := by
  have hw' : w - 1 ≠ 0 := sub_ne_zero.2 hw
  have h1 := hE ((w - 1)⁻¹ * c)
  have h2 : ⁅h, x ((w - 1)⁻¹ * c)⁆ = x (w * ((w - 1)⁻¹ * c) - (w - 1)⁻¹ * c) := by
    have h3 : x (w * ((w - 1)⁻¹ * c) - (w - 1)⁻¹ * c) * x ((w - 1)⁻¹ * c) =
        x (w * ((w - 1)⁻¹ * c)) := by rw [← hadd, sub_add_cancel]
    rw [commutatorElement_def, hconj, ← h3, mul_inv_cancel_right]
  rw [h2] at h1
  have h4 : w * ((w - 1)⁻¹ * c) - (w - 1)⁻¹ * c = c := by
    field_simp
  rwa [h4] at h1

end Tools

@[expose] def fa0 : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩

@[expose] def fa1 : Fin TwistTag.D4.foldedTag.rank := ⟨1, by decide⟩

section RadicalRoots

theorem supp_fa0 : ∀ k : Fin 24, 0 < height (TwistTag.D4.tag.rootCertificate.root k) →
    (∀ j : Fin TwistTag.D4.tag.rank, j ∉ TwistTag.D4.orbit fa0 →
      TwistTag.D4.tag.rootCertificate.root k j = 0) →
    ∃ i ∈ TwistTag.D4.orbit fa0, TwistTag.D4.tag.rootCertificate.root k = Pi.single i 1 := by
  decide +kernel

theorem supp_fa1 : ∀ k : Fin 24, 0 < height (TwistTag.D4.tag.rootCertificate.root k) →
    (∀ j : Fin TwistTag.D4.tag.rank, j ∉ TwistTag.D4.orbit fa1 →
      TwistTag.D4.tag.rootCertificate.root k j = 0) →
    ∃ i ∈ TwistTag.D4.orbit fa1, TwistTag.D4.tag.rootCertificate.root k = Pi.single i 1 := by
  decide +kernel

theorem radicalRoots_eq
    (a : Fin TwistTag.D4.foldedTag.rank)
    (h : ∀ k : Fin 24, 0 < height (TwistTag.D4.tag.rootCertificate.root k) →
      (∀ j : Fin TwistTag.D4.tag.rank, j ∉ TwistTag.D4.orbit a →
        TwistTag.D4.tag.rootCertificate.root k j = 0) →
      ∃ i ∈ TwistTag.D4.orbit a, TwistTag.D4.tag.rootCertificate.root k = Pi.single i 1) :
    parabolicRadicalRoots TwistTag.D4.tag (TwistTag.D4.orbitUnion {a}) =
      simpleComplementRoots TwistTag.D4 a := by
  have hU : ∀ j, j ∈ TwistTag.D4.orbitUnion {a} ↔ j ∈ TwistTag.D4.orbit a := by
    intro j
    rw [TwistTag.mem_orbitUnion]
    simp
  ext α
  constructor
  · rintro ⟨⟨hr, hp⟩, hnot⟩
    refine ⟨⟨hr, hp⟩, ?_⟩
    rintro ⟨i, hi, rfl⟩
    apply hnot
    refine ⟨⟨isRoot_single _ i, fun j hj => ?_⟩, isRoot_single _ i, ?_⟩
    · have hij : j ≠ i := fun hji => hj ((hU j).2 (hji ▸ hi))
      simp [hij]
    · rw [height_single]; exact one_pos
  · rintro ⟨⟨hr, hp⟩, hnot⟩
    refine ⟨⟨hr, hp⟩, ?_⟩
    rintro ⟨⟨-, hsupp⟩, -, -⟩
    obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hr
    obtain ⟨i, hi, hα⟩ := h ⟨k, hk⟩ hp (fun j hj => hsupp j (fun hj' => hj ((hU j).1 hj')))
    exact hnot ⟨i, hi, hα.symm⟩

theorem radical_eq_simpleComplement
    {K : Type} [Field K] (σ : K →+* K)
    (a : Fin TwistTag.D4.foldedTag.rank)
    (h : ∀ k : Fin 24, 0 < height (TwistTag.D4.tag.rootCertificate.root k) →
      (∀ j : Fin TwistTag.D4.tag.rank, j ∉ TwistTag.D4.orbit a →
        TwistTag.D4.tag.rootCertificate.root k j = 0) →
      ∃ i ∈ TwistTag.D4.orbit a, TwistTag.D4.tag.rootCertificate.root k = Pi.single i 1) :
    graphFixedParabolicRadical TwistTag.D4 K σ {a} = graphFixedSimpleComplement TwistTag.D4 K σ a := by
  unfold graphFixedParabolicRadical parabolicRadical graphFixedSimpleComplement
  rw [radicalRoots_eq a h]

theorem orbit_sub_radical
    (a : Fin TwistTag.D4.foldedTag.rank) (j : Fin 6)
    (h : ∀ α ∈ trialityOrbit j, ∃ i : Fin TwistTag.D4.tag.rank,
      i ∉ TwistTag.D4.orbit a ∧ 0 < α i) :
    ((trialityOrbit j : Finset (Fin TwistTag.D4.tag.rank → ℤ)) :
        Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊆
      parabolicRadicalRoots TwistTag.D4.tag (TwistTag.D4.orbitUnion {a}) := by
  intro α hα
  obtain ⟨hr, hp⟩ := trialityOrbit_pos j α hα
  obtain ⟨i, hi, hαi⟩ := h α hα
  refine mem_parabolicRadicalRoots_iff.2 ⟨hr, hp, i, fun hi' => hi ?_, ne_of_gt hαi⟩
  obtain ⟨b, hb, hib⟩ := (TwistTag.mem_orbitUnion TwistTag.D4).1 hi'
  rw [Set.mem_singleton_iff] at hb
  rwa [hb] at hib

theorem orbit_radical_fa0 : ∀ j : Fin 6, j ≠ 0 → ∀ α ∈ trialityOrbit j,
    ∃ i : Fin TwistTag.D4.tag.rank, i ∉ TwistTag.D4.orbit fa0 ∧ 0 < α i := by
  decide +kernel

theorem orbit_radical_fa1 : ∀ j : Fin 6, j ≠ 1 → ∀ α ∈ trialityOrbit j,
    ∃ i : Fin TwistTag.D4.tag.rank, i ∉ TwistTag.D4.orbit fa1 ∧ 0 < α i := by
  decide +kernel

end RadicalRoots

section OrbitX

variable {K : Type} [Field K] (σ : K ≃+* K)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

theorem orbit_card_fa0 : (TwistTag.D4.orbit fa0).card = 3 := by decide

theorem orbit_card_fa1 : (TwistTag.D4.orbit fa1).card = 1 := by decide

theorem orbitMin_fa0 : TwistTag.D4.orbitMin fa0 = ⟨0, by decide⟩ := by decide

theorem orbitMin_fa1 : TwistTag.D4.orbitMin fa1 = ⟨2, by decide⟩ := by decide

theorem orbitX_fa0_eq
    (c : orbitField TwistTag.D4 K τ₀ fa0) :
    (orbitX TwistTag.D4 K τ₀ fa0 c : ModGL TwistTag.D4.tag K) = ox₁ σ (c : K) := by
  rw [coe_orbitX, orbit_card_fa0, ox₁, trialityX₁, coe_trialityOrbitProd, orbitMin_fa0]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  have e0 : (TwistTag.D4.perm ^ 0) (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank) =
      ⟨0, by decide⟩ := by decide
  have e1 : (TwistTag.D4.perm ^ 1) (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank) =
      ⟨1, by decide⟩ := by decide
  have e2 : (TwistTag.D4.perm ^ 2) (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank) =
      ⟨3, by decide⟩ := by decide
  have s0 : (Pi.single (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank) (1 : ℤ) :
      Fin TwistTag.D4.tag.rank → ℤ) = trialityRoot 0 := List.ofFn_injective (by decide +kernel)
  have s1 : (Pi.single (⟨1, by decide⟩ : Fin TwistTag.D4.tag.rank) (1 : ℤ) :
      Fin TwistTag.D4.tag.rank → ℤ) = permLattice TwistTag.D4.perm (trialityRoot 0) :=
    List.ofFn_injective (by decide +kernel)
  have s2 : (Pi.single (⟨3, by decide⟩ : Fin TwistTag.D4.tag.rank) (1 : ℤ) :
      Fin TwistTag.D4.tag.rank → ℤ) = permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 0) :=
    List.ofFn_injective (by decide +kernel)
  rw [e0, e1, e2, ← pinnedX_single, ← pinnedX_single, ← pinnedX_single, s0, s1, s2]
  simp [pow_two]

theorem orbitX_fa1_eq
    (c : orbitField TwistTag.D4 K τ₀ fa1) (b : trialityFixedField K τ₀)
    (hb : (b : K) = c) :
    (orbitX TwistTag.D4 K τ₀ fa1 c : ModGL TwistTag.D4.tag K) = ox₂ σ b := by
  rw [coe_orbitX, orbit_card_fa1, orbitMin_fa1]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  have e0 : (TwistTag.D4.perm ^ 0) (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) =
      ⟨2, by decide⟩ := by decide
  have s0 : (Pi.single (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) (1 : ℤ) :
      Fin TwistTag.D4.tag.rank → ℤ) = trialityRoot 1 := List.ofFn_injective (by decide +kernel)
  rw [e0, ← pinnedX_single, s0]
  simp [ox₂, trialityX₂, hb]

end OrbitX

section Accessors

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom

include hσ3 in
theorem ox₁_add
    (c d : K) : ox₁ σ (c + d) = ox₁ σ c * ox₁ σ d :=
  (congrArg Subtype.val ((ox_data σ hσ3).1.1 c d)).trans (Subgroup.coe_mul _ _ _)

include hσ3 in
theorem ox₂_add
    (c d : trialityFixedField K τ₀) : ox₂ σ (c + d) = ox₂ σ c * ox₂ σ d :=
  (congrArg Subtype.val ((ox_data σ hσ3).1.2.1 c d)).trans (Subgroup.coe_mul _ _ _)

include hσ3 in
theorem ox₃_add
    (c d : K) : ox₃ σ (c + d) = ox₃ σ c * ox₃ σ d :=
  (congrArg Subtype.val ((ox_data σ hσ3).1.2.2.1 c d)).trans (Subgroup.coe_mul _ _ _)

include hσ3 in
theorem ox₄_add
    (c d : K) : ox₄ σ (c + d) = ox₄ σ c * ox₄ σ d :=
  (congrArg Subtype.val ((ox_data σ hσ3).1.2.2.2.1 c d)).trans (Subgroup.coe_mul _ _ _)

include hσ3 in
theorem ox₅_add
    (c d : trialityFixedField K τ₀) : ox₅ σ (c + d) = ox₅ σ c * ox₅ σ d :=
  (congrArg Subtype.val ((ox_data σ hσ3).1.2.2.2.2.1 c d)).trans (Subgroup.coe_mul _ _ _)

include hσ3 in
theorem ox₆_add
    (c d : trialityFixedField K τ₀) : ox₆ σ (c + d) = ox₆ σ c * ox₆ σ d :=
  (congrArg Subtype.val ((ox_data σ hσ3).1.2.2.2.2.2 c d)).trans (Subgroup.coe_mul _ _ _)

include hσ3 in
theorem ox₁_zero
    : ox₁ σ 0 = 1 := zero_of_add' (ox₁ σ) (ox₁_add σ hσ3)

include hσ3 in
theorem ox₂_zero
    : ox₂ σ 0 = 1 := zero_of_add' (ox₂ σ) (ox₂_add σ hσ3)

include hσ3 in
theorem ox₃_zero
    : ox₃ σ 0 = 1 := zero_of_add' (ox₃ σ) (ox₃_add σ hσ3)

include hσ3 in
theorem ox₄_zero
    : ox₄ σ 0 = 1 := zero_of_add' (ox₄ σ) (ox₄_add σ hσ3)

include hσ3 in
theorem ox₅_zero
    : ox₅ σ 0 = 1 := zero_of_add' (ox₅ σ) (ox₅_add σ hσ3)

include hσ3 in
theorem ox₆_zero
    : ox₆ σ 0 = 1 := zero_of_add' (ox₆ σ) (ox₆_add σ hσ3)

include hσ3 in
theorem ox₁_inj
    {c d : K} (h : ox₁ σ c = ox₁ σ d) : c = d :=
  (ox_data σ hσ3).2.2.1 (Subtype.ext h)

include hσ3 in
theorem ox₂_inj
    {c d : trialityFixedField K τ₀} (h : ox₂ σ c = ox₂ σ d) : c = d :=
  (ox_data σ hσ3).2.2.2.1 (Subtype.ext h)

include hσ3 in
theorem ox₅_inj
    {c d : trialityFixedField K τ₀} (h : ox₅ σ c = ox₅ σ d) : c = d :=
  (ox_data σ hσ3).2.2.2.2.2.2.1 (Subtype.ext h)

include hσ3 in
theorem ox₆_inj
    {c d : trialityFixedField K τ₀} (h : ox₆ σ c = ox₆ σ d) : c = d :=
  (ox_data σ hσ3).2.2.2.2.2.2.2 (Subtype.ext h)

end Accessors

noncomputable abbrev Q0
    {K : Type} [Field K] (σ : K ≃+* K) :
    Subgroup (ModGL TwistTag.D4.tag K) :=
  graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {fa0}

noncomputable abbrev Q1
    {K : Type} [Field K] (σ : K ≃+* K) :
    Subgroup (ModGL TwistTag.D4.tag K) :=
  graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {fa1}

noncomputable abbrev P0
    {K : Type} [Field K] (σ : K ≃+* K) :
    Subgroup (ModGL TwistTag.D4.tag K) :=
  graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa0}

noncomputable abbrev P1
    {K : Type} [Field K] (σ : K ≃+* K) :
    Subgroup (ModGL TwistTag.D4.tag K) :=
  graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa1}

section Normal

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

omit [Finite K] [CharP K 2] in
theorem mem_radical_of_orbit
    {σ' : K →+* K} {a : Fin TwistTag.D4.foldedTag.rank} {j : Fin 6}
    {g : GL}
    (hsub : ((trialityOrbit j : Finset (Fin TwistTag.D4.tag.rank → ℤ)) :
        Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊆
      parabolicRadicalRoots TwistTag.D4.tag (TwistTag.D4.orbitUnion {a}))
    (hg : g ∈ rootSpan TwistTag.D4.tag K
      ((trialityOrbit j : Finset (Fin TwistTag.D4.tag.rank → ℤ)) :
        Set (Fin TwistTag.D4.tag.rank → ℤ)))
    (hΓ : g ∈ twistedFixedGroup TwistTag.D4 K σ') :
    g ∈ graphFixedParabolicRadical TwistTag.D4 K σ' {a} :=
  Subgroup.mem_inf.2 ⟨rootSpan_mono hsub hg, hΓ⟩

include hσ3 in
theorem ox₂_mem_Q0
    (c : trialityFixedField K τ₀) : ox₂ σ c ∈ Q0 σ :=
  mem_radical_of_orbit (j := 1) (orbit_sub_radical fa0 1 (orbit_radical_fa0 1 (by decide)))
    (pinnedX_mem_rootSpan_trialityOrbit 1 (c : K))
    (graphFixedPosUnipotent_le TwistTag.D4 K τ₀ ((ox_data σ hσ3).2.1.2.1 c))

include hσ3 in
theorem ox₃_mem_Q0
    (c : K) : ox₃ σ c ∈ Q0 σ :=
  mem_radical_of_orbit (j := 2) (orbit_sub_radical fa0 2 (orbit_radical_fa0 2 (by decide)))
    (trialityOrbitProd_mem_rootSpan (α := trialityRoot 2) τ₀ c)
    (graphFixedPosUnipotent_le TwistTag.D4 K τ₀ ((ox_data σ hσ3).2.1.2.2.1 c))

include hσ3 in
theorem ox₄_mem_Q0
    (c : K) : ox₄ σ c ∈ Q0 σ :=
  mem_radical_of_orbit (j := 3) (orbit_sub_radical fa0 3 (orbit_radical_fa0 3 (by decide)))
    (trialityOrbitProd_mem_rootSpan (α := trialityRoot 3) τ₀ c)
    (graphFixedPosUnipotent_le TwistTag.D4 K τ₀ ((ox_data σ hσ3).2.1.2.2.2.1 c))

include hσ3 in
theorem ox₅_mem_Q0
    (c : trialityFixedField K τ₀) : ox₅ σ c ∈ Q0 σ :=
  mem_radical_of_orbit (j := 4) (orbit_sub_radical fa0 4 (orbit_radical_fa0 4 (by decide)))
    (pinnedX_mem_rootSpan_trialityOrbit 4 (c : K))
    (graphFixedPosUnipotent_le TwistTag.D4 K τ₀ ((ox_data σ hσ3).2.1.2.2.2.2.1 c))

include hσ3 in
theorem ox₆_mem_Q0
    (c : trialityFixedField K τ₀) : ox₆ σ c ∈ Q0 σ :=
  mem_radical_of_orbit (j := 5) (orbit_sub_radical fa0 5 (orbit_radical_fa0 5 (by decide)))
    (pinnedX_mem_rootSpan_trialityOrbit 5 (c : K))
    (graphFixedPosUnipotent_le TwistTag.D4 K τ₀ ((ox_data σ hσ3).2.1.2.2.2.2.2 c))

include hσ3 in
theorem ox₁_mem_Q1
    (c : K) : ox₁ σ c ∈ Q1 σ :=
  mem_radical_of_orbit (j := 0) (orbit_sub_radical fa1 0 (orbit_radical_fa1 0 (by decide)))
    (trialityOrbitProd_mem_rootSpan (α := trialityRoot 0) τ₀ c)
    (graphFixedPosUnipotent_le TwistTag.D4 K τ₀ ((ox_data σ hσ3).2.1.1 c))

include hσ3 in
theorem ox₃_mem_Q1
    (c : K) : ox₃ σ c ∈ Q1 σ :=
  mem_radical_of_orbit (j := 2) (orbit_sub_radical fa1 2 (orbit_radical_fa1 2 (by decide)))
    (trialityOrbitProd_mem_rootSpan (α := trialityRoot 2) τ₀ c)
    (graphFixedPosUnipotent_le TwistTag.D4 K τ₀ ((ox_data σ hσ3).2.1.2.2.1 c))

include hσ3 in
theorem ox₄_mem_Q1
    (c : K) : ox₄ σ c ∈ Q1 σ :=
  mem_radical_of_orbit (j := 3) (orbit_sub_radical fa1 3 (orbit_radical_fa1 3 (by decide)))
    (trialityOrbitProd_mem_rootSpan (α := trialityRoot 3) τ₀ c)
    (graphFixedPosUnipotent_le TwistTag.D4 K τ₀ ((ox_data σ hσ3).2.1.2.2.2.1 c))

include hσ3 in
theorem ox₅_mem_Q1
    (c : trialityFixedField K τ₀) : ox₅ σ c ∈ Q1 σ :=
  mem_radical_of_orbit (j := 4) (orbit_sub_radical fa1 4 (orbit_radical_fa1 4 (by decide)))
    (pinnedX_mem_rootSpan_trialityOrbit 4 (c : K))
    (graphFixedPosUnipotent_le TwistTag.D4 K τ₀ ((ox_data σ hσ3).2.1.2.2.2.2.1 c))

include hσ3 in
theorem ox₆_mem_Q1
    (c : trialityFixedField K τ₀) : ox₆ σ c ∈ Q1 σ :=
  mem_radical_of_orbit (j := 5) (orbit_sub_radical fa1 5 (orbit_radical_fa1 5 (by decide)))
    (pinnedX_mem_rootSpan_trialityOrbit 5 (c : K))
    (graphFixedPosUnipotent_le TwistTag.D4 K τ₀ ((ox_data σ hσ3).2.1.2.2.2.2.2 c))

include hσ3 in
theorem mem_radical_a0_iff
    {g : GL} :
    g ∈ Q0 σ ↔ ∃ (b : trialityFixedField K τ₀) (c d : K) (e f : trialityFixedField K τ₀),
      g = ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f := by
  constructor
  · intro hg
    have hgU : g ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ :=
      graphFixedParabolicRadical_le_graphFixedPosUnipotent {fa0} hg
    obtain ⟨a, b, c, d, e, f, hgeq⟩ := coord_exists σ hσ3 hgU
    have hrQ : ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f ∈ Q0 σ :=
      mul_mem (mul_mem (mul_mem (mul_mem (ox₂_mem_Q0 σ hσ3 b) (ox₃_mem_Q0 σ hσ3 c))
        (ox₄_mem_Q0 σ hσ3 d)) (ox₅_mem_Q0 σ hσ3 e)) (ox₆_mem_Q0 σ hσ3 f)
    have h1 : ox₁ σ a = g * (ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f)⁻¹ := by
      rw [hgeq]; group
    have h1Q : ox₁ σ a ∈ Q0 σ := by rw [h1]; exact mul_mem hg (inv_mem hrQ)
    have haF : a ∈ orbitField TwistTag.D4 K τ₀ fa0 :=
      mem_orbitField.2 (by rw [orbit_card_fa0, hσ3]; rfl)
    have hX : (orbitX TwistTag.D4 K τ₀ fa0 ⟨a, haF⟩ : GL) = ox₁ σ a :=
      orbitX_fa0_eq σ ⟨a, haF⟩
    have hV : (orbitX TwistTag.D4 K τ₀ fa0 ⟨a, haF⟩ : GL) ∈
        graphFixedSimpleComplement TwistTag.D4 K τ₀ fa0 := by
      rw [hX, ← radical_eq_simpleComplement τ₀ fa0 supp_fa0]
      exact h1Q
    have h2 := eq_one_of_mem_graphFixedSimpleComplement hV
    rw [hX] at h2
    have ha0 : a = 0 := ox₁_inj σ hσ3 (h2.trans (ox₁_zero σ hσ3).symm)
    refine ⟨b, c, d, e, f, ?_⟩
    rw [hgeq, ha0, ox₁_zero σ hσ3, one_mul]
  · rintro ⟨b, c, d, e, f, rfl⟩
    exact mul_mem (mul_mem (mul_mem (mul_mem (ox₂_mem_Q0 σ hσ3 b) (ox₃_mem_Q0 σ hσ3 c))
      (ox₄_mem_Q0 σ hσ3 d)) (ox₅_mem_Q0 σ hσ3 e)) (ox₆_mem_Q0 σ hσ3 f)

include hσ3 in
theorem mem_radical_a1_iff
    {g : GL} :
    g ∈ Q1 σ ↔ ∃ (a c d : K) (e f : trialityFixedField K τ₀),
      g = ox₁ σ a * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f := by
  constructor
  · intro hg
    have hgU : g ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ :=
      graphFixedParabolicRadical_le_graphFixedPosUnipotent {fa1} hg
    obtain ⟨a, b, c, d, e, f, hgeq⟩ := coord_exists σ hσ3 hgU
    have hrQ : ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f ∈ Q1 σ :=
      mul_mem (mul_mem (mul_mem (ox₃_mem_Q1 σ hσ3 c) (ox₄_mem_Q1 σ hσ3 d))
        (ox₅_mem_Q1 σ hσ3 e)) (ox₆_mem_Q1 σ hσ3 f)
    have h1 : ox₂ σ b = (ox₁ σ a)⁻¹ * g * (ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f)⁻¹ := by
      rw [hgeq]; group
    have h1Q : ox₂ σ b ∈ Q1 σ := by
      rw [h1]
      exact mul_mem (mul_mem (inv_mem (ox₁_mem_Q1 σ hσ3 a)) hg) (inv_mem hrQ)
    have hbF : (b : K) ∈ orbitField TwistTag.D4 K τ₀ fa1 :=
      mem_orbitField.2 (by rw [orbit_card_fa1, pow_one]; exact b.2)
    have hX : (orbitX TwistTag.D4 K τ₀ fa1 ⟨(b : K), hbF⟩ : GL) = ox₂ σ b :=
      orbitX_fa1_eq σ ⟨(b : K), hbF⟩ b rfl
    have hV : (orbitX TwistTag.D4 K τ₀ fa1 ⟨(b : K), hbF⟩ : GL) ∈
        graphFixedSimpleComplement TwistTag.D4 K τ₀ fa1 := by
      rw [hX, ← radical_eq_simpleComplement τ₀ fa1 supp_fa1]
      exact h1Q
    have h2 := eq_one_of_mem_graphFixedSimpleComplement hV
    rw [hX] at h2
    have hb0 : b = 0 := ox₂_inj σ hσ3 (h2.trans (ox₂_zero σ hσ3).symm)
    refine ⟨a, c, d, e, f, ?_⟩
    rw [hgeq, hb0, ox₂_zero σ hσ3, mul_one]
  · rintro ⟨a, c, d, e, f, rfl⟩
    exact mul_mem (mul_mem (mul_mem (mul_mem (ox₁_mem_Q1 σ hσ3 a) (ox₃_mem_Q1 σ hσ3 c))
      (ox₄_mem_Q1 σ hσ3 d)) (ox₅_mem_Q1 σ hσ3 e)) (ox₆_mem_Q1 σ hσ3 f)

end Normal

section Center

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

omit [Finite K] in
include hσ3 in
theorem trace_one : trialityTrace K τ₀ hσ3 1 = 1 := trace_fixed σ hσ3 1

include hσ3 in
theorem five_six_eq_one
    {e f : trialityFixedField K τ₀} (h : ox₅ σ e * ox₆ σ f = 1) :
    e = 0 ∧ f = 0 := by
  have := coord_unique σ hσ3 (a := 0) (a' := 0) (b := 0) (b' := 0) (c := 0) (c' := 0)
    (d := 0) (d' := 0) (e := e) (e' := 0) (f := f) (f' := 0) (by
      rw [ox₁_zero σ hσ3, ox₂_zero σ hσ3, ox₃_zero σ hσ3, ox₄_zero σ hσ3, ox₅_zero σ hσ3,
        ox₆_zero σ hσ3]
      simpa using h)
  exact ⟨this.2.2.2.2.1, this.2.2.2.2.2⟩

include hσ3 in
theorem nonabelian_a0
    : ∃ x ∈ Q0 σ, ∃ y ∈ Q0 σ, x * y ≠ y * x := by
  refine ⟨ox₂ σ 1, ox₂_mem_Q0 σ hσ3 1, ox₅ σ 1, ox₅_mem_Q0 σ hσ3 1, fun h => ?_⟩
  have h1 : ⁅ox₂ σ 1, ox₅ σ 1⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h
  rw [rel25 σ hσ3] at h1
  have := ox₆_inj σ hσ3 (h1.trans (ox₆_zero σ hσ3).symm)
  rw [mul_one] at this
  exact one_ne_zero this

include hσ3 in
theorem nonabelian_a1
    : ∃ x ∈ Q1 σ, ∃ y ∈ Q1 σ, x * y ≠ y * x := by
  refine ⟨ox₁ σ 1, ox₁_mem_Q1 σ hσ3 1, ox₄ σ 1, ox₄_mem_Q1 σ hσ3 1, fun h => ?_⟩
  have h1 : ⁅ox₁ σ 1, ox₄ σ 1⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h
  rw [rel14 σ hσ3, mul_one, trace_one σ hσ3] at h1
  have := ox₅_inj σ hσ3 (h1.trans (ox₅_zero σ hσ3).symm)
  exact one_ne_zero this

include hσ3 in
theorem center_le_a0
    : Q0 σ ⊓ Subgroup.centralizer (Q0 σ : Set GL) ≤ ⁅Q0 σ, Q0 σ⁆ := by
  rintro z ⟨hzQ, hzC⟩
  obtain ⟨b, c, d, e, f, rfl⟩ := (mem_radical_a0_iff σ hσ3).1 hzQ
  have hcent : ∀ g ∈ Q0 σ,
      ⁅ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f, g⁆ = 1 := fun g hg =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have hb : b = 0 := by
    have h1 := hcent _ (ox₅_mem_Q0 σ hσ3 (1 : trialityFixedField K τ₀))
    have e1 : ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        1 * ox₂ σ b * (ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f) := by group
    have hB : Commute (ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f) (ox₅ σ 1) :=
      (((comm35 σ hσ3 c 1).mul_left (comm45 σ hσ3 d 1)).mul_left
        (commute_of_add (ox₅ σ) (ox₅_add σ hσ3) e 1)).mul_left (comm56 σ hσ3 1 f).symm
    rw [e1, comm_sandwich (Commute.one_left _) hB (Commute.one_left _), rel25 σ hσ3] at h1
    have := ox₆_inj σ hσ3 (h1.trans (ox₆_zero σ hσ3).symm)
    exact (mul_one b).symm.trans this
  subst hb
  have hc : c = 0 := by
    apply trace_nondeg σ hσ3
    intro t
    have h1 := hcent _ (ox₄_mem_Q0 σ hσ3 t)
    have e1 : ox₂ σ 0 * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        ox₂ σ 0 * ox₃ σ c * (ox₄ σ d * ox₅ σ e * ox₆ σ f) := by group
    have hA : Commute (ox₂ σ 0) (ox₄ σ t) := comm24 σ hσ3 0 t
    have hB : Commute (ox₄ σ d * ox₅ σ e * ox₆ σ f) (ox₄ σ t) :=
      ((commute_of_add (ox₄ σ) (ox₄_add σ hσ3) d t).mul_left (comm45 σ hσ3 t e).symm).mul_left
        (comm46 σ hσ3 t f).symm
    have hAy : Commute (ox₂ σ 0) ⁅ox₃ σ c, ox₄ σ t⁆ := by
      rw [rel34 σ hσ3]; exact comm26 σ hσ3 0 _
    rw [e1, comm_sandwich hA hB hAy, rel34 σ hσ3] at h1
    exact ox₆_inj σ hσ3 (h1.trans (ox₆_zero σ hσ3).symm)
  subst hc
  have hd : d = 0 := by
    apply trace_nondeg' σ hσ3
    intro s
    have h1 := hcent _ (ox₃_mem_Q0 σ hσ3 s)
    have e1 : ox₂ σ 0 * ox₃ σ 0 * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        (ox₂ σ 0 * ox₃ σ 0) * ox₄ σ d * (ox₅ σ e * ox₆ σ f) := by group
    have hA : Commute (ox₂ σ 0 * ox₃ σ 0) (ox₃ σ s) :=
      (comm23 σ hσ3 0 s).mul_left (commute_of_add (ox₃ σ) (ox₃_add σ hσ3) 0 s)
    have hB : Commute (ox₅ σ e * ox₆ σ f) (ox₃ σ s) :=
      (comm35 σ hσ3 s e).symm.mul_left (comm36 σ hσ3 s f).symm
    have hinv : ⁅ox₄ σ d, ox₃ σ s⁆ = (ox₆ σ (trialityTrace K τ₀ hσ3 (s * d)))⁻¹ := by
      rw [← commutatorElement_inv, rel34 σ hσ3]
    have hAy : Commute (ox₂ σ 0 * ox₃ σ 0) ⁅ox₄ σ d, ox₃ σ s⁆ := by
      rw [hinv]
      exact ((comm26 σ hσ3 0 _).mul_left (comm36 σ hσ3 0 _)).inv_right
    rw [e1, comm_sandwich hA hB hAy, hinv] at h1
    have h2 : ox₆ σ (trialityTrace K τ₀ hσ3 (s * d)) = 1 := inv_eq_one.1 h1
    exact ox₆_inj σ hσ3 (h2.trans (ox₆_zero σ hσ3).symm)
  subst hd
  have he : e = 0 := by
    have h1 := hcent _ (ox₂_mem_Q0 σ hσ3 (1 : trialityFixedField K τ₀))
    have e1 : ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0 * ox₅ σ e * ox₆ σ f =
        (ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0) * ox₅ σ e * ox₆ σ f := by group
    have hA : Commute (ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0) (ox₂ σ 1) :=
      (((commute_of_add (ox₂ σ) (ox₂_add σ hσ3) 0 1).mul_left (comm23 σ hσ3 1 0).symm).mul_left
        (comm24 σ hσ3 1 0).symm)
    have hB : Commute (ox₆ σ f) (ox₂ σ 1) := (comm26 σ hσ3 1 f).symm
    have hinv : ⁅ox₅ σ e, ox₂ σ 1⁆ = (ox₆ σ (1 * e))⁻¹ := by
      rw [← commutatorElement_inv, rel25 σ hσ3]
    have hAy : Commute (ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0) ⁅ox₅ σ e, ox₂ σ 1⁆ := by
      rw [hinv]
      exact (((comm26 σ hσ3 0 _).mul_left (comm36 σ hσ3 0 _)).mul_left
        (comm46 σ hσ3 0 _)).inv_right
    rw [e1, comm_sandwich hA hB hAy, hinv] at h1
    have h2 : ox₆ σ (1 * e) = 1 := inv_eq_one.1 h1
    have := ox₆_inj σ hσ3 (h2.trans (ox₆_zero σ hσ3).symm)
    exact (one_mul e).symm.trans this
  subst he
  have : ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0 * ox₅ σ 0 * ox₆ σ f = ⁅ox₂ σ 1, ox₅ σ f⁆ := by
    rw [rel25 σ hσ3, one_mul, ox₂_zero σ hσ3, ox₃_zero σ hσ3, ox₄_zero σ hσ3, ox₅_zero σ hσ3]
    simp
  rw [this]
  exact Subgroup.commutator_mem_commutator (ox₂_mem_Q0 σ hσ3 1) (ox₅_mem_Q0 σ hσ3 f)

include hσ3 in
theorem center_le_a1
    : Q1 σ ⊓ Subgroup.centralizer (Q1 σ : Set GL) ≤ ⁅Q1 σ, Q1 σ⁆ := by
  rintro z ⟨hzQ, hzC⟩
  obtain ⟨a, c, d, e, f, rfl⟩ := (mem_radical_a1_iff σ hσ3).1 hzQ
  have hcent : ∀ g ∈ Q1 σ,
      ⁅ox₁ σ a * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f, g⁆ = 1 := fun g hg =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have hac : ∀ t : K, trialityTrace K τ₀ hσ3 (a * t) = 0 ∧ trialityTrace K τ₀ hσ3 (c * t) = 0 := by
    intro t
    have h1 := hcent _ (ox₄_mem_Q1 σ hσ3 t)
    have e1 : ox₁ σ a * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        1 * (ox₁ σ a * ox₃ σ c) * (ox₄ σ d * ox₅ σ e * ox₆ σ f) := by group
    have hB : Commute (ox₄ σ d * ox₅ σ e * ox₆ σ f) (ox₄ σ t) :=
      ((commute_of_add (ox₄ σ) (ox₄_add σ hσ3) d t).mul_left (comm45 σ hσ3 t e).symm).mul_left
        (comm46 σ hσ3 t f).symm
    rw [e1, comm_sandwich (Commute.one_left _) hB (Commute.one_left _)] at h1
    have e2 : ⁅ox₁ σ a * ox₃ σ c, ox₄ σ t⁆ =
        ox₁ σ a * ⁅ox₃ σ c, ox₄ σ t⁆ * (ox₁ σ a)⁻¹ * ⁅ox₁ σ a, ox₄ σ t⁆ := by
      simp only [commutatorElement_def]; group
    rw [e2, rel34 σ hσ3, rel14 σ hσ3, (comm16 σ hσ3 a _).eq, mul_inv_cancel_right] at h1
    have h2 : ox₅ σ (trialityTrace K τ₀ hσ3 (a * t)) * ox₆ σ (trialityTrace K τ₀ hσ3 (c * t)) =
        1 := by
      rw [(comm56 σ hσ3 _ _).eq]; exact h1
    obtain ⟨h5, h6⟩ := five_six_eq_one σ hσ3 h2
    exact ⟨h5, h6⟩
  have ha : a = 0 := trace_nondeg σ hσ3 a (fun t => (hac t).1)
  have hc : c = 0 := trace_nondeg σ hσ3 c (fun t => (hac t).2)
  subst ha
  subst hc
  have hd : d = 0 := by
    apply trace_nondeg' σ hσ3
    intro s
    have h1 := hcent _ (ox₁_mem_Q1 σ hσ3 s)
    have e1 : ox₁ σ 0 * ox₃ σ 0 * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        1 * ox₄ σ d * (ox₅ σ e * ox₆ σ f) := by
      rw [ox₁_zero σ hσ3, ox₃_zero σ hσ3]; group
    have hB : Commute (ox₅ σ e * ox₆ σ f) (ox₁ σ s) :=
      (comm15 σ hσ3 s e).symm.mul_left (comm16 σ hσ3 s f).symm
    have hinv : ⁅ox₄ σ d, ox₁ σ s⁆ = (ox₅ σ (trialityTrace K τ₀ hσ3 (s * d)))⁻¹ := by
      rw [← commutatorElement_inv, rel14 σ hσ3]
    rw [e1, comm_sandwich (Commute.one_left _) hB (Commute.one_left _), hinv] at h1
    exact ox₅_inj σ hσ3 ((inv_eq_one.1 h1).trans (ox₅_zero σ hσ3).symm)
  subst hd
  have h5 : ox₅ σ e = ⁅ox₁ σ 1, ox₄ σ (e : K)⁆ := by
    rw [rel14 σ hσ3, one_mul, trace_fixed σ hσ3]
  have h6 : ox₆ σ f = ⁅ox₃ σ 1, ox₄ σ (f : K)⁆ := by
    rw [rel34 σ hσ3, one_mul, trace_fixed σ hσ3]
  have hz : ox₁ σ 0 * ox₃ σ 0 * ox₄ σ 0 * ox₅ σ e * ox₆ σ f =
      ⁅ox₁ σ 1, ox₄ σ (e : K)⁆ * ⁅ox₃ σ 1, ox₄ σ (f : K)⁆ := by
    rw [← h5, ← h6, ox₁_zero σ hσ3, ox₃_zero σ hσ3, ox₄_zero σ hσ3]
    simp
  rw [hz]
  exact mul_mem (Subgroup.commutator_mem_commutator (ox₁_mem_Q1 σ hσ3 1) (ox₄_mem_Q1 σ hσ3 _))
    (Subgroup.commutator_mem_commutator (ox₃_mem_Q1 σ hσ3 1) (ox₄_mem_Q1 σ hσ3 _))

end Center

section Levi

open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

theorem levi_package
    (a : Fin TwistTag.D4.foldedTag.rank)
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K τ₀))
    (hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K τ₀ a), s.card = 4) :
    ∃ R : SL2 ↥(orbitField TwistTag.D4 K τ₀ a) →* GL,
      (∀ c, R (uSL c) = orbitX TwistTag.D4 K τ₀ a c) ∧
      (∀ u, R (HSL u) = orbitH TwistTag.D4 K τ₀ a u) ∧
      R WSL = canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∧
      R.range ≤ CFSG.Quasithin.perfectCore (graphFixedParabolic TwistTag.D4 K τ₀ {a}) ∧
      IsSimpleGroup ↥R.range ∧
      ∃ g : ↥(CFSG.Quasithin.perfectCore (graphFixedParabolic TwistTag.D4 K τ₀ {a})) →*
          ↥R.range, Function.Surjective g ∧
        ∀ x, g x = 1 → (x : GL) ∈ graphFixedSimpleComplement TwistTag.D4 K τ₀ a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite GL := finite_modGL
  obtain ⟨R, hRx, hRy, hRH, hRW, hRn, hrange, -, hker, -⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.D4 K τ₀ a
  obtain ⟨hVU, hVnormal, hmul, -, -, -, -, hnV, -, himage⟩ :=
    fixed_simple_positive_complement TwistTag.D4 K σ a
  have hUnormV : graphFixedPosUnipotent TwistTag.D4 K τ₀ ≤
      Subgroup.normalizer (graphFixedSimpleComplement TwistTag.D4 K τ₀ a : Set GL) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVU).mp hVnormal
  have hX : ∀ c, (orbitX TwistTag.D4 K τ₀ a c : GL) ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ :=
    fun c => orbitX_mem_graphFixedPosUnipotent TwistTag.D4 τ₀ a c
  have hUN := graphFixedPosUnipotent_le_fixedPosWeylGroup (t := TwistTag.D4) (K := K) (σ := τ₀) a
  have hRN : R.range ≤ fixedPosWeylGroup TwistTag.D4 K τ₀ a := by
    rw [hrange]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hUN (hX c)
    · exact orbitY_mem_fixedPosWeylGroup a c
  have hRnorm : R.range ≤
      Subgroup.normalizer (graphFixedSimpleComplement TwistTag.D4 K τ₀ a : Set GL) := by
    rw [hrange]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hUnormV (hX c)
    · have hy : (orbitY TwistTag.D4 K τ₀ a c : GL) ∈
          (fun g => canonicalRep (coxeterSystem TwistTag.D4.tag) K
              (TwistTag.D4.orbitReflection a) * g *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a))⁻¹) ''
            Set.range (fun c : orbitField TwistTag.D4 K τ₀ a =>
              (orbitX TwistTag.D4 K τ₀ a c : GL)) := by
        rw [himage]
        exact ⟨c, rfl⟩
      obtain ⟨_, ⟨c', rfl⟩, hyc⟩ := hy
      show (orbitY TwistTag.D4 K τ₀ a c : GL) ∈
        Subgroup.normalizer (graphFixedSimpleComplement TwistTag.D4 K τ₀ a : Set GL)
      rw [← hyc]
      exact mul_mem (mul_mem hnV (hUnormV (hX c'))) (inv_mem hnV)
  have hNnorm : fixedPosWeylGroup TwistTag.D4 K τ₀ a ≤
      Subgroup.normalizer (graphFixedSimpleComplement TwistTag.D4 K τ₀ a : Set GL) :=
    sup_le hUnormV ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hnV))
  have hsup : graphFixedSimpleComplement TwistTag.D4 K τ₀ a ⊔ R.range =
      fixedPosWeylGroup TwistTag.D4 K τ₀ a := by
    refine le_antisymm (sup_le (hVU.trans hUN) hRN) ?_
    refine sup_le (fun u hu => ?_) ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 ?_))
    · have hu' : u ∈ (graphFixedPosUnipotent TwistTag.D4 K τ₀ : Set GL) := hu
      rw [hmul] at hu'
      obtain ⟨v, hv, _, ⟨c, rfl⟩, rfl⟩ := hu'
      exact mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right ⟨uSL c, hRx c⟩)
    · exact Subgroup.mem_sup_right ⟨WSL, by rw [hRW, hRn]⟩
  have hRinj : Function.Injective R := fixed_rankOne_injective σ a hker
  have hsimpleSL : IsSimpleGroup (SL2 ↥(orbitField TwistTag.D4 K τ₀ a)) := sl2_isSimple hL4
  have hperfSL : Group.IsPerfect (SL2 ↥(orbitField TwistTag.D4 K τ₀ a)) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect hL4
  have hsimpleM : IsSimpleGroup ↥R.range :=
    (MonoidHom.ofInjective hRinj).symm.isSimpleGroup
  have hMperf : ⁅R.range, R.range⁆ = R.range := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range R)
  have hV2 : IsPGroup 2 ↥(graphFixedSimpleComplement TwistTag.D4 K τ₀ a) :=
    IsPGroup.of_injective hU (Subgroup.inclusion hVU) (Subgroup.inclusion_injective hVU)
  have hVM : graphFixedSimpleComplement TwistTag.D4 K τ₀ a ⊓ R.range = ⊥ :=
    inf_eq_bot_of_simple hRnorm hV2 hMperf
  have hMP : R.range ≤ graphFixedParabolic TwistTag.D4 K τ₀ {a} :=
    hRN.trans (fixedPosWeylGroup_le_graphFixedParabolic_singleton σ.surjective a)
  obtain ⟨g, hg, hk⟩ := exists_levi_hom (hVU.trans hUN) hNnorm hVM hsup le_rfl hMperf
    (CFSG.Quasithin.perfectCore_le _)
  have hpc : CFSG.Quasithin.perfectCore (graphFixedParabolic TwistTag.D4 K τ₀ {a}) =
      CFSG.Quasithin.perfectCore (fixedPosWeylGroup TwistTag.D4 K τ₀ a) :=
    fixed_perfectCore_eq σ a
  refine ⟨R, hRx, hRH, ?_, ?_, hsimpleM, ?_⟩
  · rw [hRW, hRn]
  · exact CFSG.Quasithin.le_perfectCore_of_perfect hMP hMperf
  · refine ⟨g.comp (MulEquiv.subgroupCongr hpc).toMonoidHom,
      hg.comp (MulEquiv.subgroupCongr hpc).surjective, ?_⟩
    intro x hx
    have h1 : g (MulEquiv.subgroupCongr hpc x) = 1 := hx
    have h2 := hk (MulEquiv.subgroupCongr hpc x) h1
    rwa [MulEquiv.subgroupCongr_apply] at h2

end Levi

section Generation

open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

theorem commutator_perfectCore_facts {G : Type*} [Group G] [Finite G] {P Q : Subgroup G}
    (hQP : Q ≤ P) (hPN : P ≤ Subgroup.normalizer (Q : Set G)) :
    ⁅Q, CFSG.Quasithin.perfectCore P⁆ ≤ Q ∧
      P ≤ Subgroup.normalizer ((⁅Q, CFSG.Quasithin.perfectCore P⁆ : Subgroup G) : Set G) := by
  have _ := hQP
  constructor
  · refine Subgroup.commutator_le.2 fun q hq m hm => ?_
    have h1 : m * q⁻¹ * m⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.1 (hPN (CFSG.Quasithin.perfectCore_le P hm)) q⁻¹).1
        (Q.inv_mem hq)
    have : ⁅q, m⁆ = q * (m * q⁻¹ * m⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Q.mul_mem hq h1
  · exact le_normalizer_commutator_of_le_normalizer P Q _ hPN
      (Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore P))

theorem exists_units_ne_one'
    {F : Type} [Field F] [Finite F] (hF4 : 4 ≤ Nat.card F) :
    ∃ t : Fˣ, t ≠ 1 := by
  obtain ⟨u, hu⟩ := CFSG.LieType.BorelTits.exists_units_sq_ne_one hF4
  exact ⟨u, fun h => hu (by rw [h]; simp)⟩

omit [Finite K] [CharP K 2] in
include hσ3 in
theorem pow_three_equiv : σ ^ 3 = 1 :=
  RingEquiv.ext fun c =>
    (ringEquiv_pow_three_apply σ c).trans (ringHom_apply_apply_apply_of_pow_three hσ3 c)

theorem singleton_ne_univ_fa0 : ({fa0} : Set (Fin TwistTag.D4.foldedTag.rank)) ≠ Set.univ :=
  fun h => absurd (Set.mem_singleton_iff.1 (h ▸ Set.mem_univ fa1)) (by decide)

theorem singleton_ne_univ_fa1 : ({fa1} : Set (Fin TwistTag.D4.foldedTag.rank)) ≠ Set.univ :=
  fun h => absurd (Set.mem_singleton_iff.1 (h ▸ Set.mem_univ fa0)) (by decide)

theorem library_facts
    (a : Fin TwistTag.D4.foldedTag.rank)
    (hJ : ({a} : Set (Fin TwistTag.D4.foldedTag.rank)) ≠ Set.univ) :
    graphFixedParabolicRadical TwistTag.D4 K τ₀ {a} ≤ graphFixedParabolic TwistTag.D4 K τ₀ {a} ∧
      graphFixedParabolic TwistTag.D4 K τ₀ {a} ≤
        Subgroup.normalizer (graphFixedParabolicRadical TwistTag.D4 K τ₀ {a} : Set GL) ∧
      IsPGroup 2 ↥(graphFixedParabolicRadical TwistTag.D4 K τ₀ {a}) ∧
      graphFixedParabolic TwistTag.D4 K τ₀ {a} ⊓
          Subgroup.centralizer (graphFixedParabolicRadical TwistTag.D4 K τ₀ {a} : Set GL) ≤
        graphFixedParabolicRadical TwistTag.D4 K τ₀ {a} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hnorm, -, -, -, -, -, -, hpg, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ {a}
  exact ⟨hQP, (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hnorm, hpg 2,
    (diagram_fixed_proper_parabolic_root_radical_self_centralizing TwistTag.D4 K σ hJ).2⟩

include hσ3 in
theorem exists_weight_ne_one
    (hK4 : 4 ≤ Nat.card K) :
    ∃ a : K, a ≠ 0 ∧ a ≠ σ a * σ (σ a) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu⟩ := exists_units_ne_one' hK4
  have h3 : ∀ x : K, σ (σ (σ x)) = x := fun x => ringHom_apply_apply_apply_of_pow_three hσ3 x
  have hσne : ∀ x : K, x ≠ 0 → σ x ≠ 0 := fun x hx => (map_ne_zero σ).2 hx
  have h0 : (u : K) ≠ 0 := u.ne_zero
  have e1 := hcon u h0
  have e3 := hcon (σ (σ u)) (hσne _ (hσne _ h0))
  rw [h3] at e3
  have e4 : (σ (u : K)) ^ 2 = 1 := by
    have : (u : K) = u * σ u ^ 2 := by
      calc (u : K) = σ u * σ (σ u) := e1
        _ = σ u * (u * σ u) := by rw [e3]
        _ = u * σ u ^ 2 := by ring
    have h5 : (u : K) * (σ u ^ 2 - 1) = 0 := by linear_combination -this
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd h h0
    · exact sub_eq_zero.1 h
  have e5 : σ (u : K) = 1 := eq_one_of_sq_eq_one_charTwo e4
  have e6 : (u : K) = 1 := by
    have : σ (u : K) = σ 1 := by rw [e5, map_one]
    exact σ.injective this
  exact hu (Units.ext e6)

include hσ3 in
theorem generation_a0
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K τ₀))
    (hK4 : 4 ≤ Nat.card K) :
    Q0 σ ≤ ⁅Q0 σ, CFSG.Quasithin.perfectCore (P0 σ)⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ3' : σ ^ 3 = 1 := pow_three_equiv σ hσ3
  have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K τ₀ fa0), s.card = 4 := by
    have htop : orbitField TwistTag.D4 K τ₀ fa0 = ⊤ :=
      orbitField_D4_zero_eq_top σ (fun c => ringHom_apply_apply_apply_of_pow_three hσ3 c)
    have hc : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K τ₀ fa0) := by
      rw [htop, Nat.card_congr Subfield.topEquiv.toEquiv]; exact hK4
    exact exists_finset_card_four hc
  obtain ⟨R, hRx, hRH, hRW, hMP, -, -⟩ := levi_package σ fa0 hU hL4
  obtain ⟨hQP, hPN, hQ2, -⟩ := library_facts σ fa0 singleton_ne_univ_fa0
  obtain ⟨hEQ, hPE⟩ := commutator_perfectCore_facts hQP hPN
  set E := ⁅Q0 σ, CFSG.Quasithin.perfectCore (P0 σ)⁆ with hE
  have hcomm : ∀ m ∈ CFSG.Quasithin.perfectCore (P0 σ), ∀ q ∈ Q0 σ, ⁅m, q⁆ ∈ E :=
    fun m hm q hq => comm_mem_of_left hm hq
  have hx1 : ox₁ σ 1 ∈ CFSG.Quasithin.perfectCore (P0 σ) := by
    refine hMP ⟨uSL (1 : ↥(orbitField TwistTag.D4 K τ₀ fa0)), ?_⟩
    rw [hRx]; exact orbitX_fa0_eq σ 1
  have hn : canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa0) ∈
      CFSG.Quasithin.perfectCore (P0 σ) := hMP ⟨WSL, hRW⟩
  have hH : ∀ a : Kˣ, trialityTorusHom σ (a, 1) ∈ CFSG.Quasithin.perfectCore (P0 σ) := by
    intro a
    have e := trialityTorusHom_eq_orbitH hσ3' a (1 : (trialityFixedField K τ₀)ˣ)
    have h1 : trialityMiddleParam (σ := σ) (1 : (trialityFixedField K τ₀)ˣ) = 1 :=
      Units.ext (Subtype.ext rfl)
    rw [h1, orbitH_one', mul_one] at e
    rw [e]
    exact hMP ⟨HSL _, hRH _⟩
  have h5 : ∀ e : trialityFixedField K τ₀, ox₅ σ e ∈ E := by
    intro e
    have : ox₅ σ e = ⁅ox₁ σ 1, ox₄ σ (e : K)⁆ := by
      rw [rel14 σ hσ3, one_mul, trace_fixed σ hσ3]
    rw [this]
    exact hcomm _ hx1 _ (ox₄_mem_Q0 σ hσ3 _)
  have h2 : ∀ b : trialityFixedField K τ₀, ox₂ σ b ∈ E := by
    intro b
    have hw : canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa0) *
        ox₅ σ b * (canonicalRep (coxeterSystem TwistTag.D4.tag) K
          (TwistTag.D4.orbitReflection fa0))⁻¹ = ox₂ σ b := weyl_x5_x2 σ b
    have : ox₂ σ b = ⁅canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection fa0), ox₅ σ b⁆ * ox₅ σ b := by
      rw [commutatorElement_def, hw]; group
    rw [this]
    exact E.mul_mem (hcomm _ hn _ (ox₅_mem_Q0 σ hσ3 b)) (h5 b)
  obtain ⟨a, ha0, ha⟩ := exists_weight_ne_one σ hσ3 hK4
  have hN0 : a * σ a * σ (σ a) ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha0 ((map_ne_zero σ).2 ha0)) ((map_ne_zero σ).2 ((map_ne_zero σ).2 ha0))
  have hσa0 : σ a ≠ 0 := (map_ne_zero σ).2 ha0
  have hσσa0 : σ (σ a) ≠ 0 := (map_ne_zero σ).2 hσa0
  have hw3 : (a ^ 2 * (a * σ a * σ (σ a))⁻¹ : K) ≠ 1 := by
    intro h
    rw [mul_inv_eq_one₀ hN0] at h
    apply ha
    apply mul_left_cancel₀ ha0
    linear_combination h
  have hw4 : (σ a ^ 2 * σ (σ a) ^ 2 * (a * σ a * σ (σ a))⁻¹ : K) ≠ 1 := by
    intro h
    rw [mul_inv_eq_one₀ hN0] at h
    apply ha
    apply mul_left_cancel₀ (mul_ne_zero hσa0 hσσa0)
    linear_combination -h
  have hHa := hH (Units.mk0 a ha0)
  have h3 : ∀ c : K, ox₃ σ c ∈ E := fun c =>
    mem_of_weight (F := K) (E := E) (x := ox₃ σ) (ox₃_add σ hσ3)
      (h := trialityTorusHom σ (Units.mk0 a ha0, 1))
      (w := (a : K) ^ 2 * ((a : K) * σ a * σ (σ a))⁻¹) hw3
      (torus_a_ox₃ σ hσ3 (Units.mk0 a ha0))
      (fun s => hcomm _ hHa _ (ox₃_mem_Q0 σ hσ3 s)) c
  have h4 : ∀ c : K, ox₄ σ c ∈ E := fun c =>
    mem_of_weight (F := K) (E := E) (x := ox₄ σ) (ox₄_add σ hσ3)
      (h := trialityTorusHom σ (Units.mk0 a ha0, 1))
      (w := σ a ^ 2 * σ (σ a) ^ 2 * ((a : K) * σ a * σ (σ a))⁻¹) hw4
      (torus_a_ox₄ σ hσ3 (Units.mk0 a ha0))
      (fun s => hcomm _ hHa _ (ox₄_mem_Q0 σ hσ3 s)) c
  have h6 : ∀ f : trialityFixedField K τ₀, ox₆ σ f ∈ ⁅Q0 σ, Q0 σ⁆ := fun f => by
    have : ox₆ σ f = ⁅ox₂ σ 1, ox₅ σ f⁆ := by rw [rel25 σ hσ3, one_mul]
    rw [this]
    exact Subgroup.commutator_mem_commutator (ox₂_mem_Q0 σ hσ3 1) (ox₅_mem_Q0 σ hσ3 f)
  have hF : Q0 σ ≤ E ⊔ ⁅Q0 σ, Q0 σ⁆ := by
    intro g hg
    obtain ⟨b, c, d, e, f, rfl⟩ := (mem_radical_a0_iff σ hσ3).1 hg
    exact mul_mem (mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left (h2 b))
      (Subgroup.mem_sup_left (h3 c))) (Subgroup.mem_sup_left (h4 d)))
      (Subgroup.mem_sup_left (h5 e))) (Subgroup.mem_sup_right (h6 f))
  have hsup : E ⊔ ⁅Q0 σ, Q0 σ⁆ = Q0 σ := le_antisymm (sup_le hEQ (commutator_self_le _)) hF
  have hEeq : E = Q0 σ := eq_of_sup_commutator_eq (p := 2) hQ2 hEQ hsup
  exact hEeq.ge

include hσ3 in
theorem generation_a1
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K τ₀))
    (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K τ₀)) :
    Q1 σ ≤ ⁅Q1 σ, CFSG.Quasithin.perfectCore (P1 σ)⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ3' : σ ^ 3 = 1 := pow_three_equiv σ hσ3
  have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K τ₀ fa1), s.card = 4 := by
    have hc : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K τ₀ fa1) := by
      have : Nat.card ↥(orbitField TwistTag.D4 K τ₀ fa1) =
          Nat.card ↥(trialityFixedField K τ₀) :=
        Nat.card_congr (Equiv.subtypeEquivRight fun c =>
          (mem_orbitField_D4_one σ).trans (mem_trialityFixedField (K := K) (σ := τ₀)).symm)
      rw [this]; exact hk4
    exact exists_finset_card_four hc
  obtain ⟨R, hRx, hRH, -, hMP, -, -⟩ := levi_package σ fa1 hU hL4
  obtain ⟨hQP, hPN, hQ2, -⟩ := library_facts σ fa1 singleton_ne_univ_fa1
  obtain ⟨hEQ, hPE⟩ := commutator_perfectCore_facts hQP hPN
  set E := ⁅Q1 σ, CFSG.Quasithin.perfectCore (P1 σ)⁆ with hE
  have hcomm : ∀ m ∈ CFSG.Quasithin.perfectCore (P1 σ), ∀ q ∈ Q1 σ, ⁅m, q⁆ ∈ E :=
    fun m hm q hq => comm_mem_of_left hm hq
  have hx2 : ∀ β : trialityFixedField K τ₀, ox₂ σ β ∈ CFSG.Quasithin.perfectCore (P1 σ) := by
    intro β
    have hβ : (β : K) ∈ orbitField TwistTag.D4 K τ₀ fa1 := (mem_orbitField_D4_one σ).2 β.2
    refine hMP ⟨uSL (⟨(β : K), hβ⟩ : ↥(orbitField TwistTag.D4 K τ₀ fa1)), ?_⟩
    rw [hRx]; exact orbitX_fa1_eq σ ⟨(β : K), hβ⟩ β rfl
  have hH : ∀ b : (trialityFixedField K τ₀)ˣ,
      trialityTorusHom σ (1, b) ∈ CFSG.Quasithin.perfectCore (P1 σ) := by
    intro b
    have e := trialityTorusHom_eq_orbitH hσ3' 1 b
    have h1 : trialityOuterParam hσ3' (1 : Kˣ) = 1 := Units.ext (Subtype.ext rfl)
    rw [h1, orbitH_one', one_mul] at e
    rw [e]
    exact hMP ⟨HSL _, hRH _⟩
  have hHP : ∀ a : Kˣ, trialityTorusHom σ (a, 1) ∈ P1 σ := by
    intro a
    have e := trialityTorusHom_eq_orbitH hσ3' a (1 : (trialityFixedField K τ₀)ˣ)
    have h1 : trialityMiddleParam (σ := σ) (1 : (trialityFixedField K τ₀)ˣ) = 1 :=
      Units.ext (Subtype.ext rfl)
    rw [h1, orbitH_one', mul_one] at e
    rw [e]
    exact graphFixedRootBorel_le_graphFixedParabolic TwistTag.D4 K τ₀ {fa1}
      (graphFixedRootTorus_le_graphFixedRootBorel (orbitH_mem_graphFixedRootTorus TwistTag.D4 τ₀ fa0 _))
  obtain ⟨b₀, hb₀⟩ := exists_units_ne_one' hk4
  have hb₀K : ((b₀ : trialityFixedField K τ₀) : K) ≠ 1 := fun h =>
    hb₀ (Units.ext (Subtype.ext h))
  have h1 : ∀ c : K, ox₁ σ c ∈ E := fun c =>
    mem_of_weight (F := K) (E := E) (x := ox₁ σ) (ox₁_add σ hσ3)
      (h := trialityTorusHom σ (1, b₀)) (w := (((b₀ : trialityFixedField K τ₀) : K))⁻¹)
      (inv_ne_one.2 hb₀K) (torus_b_ox₁ σ hσ3 b₀)
      (fun s => hcomm _ (hH b₀) _ (ox₁_mem_Q1 σ hσ3 s)) c
  have h3 : ∀ c : K, ox₃ σ c ∈ E := fun c =>
    mem_of_weight (F := K) (E := E) (x := ox₃ σ) (ox₃_add σ hσ3)
      (h := trialityTorusHom σ (1, b₀)) (w := ((b₀ : trialityFixedField K τ₀) : K)) hb₀K
      (torus_b_ox₃ σ hσ3 b₀) (fun s => hcomm _ (hH b₀) _ (ox₃_mem_Q1 σ hσ3 s)) c
  have h5 : ∀ e : trialityFixedField K τ₀, ox₅ σ e ∈ E := fun e =>
    mem_of_weight (F := trialityFixedField K τ₀) (E := E) (x := ox₅ σ) (ox₅_add σ hσ3)
      (h := trialityTorusHom σ (1, b₀))
      (w := ((b₀⁻¹ : (trialityFixedField K τ₀)ˣ) : trialityFixedField K τ₀))
      (fun h => hb₀ (inv_eq_one.1 (Units.ext h))) (torus_b_ox₅ σ hσ3 b₀)
      (fun s => hcomm _ (hH b₀) _ (ox₅_mem_Q1 σ hσ3 s)) e
  have h6 : ∀ f : trialityFixedField K τ₀, ox₆ σ f ∈ E := fun f =>
    mem_of_weight (F := trialityFixedField K τ₀) (E := E) (x := ox₆ σ) (ox₆_add σ hσ3)
      (h := trialityTorusHom σ (1, b₀))
      (w := ((b₀ : (trialityFixedField K τ₀)ˣ) : trialityFixedField K τ₀))
      (fun h => hb₀ (Units.ext h)) (torus_b_ox₆ σ hσ3 b₀)
      (fun s => hcomm _ (hH b₀) _ (ox₆_mem_Q1 σ hσ3 s)) f
  have h4k : ∀ β : trialityFixedField K τ₀, ox₄ σ (β : K) ∈ E := by
    intro β
    have hm : ⁅ox₂ σ β, ox₁ σ 1⁆ ∈ E := hcomm _ (hx2 β) _ (ox₁_mem_Q1 σ hσ3 1)
    rw [ox₂_comm_ox₁ σ β] at hm
    have : ox₄ σ (β : K) = (ox₃ σ (β : K))⁻¹ *
        (ox₃ σ (β : K) * ox₄ σ (β : K) * ox₅ σ β * ox₆ σ (β * β)) *
        (ox₅ σ β * ox₆ σ (β * β))⁻¹ := by group
    rw [this]
    exact E.mul_mem (E.mul_mem (E.inv_mem (h3 _)) hm) (E.inv_mem (E.mul_mem (h5 β) (h6 _)))
  have h4 : ∀ c : K, ox₄ σ c ∈ E := by
    intro c
    by_cases hc : c = 0
    · rw [hc, ox₄_zero σ hσ3]; exact E.one_mem
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c⁻¹
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact inv_ne_zero hc (by simpa using hr)
    have hσr0 : σ r ≠ 0 := (map_ne_zero σ).2 hr0
    have hσσr0 : σ (σ r) ≠ 0 := (map_ne_zero σ).2 hσr0
    have hNk : r * σ r * σ (σ r) ∈ trialityFixedField K τ₀ := norm_mem_trialityFixedField hσ3' r
    let β : trialityFixedField K τ₀ := ⟨(r * σ r * σ (σ r))⁻¹, inv_mem hNk⟩
    have hcr : c = (r * r)⁻¹ := by rw [← hr, inv_inv]
    have hw : (σ r ^ 2 * σ (σ r) ^ 2 * (r * σ r * σ (σ r))⁻¹) * (β : K) = c := by
      change (σ r ^ 2 * σ (σ r) ^ 2 * (r * σ r * σ (σ r))⁻¹) * (r * σ r * σ (σ r))⁻¹ = c
      rw [hcr]
      field_simp
    have hconj := torus_a_ox₄ σ hσ3 (Units.mk0 r hr0) (β : K)
    have hmem := (Subgroup.mem_normalizer_iff.1 (hPE (hHP (Units.mk0 r hr0))) (ox₄ σ (β : K))).1
      (h4k β)
    rw [hconj] at hmem
    simp only [Units.val_mk0] at hmem
    rwa [hw] at hmem
  have hF : Q1 σ ≤ E := by
    intro g hg
    obtain ⟨a, c, d, e, f, rfl⟩ := (mem_radical_a1_iff σ hσ3).1 hg
    exact mul_mem (mul_mem (mul_mem (mul_mem (h1 a) (h3 c)) (h4 d)) (h5 e)) (h6 f)
  exact hF

end Generation

section Facts

open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

include hσ3 in
theorem isPGroup_posUnipotent
    : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K τ₀) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hcard, -⟩ := even_triality_positive_orbit_parametrization K σ hσ3
  have : Fintype K := Fintype.ofFinite K
  have : Fintype ↥(trialityFixedField K τ₀) := Fintype.ofFinite _
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  obtain ⟨m, -, hm⟩ := FiniteField.card ↥(trialityFixedField K τ₀) 2
  refine IsPGroup.of_card (n := (n : ℕ) * 3 + (m : ℕ) * 3) ?_
  rw [hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hn, hm, ← pow_mul, ← pow_mul,
    ← pow_add]

omit [CharP K 2] in
theorem perfectCore_bot_of_card_two
    (a : Fin TwistTag.D4.foldedTag.rank)
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K τ₀))
    (h2 : Nat.card ↥(orbitField TwistTag.D4 K τ₀ a) = 2) :
    CFSG.Quasithin.perfectCore (graphFixedParabolic TwistTag.D4 K τ₀ {a}) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite GL := finite_modGL
  obtain ⟨R, hVN, hNV, hsup, hRV, -⟩ := fixed_structure σ a
  have hVU : graphFixedSimpleComplement TwistTag.D4 K τ₀ a ≤
      graphFixedPosUnipotent TwistTag.D4 K τ₀ := graphFixedSimpleComplement_le a
  have hV2 : IsPGroup 2 ↥(graphFixedSimpleComplement TwistTag.D4 K τ₀ a) :=
    IsPGroup.of_injective hU (Subgroup.inclusion hVU) (Subgroup.inclusion_injective hVU)
  have hVs : Group.IsSolvable ↥(graphFixedSimpleComplement TwistTag.D4 K τ₀ a) := by
    have := hV2.isNilpotent
    infer_instance
  have hsolvSL : Group.IsSolvable (SL2 ↥(orbitField TwistTag.D4 K τ₀ a)) := by
    refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h2]
    norm_num
  have hMs : Group.IsSolvable ↥R.range :=
    Group.isSolvable_of_surjective (f := R.rangeRestrict) (MonoidHom.rangeRestrict_surjective R)
  have hNs : Group.IsSolvable ↥(fixedPosWeylGroup TwistTag.D4 K τ₀ a) :=
    isSolvable_of_levi hVN hNV hsup hVs hMs
  have hpcN : CFSG.Quasithin.perfectCore (fixedPosWeylGroup TwistTag.D4 K τ₀ a) = ⊥ :=
    (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot _).mp hNs
  rw [fixed_perfectCore_eq σ a, hpcN]

include hσ3 in
theorem parabolicFacts_a0
    (hK4 : 4 ≤ Nat.card K) : ParabolicFacts (P0 σ) (Q0 σ) := by
  have hU := isPGroup_posUnipotent σ hσ3
  obtain ⟨hQP, hPN, hQ2, hsc⟩ := library_facts σ fa0 singleton_ne_univ_fa0
  refine
    { le := hQP
      normalizes := hPN
      pGroup := hQ2
      selfCentralizing := hsc
      center_le := center_le_a0 σ hσ3
      nonabelian := nonabelian_a0 σ hσ3
      levi := Or.inr ⟨generation_a0 σ hσ3 hU hK4, ?_⟩ }
  have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K τ₀ fa0), s.card = 4 := by
    have htop : orbitField TwistTag.D4 K τ₀ fa0 = ⊤ :=
      orbitField_D4_zero_eq_top σ (fun c => ringHom_apply_apply_apply_of_pow_three hσ3 c)
    have hc : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K τ₀ fa0) := by
      rw [htop, Nat.card_congr Subfield.topEquiv.toEquiv]; exact hK4
    exact exists_finset_card_four hc
  obtain ⟨R, -, -, -, -, hsimple, g, hg, hk⟩ := levi_package σ fa0 hU hL4
  refine ⟨↥R.range, inferInstance, g, hsimple, hg, fun x hx => ?_⟩
  rw [show Q0 σ = graphFixedSimpleComplement TwistTag.D4 K τ₀ fa0 from
    radical_eq_simpleComplement τ₀ fa0 supp_fa0]
  exact hk x hx

include hσ3 in
theorem parabolicFacts_a1
    : ParabolicFacts (P1 σ) (Q1 σ) := by
  have hU := isPGroup_posUnipotent σ hσ3
  obtain ⟨hQP, hPN, hQ2, hsc⟩ := library_facts σ fa1 singleton_ne_univ_fa1
  refine
    { le := hQP
      normalizes := hPN
      pGroup := hQ2
      selfCentralizing := hsc
      center_le := center_le_a1 σ hσ3
      nonabelian := nonabelian_a1 σ hσ3
      levi := ?_ }
  have : Fintype ↥(trialityFixedField K τ₀) := Fintype.ofFinite _
  obtain ⟨m, -, hm⟩ := FiniteField.card ↥(trialityFixedField K τ₀) 2
  have hcard : Nat.card ↥(trialityFixedField K τ₀) = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card, hm]
  have hcardL : Nat.card ↥(orbitField TwistTag.D4 K τ₀ fa1) =
      Nat.card ↥(trialityFixedField K τ₀) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun c =>
      (mem_orbitField_D4_one σ).trans (mem_trialityFixedField (K := K) (σ := τ₀)).symm)
  have hmpos : 1 ≤ (m : ℕ) := m.pos
  rcases Nat.lt_or_ge (m : ℕ) 2 with hm2 | hm2
  · left
    have hm1 : (m : ℕ) = 1 := by omega
    have h2 : Nat.card ↥(orbitField TwistTag.D4 K τ₀ fa1) = 2 := by
      rw [hcardL, hcard, hm1, pow_one]
    rw [perfectCore_bot_of_card_two σ fa1 hU h2]
    exact bot_le
  · right
    have hk4 : 4 ≤ Nat.card ↥(trialityFixedField K τ₀) := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) hm2
    refine ⟨generation_a1 σ hσ3 hU hk4, ?_⟩
    have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K τ₀ fa1), s.card = 4 := by
      have hc : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K τ₀ fa1) := by
        rw [hcardL]; exact hk4
      exact exists_finset_card_four hc
    obtain ⟨R, -, -, -, -, hsimple, g, hg, hk⟩ := levi_package σ fa1 hU hL4
    refine ⟨↥R.range, inferInstance, g, hsimple, hg, fun x hx => ?_⟩
    rw [show Q1 σ = graphFixedSimpleComplement TwistTag.D4 K τ₀ fa1 from
      radical_eq_simpleComplement τ₀ fa1 supp_fa1]
    exact hk x hx

end Facts

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
