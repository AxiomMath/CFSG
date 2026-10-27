module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbitsCoordinates
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenSymplectic
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbitsGroup
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public noncomputable section

universe u

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits

open Subgroup Module Matrix MulAction SymplecticFlag SymplecticTorusWeyl CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open scoped Pointwise IsMulCommutative

theorem card_GL_three_two : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3

theorem isSimpleGroup_GL_three_two : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
  CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh

variable {G : Type*} [Group G]

@[expose] def FusionOrbitPattern (Ω : Set G) (z : G) (A A₁ A₂a A₂n A₃ : Set G) : Prop :=
  z ∈ Ω ∧ Ω ⊆ {z} ∪ z • A₁ ∪ z • A₂a ∪ z • A₂n ∪ z • A₃ ∪ A₃ ∧
    (z • A₁ ⊆ Ω ∨ Disjoint (z • A₁) Ω) ∧ (z • A₂a ⊆ Ω ∨ Disjoint (z • A₂a) Ω) ∧
    (z • A₂n ⊆ Ω ∨ Disjoint (z • A₂n) Ω) ∧ (z • A₃ ⊆ Ω ∨ Disjoint (z • A₃) Ω) ∧
    (A₃ ⊆ Ω ∨ Disjoint A₃ Ω) ∧
    (Nat.card Ω = 8 ∨ Nat.card Ω = 15 ∨ Nat.card Ω = 36 ∨ Nat.card Ω = 64) ∧
    (Nat.card Ω = 8 → Ω = {z} ∪ z • A₁ ∨ Ω = {z} ∪ z • A₂a) ∧
    (Nat.card Ω = 64 → Ω = z • A ∨ Ω = {z} ∪ z • A₁ ∪ z • A₃ ∪ A₃ ∨
      Ω = {z} ∪ z • A₂a ∪ z • A₃ ∪ A₃ ∨ Ω = {z} ∪ z • A₁ ∪ z • A₂a ∪ z • A₂n ∪ A₃)

theorem card_conjClass_eq {z : G} {N₀ M : Subgroup G}
    (h : M ⊓ centralizer ({z} : Set G) = N₀) : Nat.card (conjClass M z) = N₀.relIndex M := by
  rw [card_conjClass, ← inf_relIndex_right, inf_comm, h]

theorem conj_fix {z g n : G} {M : Subgroup G} (hn : n ∈ M)
    (hg : ∀ w ∈ conjClass M z, g * w * g⁻¹ = w) :
    ∀ w ∈ conjClass M z, (n * g * n⁻¹) * w * (n * g * n⁻¹)⁻¹ = w := by
  intro w hw
  have h := hg (n⁻¹ * w * n⁻¹⁻¹) (conj_mem_conjClass (M.inv_mem hn) hw)
  calc n * g * n⁻¹ * w * (n * g * n⁻¹)⁻¹ = n * (g * (n⁻¹ * w * n⁻¹⁻¹) * g⁻¹) * n⁻¹ := by group
    _ = w := by rw [h]; group

theorem ker_toPermHom_eq {z : G} {R N₀ M : Subgroup G} (hRN₀ : R ≤ N₀) (hN₀M : N₀ ≤ M)
    (hstab : M ⊓ centralizer ({z} : Set G) ≤ N₀) (hzR : conjClass M z ⊆ R)
    (hRab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (hsimp : ∀ K : Subgroup G, R ≤ K → K ≤ N₀ → N₀ ≤ normalizer (K : Set G) → K = R ∨ K = N₀)
    {x y n : G} (hx : x ∈ conjClass M z) (hxy : x ≠ y) (hn : n ∈ N₀) (hnx : n * x * n⁻¹ = y) :
    (toPermHom M (conjClass M z)).ker = R.subgroupOf M := by
  set K := (toPermHom M (conjClass M z)).ker.map M.subtype with hK
  have hmemK : ∀ g, g ∈ K ↔ ∃ _ : g ∈ M, ∀ w ∈ conjClass M z, g * w * g⁻¹ = w := by
    intro g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m.2, (mem_ker_toPermHom_conjClass m).1 hm⟩
    · rintro ⟨hg, h⟩
      exact ⟨⟨g, hg⟩, (mem_ker_toPermHom_conjClass ⟨g, hg⟩).2 h, rfl⟩
  have hRK : R ≤ K := fun r hr => (hmemK r).2 ⟨hN₀M (hRN₀ hr), fun w hw => by
    rw [hRab r hr w (hzR hw), mul_inv_cancel_right]⟩
  have hKN₀ : K ≤ N₀ := fun k hk => by
    obtain ⟨hkM, h⟩ := (hmemK k).1 hk
    refine hstab ⟨hkM, mem_centralizer_singleton_iff.2 ?_⟩
    have := h z (self_mem_conjClass M z)
    calc k * z = k * z * k⁻¹ * k := by group
      _ = z * k := by rw [this]
  have hKn : N₀ ≤ normalizer (K : Set G) := fun m hm => mem_normalizer_iff.2 fun g => by
    rw [hmemK, hmemK]
    constructor
    · rintro ⟨hg, h⟩
      exact ⟨M.mul_mem (M.mul_mem (hN₀M hm) hg) (M.inv_mem (hN₀M hm)), conj_fix (hN₀M hm) h⟩
    · rintro ⟨hg, h⟩
      have hg' : g = m⁻¹ * (m * g * m⁻¹) * m⁻¹⁻¹ := by group
      refine ⟨?_, ?_⟩
      · rw [hg']
        exact M.mul_mem (M.mul_mem (M.inv_mem (hN₀M hm)) hg) (M.inv_mem (M.inv_mem (hN₀M hm)))
      · rw [hg']
        exact conj_fix (M.inv_mem (hN₀M hm)) h
  rcases hsimp K hRK hKN₀ hKn with hKR | hKN
  · ext m
    rw [mem_ker_toPermHom_conjClass, mem_subgroupOf]
    constructor
    · intro h
      have : (m : G) ∈ K := (hmemK m).2 ⟨m.2, h⟩
      rwa [hKR] at this
    · intro hm w hw
      rw [hRab m hm w (hzR hw), mul_inv_cancel_right]
  · exfalso
    have hnK : n ∈ K := by
      rw [hKN]
      exact hn
    obtain ⟨-, h⟩ := (hmemK n).1 hnK
    exact hxy ((h x hx).symm.trans hnx)

theorem card_conjClass_dvd {z : G} {R N₀ N M : Subgroup G} (hRN₀ : R ≤ N₀) (hN₀M : N₀ ≤ M)
    (hMN : M ≤ N) (hstab : M ⊓ centralizer ({z} : Set G) = N₀) (ψ : N →* MulAut R)
    (hψ : ψ.ker = R.subgroupOf N) (hidx : R.relIndex N₀ = 168) {k : ℕ}
    (hAut : Nat.card (MulAut R) = 168 * k) : Nat.card (conjClass M z) ∣ k := by
  have hker : (ψ.comp (inclusion hMN)).ker = R.subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hψ, mem_subgroupOf,
      mem_subgroupOf]
    rfl
  have h1 : R.relIndex M ∣ Nat.card (MulAut R) := by
    have := Subgroup.index_ker (ψ.comp (inclusion hMN))
    rw [hker] at this
    change (R.subgroupOf M).index ∣ _
    rw [this]
    exact Subgroup.card_subgroup_dvd_card _
  rw [← relIndex_mul_relIndex R N₀ M hRN₀ hN₀M, hidx, ← card_conjClass_eq hstab, hAut] at h1
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1

theorem eq_or_eq_of_card_conjClass {z : G} {N₀ N M : Subgroup G} (hN₀M : N₀ ≤ M) (hMN : M ≤ N)
    (hstab : ∀ K : Subgroup G, N₀ ≤ K → K ≤ N → K ⊓ centralizer ({z} : Set G) = N₀)
    (hdeg : ∀ K : Subgroup G, N₀ < K → K ≤ N → Nat.card (conjClass K z) = 8 ∨
      Nat.card (conjClass K z) = 15 ∨ Nat.card (conjClass K z) = 36 ∨
      Nat.card (conjClass K z) = 64)
    (hM : Nat.card (conjClass M z) = 15 ∨ Nat.card (conjClass M z) = 36)
    (K : Subgroup G) (hN₀K : N₀ ≤ K) (hKM : K ≤ M) : K = N₀ ∨ K = M := by
  by_contra hc
  obtain ⟨hc₁, hc₂⟩ := not_or.1 hc
  have h1 := hdeg K (lt_of_le_of_ne hN₀K (Ne.symm hc₁)) (hKM.trans hMN)
  have h2 := relIndex_mul_relIndex N₀ K M hN₀K hKM
  rw [← card_conjClass_eq (hstab K hN₀K (hKM.trans hMN)),
    ← card_conjClass_eq (hstab M hN₀M hMN)] at h2
  have h3 : K.relIndex M ≠ 1 := fun h => hc₂ (le_antisymm hKM (relIndex_eq_one.1 h))
  rcases h1 with h | h | h | h <;> rcases hM with h' | h' <;> rw [h, h'] at h2 <;> omega

theorem subset_or_disjoint {z : G} {N₀ M : Subgroup G} (hM : N₀ ≤ M) {P : Set G}
    (hP : ∀ x ∈ P, ∀ y ∈ P, ∃ n ∈ N₀, n * x * n⁻¹ = y) :
    P ⊆ conjClass M z ∨ Disjoint P (conjClass M z) := by
  by_cases h : Disjoint P (conjClass M z)
  · exact Or.inr h
  · left
    obtain ⟨x, hxP, hxM⟩ := Set.not_disjoint_iff.1 h
    intro y hy
    obtain ⟨n, hn, rfl⟩ := hP x hxP y hy
    exact conj_mem_conjClass (hM hn) hxM

theorem exists_conj_ne [Finite G] {N₀ : Subgroup G} {P : Set G}
    (hP : ∀ x ∈ P, ∀ y ∈ P, ∃ n ∈ N₀, n * x * n⁻¹ = y) (hc : 1 < Nat.card P) {x : G}
    (hx : x ∈ P) : ∃ y n, x ≠ y ∧ n ∈ N₀ ∧ n * x * n⁻¹ = y := by
  rw [Nat.card_coe_set_eq] at hc
  obtain ⟨y, hy, hyx⟩ := Set.exists_ne_of_one_lt_ncard hc x
  obtain ⟨n, hn, hnx⟩ := hP x hx y hy
  exact ⟨y, n, Ne.symm hyx, hn, hnx⟩

section Setting

variable [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "𝒮" => (𝒩 ⊓ centralizer (Singleton.singleton z : Set G) : Subgroup G)
local notation "ℒ" => (normalizer ((𝒜 : Subgroup G) : Set G) ⊓ L : Subgroup G)

omit [Finite G] in
include hzC hinf hz hb hnd hV he in
theorem radical_facts : 𝒜 ⊓ zpowers z = ⊥ ∧ IsElementaryAbelian 2 ℛ ∧ Nat.card ℛ = 128 := by
  obtain ⟨hAe, hAc, -, -⟩ := pullSub_radical hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  exact sup_facts hzC hinf hz (pullSub_le φ _) hAe hAc

omit [Finite G] in
include hzC hinf hz hb hnd hV he in
theorem mul_comm_of_mem_radical {x y : G} (hx : x ∈ ℛ) (hy : y ∈ ℛ) : x * y = y * x :=
  mul_comm_of_isElementaryAbelian (radical_facts hzC hinf hz hb hnd hV φ he).2.1 hx hy

omit [Finite G] in
include hzC hinf hz hb hnd hV he in
theorem mul_self_of_mem_radical {x : G} (hx : x ∈ ℛ) : x * x = 1 :=
  mul_self_of_isElementaryAbelian (radical_facts hzC hinf hz hb hnd hV φ he).2.1 hx

omit [Finite G] in
include hzC hinf hz hb hnd hV he in
theorem radical_le_stab : ℛ ≤ 𝒮 := fun _ hx =>
  mem_inf.2 ⟨le_normalizer hx, mem_centralizer_singleton_iff.2
    (mul_comm_of_mem_radical hzC hinf hz hb hnd hV φ he hx (mem_sup_right (mem_zpowers z)))⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hzC hsup hinf in
theorem stab_eq : 𝒮 = ℒ ⊔ zpowers z ∧ ℒ ⊓ zpowers z = ⊥ :=
  normalizer_inf_eq hzC hsup hinf (pullSub_le φ _)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hzC in
theorem zpowers_le_centralizer_levi : zpowers z ≤ centralizer (ℒ : Set G) := fun _ ht =>
  mem_centralizer_iff.2 fun l hl => mem_centralizer_iff.1 (zpowers_le.2 hzC ht) l (mem_inf.1 hl).2

omit [Finite G] in
include hzC hsup hinf hb hnd hV in
theorem leviHom_mem_stab (D : GL (Fin 3) (ZMod 2)) : leviHom φ he D ∈ 𝒮 := by
  rw [(stab_eq hzC hsup hinf φ).1]
  exact mem_sup_left (leviHom_mem_normalizer φ he hb hnd hV D)

omit [Finite G] in
include hzC hsup hinf hb hnd hV he in
theorem exists_sigma :
    ∃ σ : 𝒮 →* GL (Fin 3) (ZMod 2), Function.Surjective σ ∧ σ.ker = (ℛ).subgroupOf 𝒮 ∧
      (∀ (n : 𝒮) (hn : (n : G) ∈ L) (j : Fin 3), linOf (φ ⟨n, hn⟩) (e (Sum.inl j)) =
        ∑ i, (σ n : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j • e (Sum.inl i)) ∧
      ∀ (n : 𝒮) (a : G) (ha : a ∈ L) (B : Matrix (Fin 3) (Fin 3) (ZMod 2)), Bᵀ = B →
        LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
        ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
          LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
            fromBlocks 1 ((σ n : Matrix (Fin 3) (Fin 3) (ZMod 2)) * B *
              (σ n : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ) 0 1 := by
  obtain ⟨-, -, -, hNL⟩ := pullSub_radical hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  obtain ⟨hS, hLz⟩ := stab_eq hzC hsup hinf φ (e := e)
  have hcoord := coordinates hb hnd hV φ he
  have hmem : ∀ n : ℒ, ((spCoord he).toMonoidHom.comp (φ.toMonoidHom.comp
      (inclusion (inf_le_right : ℒ ≤ L)))) n ∈ stabilizer 3 (ZMod 2) (lagrangianZero 3) := by
    intro n
    have h : (n : G) ∈ pullSub φ (subspaceStabilizer b (lagrangianOf e)) := hNL ▸ n.2
    obtain ⟨_, hφ⟩ := mem_pullSub.1 h
    exact (mem_subspaceStabilizer_iff_spCoord he _).1 hφ
  set σA : ℒ →* GL (Fin 3) (ZMod 2) :=
    (lagrangianLevi 3).comp (MonoidHom.codRestrict _ _ hmem) with hσA
  have hσA_val : ∀ n : ℒ, (σA n : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (LinearMap.toMatrix e e (linOf (φ ⟨n, (mem_inf.1 n.2).2⟩))).toBlocks₁₁ := fun n => by
    rw [hσA, MonoidHom.comp_apply, coe_lagrangianLevi]
    rfl
  have hσA_ker : ∀ n : ℒ, σA n = 1 ↔ (n : G) ∈ 𝒜 := fun n => by
    rw [hσA, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_lagrangianLevi, mem_subgroupOf]
    change spCoord he (φ ⟨n, (mem_inf.1 n.2).2⟩) ∈ (tauSym 3).range ↔ _
    rw [← mem_pointwiseStabilizer_iff_spCoord he, mem_pullSub]
    exact ⟨fun h => ⟨(mem_inf.1 n.2).2, h⟩, fun ⟨_, h⟩ => h⟩
  have hzL := zpowers_le_centralizer_levi hzC φ (e := e)
  set π : 𝒮 →* ℒ := (projL hzL hLz).comp (MulEquiv.subgroupCongr hS).toMonoidHom with hπ
  have hπ_mul : ∀ x : 𝒮, ∃ s ∈ zpowers z, (x : G) = π x * s := fun x =>
    mulProd_projL hzL hLz (MulEquiv.subgroupCongr hS x)
  have hπ_eq : ∀ (x : 𝒮) {l s : G}, l ∈ ℒ → s ∈ zpowers z → (x : G) = l * s → (π x : G) = l :=
    fun x _ _ hl hs hx => projL_eq_of_mul hzL hLz (MulEquiv.subgroupCongr hS x) hl hs hx
  have hAℒ : 𝒜 ≤ ℒ := fun a ha => mem_inf.2 ⟨le_normalizer ha, pullSub_le φ _ ha⟩
  refine ⟨σA.comp π, fun D => ?_, ?_, fun n hn j => ?_, fun n a ha B hB hτ => ?_⟩
  ·
    have hl := leviHom_mem_normalizer φ he hb hnd hV D
    refine ⟨⟨leviHom φ he D, hS ▸ mem_sup_left hl⟩, Units.ext ?_⟩
    have hπl : π ⟨leviHom φ he D, hS ▸ mem_sup_left hl⟩ = ⟨leviHom φ he D, hl⟩ :=
      Subtype.ext (hπ_eq _ hl (one_mem _) (mul_one _).symm)
    rw [MonoidHom.comp_apply, hπl, hσA_val]
    change (LinearMap.toMatrix e e (linOf (φ ⟨spHom φ he (leviSp D), spHom_mem φ he _⟩))).toBlocks₁₁
      = _
    rw [toMatrix_spHom, spMatrixOf, coe_leviSp, toBlocks_fromBlocks₁₁]
  ·
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hσA_ker, mem_subgroupOf]
    obtain ⟨s, hs, hx⟩ := hπ_mul x
    constructor
    · intro h
      rw [hx]
      exact mul_mem_sup h hs
    · intro h
      obtain ⟨a, ha, s', hs', hx'⟩ := (mem_sup_of_le_centralizer
        (zpowers_le_centralizer_pullSub φ hzC _)).1 h
      rw [hπ_eq x (hAℒ ha) hs' hx'.symm]
      exact ha
  ·
    obtain ⟨s, hs, hx⟩ := hπ_mul n
    have hsL : s ∈ L := by
      have : s = (π n : G)⁻¹ * n := by rw [hx]; group
      rw [this]
      exact L.mul_mem (L.inv_mem (mem_inf.1 (π n).2).2) hn
    have hs1 : s = 1 := by
      have : s ∈ L ⊓ zpowers z := mem_inf.2 ⟨hsL, hs⟩
      rwa [hinf, mem_bot] at this
    have hnℒ : (n : G) ∈ ℒ := by
      rw [hx, hs1, mul_one]
      exact (π n).2
    have hπn : π n = ⟨n, hnℒ⟩ := Subtype.ext (hπ_eq n hnℒ (one_mem _) (mul_one _).symm)
    rw [MonoidHom.comp_apply, hπn, hσA_val]
    exact (hcoord.2 n hnℒ).2.1 j
  ·
    obtain ⟨s, hs, hx⟩ := hπ_mul n
    set l : G := (π n : G) with hl
    have hlℒ : l ∈ ℒ := (π n).2
    have hsa : s * a = a * s := (mem_centralizer_iff.1 (zpowers_le.2 hzC hs) a ha).symm
    have hconj : (n : G) * a * (n : G)⁻¹ = l * a * l⁻¹ := by
      rw [hx]
      calc l * s * a * (l * s)⁻¹ = l * (s * a) * s⁻¹ * l⁻¹ := by group
        _ = l * a * l⁻¹ := by rw [hsa]; group
    have hmemL : l * a * l⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (mem_inf.1 hlℒ).2 ha) (L.inv_mem (mem_inf.1 hlℒ).2)
    refine ⟨hconj ▸ hmemL, ?_⟩
    have h1 : (⟨(n : G) * a * (n : G)⁻¹, hconj ▸ hmemL⟩ : L) =
        ⟨l, (mem_inf.1 hlℒ).2⟩ * ⟨a, ha⟩ * ⟨l, (mem_inf.1 hlℒ).2⟩⁻¹ :=
      Subtype.ext hconj
    rw [h1, φ.map_mul, φ.map_mul, φ.map_inv, (hcoord.2 l hlℒ).2.2 a ha B hB hτ,
      MonoidHom.comp_apply, hσA_val]

omit [Finite G] in
include hzC hsup hinf hb hnd hV he in
theorem exists_conj_of_mem_piece {P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop}
    (hP : ∀ B B' : binarySymMatrices 3, P B → P B' →
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank ∧
        ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 →
          ((∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) ↔
            ∀ i, (B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0))) :
    (∀ x ∈ tauSet φ e P, ∀ y ∈ tauSet φ e P, ∃ n ∈ 𝒮, n * x * n⁻¹ = y) ∧
      ∀ x ∈ z • tauSet φ e P, ∀ y ∈ z • tauSet φ e P, ∃ n ∈ 𝒮, n * x * n⁻¹ = y := by
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨D, hD⟩ := exists_conj_of_mem_tauSet φ he hP hx hy
    exact ⟨_, leviHom_mem_stab hzC hsup hinf hb hnd hV φ he D, hD⟩
  · obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨a', ha', rfl⟩ := hy
    obtain ⟨D, hD⟩ := exists_conj_of_mem_tauSet φ he hP ha ha'
    refine ⟨_, leviHom_mem_stab hzC hsup hinf hb hnd hV φ he D, ?_⟩
    have hcomm : leviHom φ he D * z = z * leviHom φ he D :=
      mem_centralizer_iff.1 hzC _ (leviHom_mem φ he D)
    simp only [smul_eq_mul]
    rw [← hD]
    calc leviHom φ he D * (z * a) * (leviHom φ he D)⁻¹ =
        leviHom φ he D * z * a * (leviHom φ he D)⁻¹ := by group
      _ = z * (leviHom φ he D * a * (leviHom φ he D)⁻¹) := by rw [hcomm]; group

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include he in
theorem card_pieces :
    Nat.card (z • tauSet φ e (fun B => B.rank = 1) : Set G) = 7 ∧
      Nat.card (z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0) : Set G) = 7 ∧
      Nat.card (z • tauSet φ e (fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0) : Set G) = 21 ∧
      Nat.card (z • tauSet φ e (fun B => B.rank = 3) : Set G) = 28 ∧
      Nat.card (tauSet φ e (fun B => B.rank = 3) : Set G) = 28 := by
  simp only [Set.natCard_smul_set, card_tauSet φ he]
  exact ⟨card_sym_rank_one, card_sym_rank_two_alternating, card_sym_rank_two_nonalternating,
    card_sym_rank_three, card_sym_rank_three⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hinf hz in
theorem disjoint_smul_tauSet (P Q : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop) :
    Disjoint (z • tauSet φ e P) (tauSet φ e Q) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, ⟨haL, -⟩, rfl⟩ ⟨hzaL, -⟩
  apply notMem_of_inf_eq_bot hinf hz
  have h : z = z • a * a⁻¹ := by rw [smul_eq_mul, mul_inv_cancel_right]
  rw [h]
  exact L.mul_mem hzaL (L.inv_mem haL)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include he in
theorem notMem_smul_tauSet {P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop} (hP : ¬ P 0) :
    z ∉ z • tauSet φ e P := by
  rintro ⟨a, ha, h⟩
  have h1 : a = 1 := by simpa [smul_eq_mul] using h
  rw [h1] at ha
  exact one_notMem_tauSet φ he hP ha

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include he in
theorem smul_pullSub_eq :
    z • (𝒜 : Set G) = {z} ∪ z • tauSet φ e (fun B => B.rank = 1) ∪
      z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0) ∪
      z • tauSet φ e (fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0) ∪
      z • tauSet φ e (fun B => B.rank = 3) := by
  have hA : (𝒜 : Set G) = {1} ∪ tauSet φ e (fun B => B.rank = 1) ∪
      tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0) ∪
      tauSet φ e (fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0) ∪
      tauSet φ e (fun B => B.rank = 3) := by
    ext a
    rw [SetLike.mem_coe, mem_pullSub_iff φ he]
    constructor
    · rintro ⟨B, rfl⟩
      rcases sym_orbit_cases B.toAdd with h0 | h1 | h2 | h2 | h3
      · have hB : B = 1 := Multiplicative.toAdd.injective (Subtype.ext h0)
        rw [hB, map_one]
        exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ((mem_tauSet_iff φ he).2 ⟨B, h1, rfl⟩))))
      · exact Or.inl (Or.inl (Or.inr ((mem_tauSet_iff φ he).2 ⟨B, h2, rfl⟩)))
      · exact Or.inl (Or.inr ((mem_tauSet_iff φ he).2 ⟨B, h2, rfl⟩))
      · exact Or.inr ((mem_tauSet_iff φ he).2 ⟨B, h3, rfl⟩)
    · rintro ((((h | h) | h) | h) | h)
      · obtain rfl := Set.mem_singleton_iff.1 h
        exact ⟨1, map_one _⟩
      all_goals exact (mem_pullSub_iff φ he).1 (tauSet_subset φ he _ h)
  rw [hA, Set.smul_set_union, Set.smul_set_union, Set.smul_set_union, Set.smul_set_union,
    Set.smul_set_singleton, smul_eq_mul, mul_one]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem inf_centralizer_eq {M : Subgroup G} (hSM : 𝒮 ≤ M) (hMN : M ≤ 𝒩) :
    M ⊓ centralizer ({z} : Set G) = 𝒮 :=
  le_antisymm (fun _ hx => mem_inf.2 ⟨hMN (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩)
    (le_inf hSM inf_le_right)

include hzC hsup hinf hz hb hnd hV he in
theorem conjClass_subset {M : Subgroup G} (hMN : M ≤ 𝒩) :
    conjClass M z ⊆ {z} ∪ z • tauSet φ e (fun B => B.rank = 1) ∪
      z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0) ∪
      z • tauSet φ e (fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0) ∪
      z • tauSet φ e (fun B => B.rank = 3) ∪ tauSet φ e (fun B => B.rank = 3) := by
  intro x hx
  have hN : x ∈ conjClass 𝒩 z := conjClass_mono hMN z hx
  have heq := conj_set_eq hzC hsup hinf hz hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  have hx' : x ∈ {x | ∃ g : G, g * z * g⁻¹ = x} ∩ (ℛ : Set G) := by
    rw [← heq]
    exact hN
  exact conj_mem_pieces φ he hzC hsup hinf hz hb hnd hV hx'.2 hx'.1

include hzC hsup hinf hz hb hnd hV he in
theorem conjClass_subset_radical {M : Subgroup G} (hMN : M ≤ 𝒩) :
    conjClass M z ⊆ (ℛ : Set G) := by
  intro x hx
  have hN : x ∈ conjClass 𝒩 z := conjClass_mono hMN z hx
  have heq := conj_set_eq hzC hsup hinf hz hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  have hx' : x ∈ {x | ∃ g : G, g * z * g⁻¹ = x} ∩ (ℛ : Set G) := by
    rw [← heq]
    exact hN
  exact hx'.2

include hzC hinf hz hb hnd hV he in
theorem card_mulAut_radical :
    Nat.card (MulAut ℛ) = 168 * (2 ^ 18 * 3 ^ 3 * 5 * 7 * 31 * 127) := by
  obtain ⟨-, hRe, hRc⟩ := radical_facts hzC hinf hz hb hnd hV φ he
  have : IsMulCommutative ℛ := hRe.toIsMulCommutative
  rw [card_mulAut_of_sq_eq_one (n := 7) (fun x => ?_) (by rw [hRc]; norm_num), prod_GL_seven]
  exact Subtype.ext (by
    rw [SubgroupClass.coe_pow, pow_two]
    exact mul_self_of_mem_radical hzC hinf hz hb hnd hV φ he x.2)

omit [Finite G] in
include hzC hsup hinf hb hnd hV he in
theorem eq_or_eq_of_le_stab (K : Subgroup G) (hRK : ℛ ≤ K) (hKS : K ≤ 𝒮)
    (hn : 𝒮 ≤ normalizer (K : Set G)) : K = ℛ ∨ K = 𝒮 := by
  obtain ⟨σ, hσs, hσk, -⟩ := exists_sigma hzC hsup hinf hb hnd hV φ he
  have := isSimpleGroup_GL_three_two
  exact eq_or_eq_of_surjective σ hσs hσk hRK hKS hn

omit [Finite G] in
include hzC hsup hinf hb hnd hV he in
theorem relIndex_radical_stab : (ℛ).relIndex 𝒮 = 168 := by
  obtain ⟨σ, hσs, hσk, -⟩ := exists_sigma hzC hsup hinf hb hnd hV φ he
  change ((ℛ).subgroupOf 𝒮).index = 168
  rw [← hσk, Subgroup.index_ker, MonoidHom.range_eq_top.2 hσs, Subgroup.card_top,
    card_GL_three_two]

include hzC hsup hinf hz hb hnd hV he in
theorem exists_orderOf_seven : ∃ g ∈ 𝒮, orderOf g = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hRS := radical_le_stab hzC hinf hz hb hnd hV φ he
  have hcard : Nat.card 𝒮 = 168 * 128 := by
    have h := ((ℛ).subgroupOf 𝒮).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hRS).toEquiv,
      (radical_facts hzC hinf hz hb hnd hV φ he).2.2] at h
    have h' : ((ℛ).subgroupOf 𝒮).index = 168 :=
      relIndex_radical_stab hzC hsup hinf hb hnd hV φ he
    rw [h'] at h
    exact h.symm
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := 𝒮) 7 (by rw [hcard]; norm_num)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

include hzC hsup hinf hz hb hnd hV he in
theorem fusionOrbitPattern {M : Subgroup G} (hSM : 𝒮 < M) (hMN : M ≤ 𝒩) :
    FusionOrbitPattern (conjClass M z) z (𝒜 : Set G) (tauSet φ e fun B => B.rank = 1)
      (tauSet φ e fun B => B.rank = 2 ∧ ∀ i, B i i = 0)
      (tauSet φ e fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0) (tauSet φ e fun B => B.rank = 3) := by
  obtain ⟨c₁, c₂a, c₂n, c₃⟩ := congr_classes
  have o₁ := exists_conj_of_mem_piece hzC hsup hinf hb hnd hV φ he
    (P := fun B => B.rank = 1) c₁
  have o₂ := exists_conj_of_mem_piece hzC hsup hinf hb hnd hV φ he
    (P := fun B => B.rank = 2 ∧ ∀ i, B i i = 0) c₂a
  have o₃ := exists_conj_of_mem_piece hzC hsup hinf hb hnd hV φ he
    (P := fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0) c₂n
  have o₄ := exists_conj_of_mem_piece hzC hsup hinf hb hnd hV φ he
    (P := fun B => B.rank = 3) c₃
  obtain ⟨k₁, k₂, k₃, k₄, k₅⟩ := card_pieces φ he (z := z)
  have hstab := inf_centralizer_eq φ hSM.le hMN
  obtain ⟨hAe, hAc, hAC, -⟩ := pullSub_radical hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  have hRC := centralizer_sup_eq hzC hsup hinf hz (pullSub_le φ _) hAe hAc hAC
  have hdvd := card_conjClass_dvd (radical_le_stab hzC hinf hz hb hnd hV φ he) hSM.le hMN hstab
    (conjNormalizer ℛ) (ker_conjNormalizer hRC)
    (relIndex_radical_stab hzC hsup hinf hb hnd hV φ he)
    (card_mulAut_radical hzC hinf hz hb hnd hV φ he)
  have hne : Nat.card (conjClass M z) ≠ 1 := by
    rw [card_conjClass_eq hstab]
    intro h
    exact hSM.not_ge (relIndex_eq_one.1 h)
  have d : ∀ {P Q : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop}, (∀ B, P B → Q B → False) →
      Disjoint (z • tauSet φ e P) (z • tauSet φ e Q) := fun h =>
    Set.disjoint_smul_set.2 (disjoint_tauSet φ he h)
  have hzA₃ : z ∉ tauSet φ e (fun B => B.rank = 3) := fun h =>
    notMem_of_inf_eq_bot hinf hz (pullSub_le φ _ (tauSet_subset φ he _ h))
  have d₁₂ : Disjoint (z • tauSet φ e fun B => B.rank = 1)
      (z • tauSet φ e fun B => B.rank = 2 ∧ ∀ i, B i i = 0) :=
    d fun B h h' => by rw [h] at h'; exact absurd h'.1 (by norm_num)
  have d₁₃ : Disjoint (z • tauSet φ e fun B => B.rank = 1)
      (z • tauSet φ e fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0) :=
    d fun B h h' => by rw [h] at h'; exact absurd h'.1 (by norm_num)
  have d₁₄ : Disjoint (z • tauSet φ e fun B => B.rank = 1)
      (z • tauSet φ e fun B => B.rank = 3) :=
    d fun B h h' => by rw [h] at h'; exact absurd h' (by norm_num)
  have d₂₃ : Disjoint (z • tauSet φ e fun B => B.rank = 2 ∧ ∀ i, B i i = 0)
      (z • tauSet φ e fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0) :=
    d fun B h h' => h'.2 h.2
  have d₂₄ : Disjoint (z • tauSet φ e fun B => B.rank = 2 ∧ ∀ i, B i i = 0)
      (z • tauSet φ e fun B => B.rank = 3) :=
    d fun B h h' => by rw [h.1] at h'; exact absurd h' (by norm_num)
  have d₃₄ : Disjoint (z • tauSet φ e fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0)
      (z • tauSet φ e fun B => B.rank = 3) :=
    d fun B h h' => by rw [h.1] at h'; exact absurd h' (by norm_num)
  have hsub := conjClass_subset hzC hsup hinf hz hb hnd hV φ he hMN
  have s₁ := subset_or_disjoint hSM.le o₁.2 (z := z)
  have s₂ := subset_or_disjoint hSM.le o₂.2 (z := z)
  have s₃ := subset_or_disjoint hSM.le o₃.2 (z := z)
  have s₄ := subset_or_disjoint hSM.le o₄.2 (z := z)
  have s₅ := subset_or_disjoint hSM.le o₄.1 (z := z)
  obtain ⟨h1, h8, h64⟩ := pattern_of_pieces (self_mem_conjClass M z) hsub s₁ s₂ s₃ s₄ s₅
    (notMem_smul_tauSet φ he (by simp)) (notMem_smul_tauSet φ he (by simp))
    (notMem_smul_tauSet φ he (by simp)) (notMem_smul_tauSet φ he (by simp)) hzA₃
    d₁₂ d₁₃ d₁₄ (disjoint_smul_tauSet hinf hz φ _ _) d₂₃ d₂₄
    (disjoint_smul_tauSet hinf hz φ _ _) d₃₄
    (disjoint_smul_tauSet hinf hz φ _ _) (disjoint_smul_tauSet hinf hz φ _ _)
    k₁ k₂ k₃ k₄ k₅ hdvd hne
  refine ⟨self_mem_conjClass M z, hsub, s₁, s₂, s₃, s₄, s₅, h1, h8, fun h => ?_⟩
  rcases h64 h with h | h | h | h
  · exact Or.inl (h.trans (smul_pullSub_eq φ he).symm)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

include hzC hsup hinf hz hb hnd hV he in
theorem ker_toPermHom_conjClass_eq {M : Subgroup G} (hSM : 𝒮 < M) (hMN : M ≤ 𝒩) :
    (toPermHom M (conjClass M z)).ker = (ℛ).subgroupOf M := by
  obtain ⟨c₁, c₂a, c₂n, c₃⟩ := congr_classes
  have o₁ := exists_conj_of_mem_piece hzC hsup hinf hb hnd hV φ he
    (P := fun B => B.rank = 1) c₁
  have o₂ := exists_conj_of_mem_piece hzC hsup hinf hb hnd hV φ he
    (P := fun B => B.rank = 2 ∧ ∀ i, B i i = 0) c₂a
  have o₃ := exists_conj_of_mem_piece hzC hsup hinf hb hnd hV φ he
    (P := fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0) c₂n
  have o₄ := exists_conj_of_mem_piece hzC hsup hinf hb hnd hV φ he
    (P := fun B => B.rank = 3) c₃
  obtain ⟨k₁, k₂, k₃, k₄, k₅⟩ := card_pieces φ he (z := z)
  obtain ⟨-, hsub, -, -, -, -, -, hcard, -, -⟩ :=
    fusionOrbitPattern hzC hsup hinf hz hb hnd hV φ he hSM hMN
  have h1 : 1 < (conjClass M z).ncard := by
    rw [← Nat.card_coe_set_eq]
    rcases hcard with h | h | h | h <;> rw [h] <;> norm_num
  obtain ⟨x, hx, hxz⟩ := Set.exists_ne_of_one_lt_ncard h1 z
  have key : ∃ P : Set G, x ∈ P ∧ 1 < Nat.card P ∧
      ∀ x ∈ P, ∀ y ∈ P, ∃ n ∈ 𝒮, n * x * n⁻¹ = y := by
    rcases hsub hx with ((((h | h) | h) | h) | h) | h
    · exact absurd (Set.mem_singleton_iff.1 h) hxz
    · exact ⟨_, h, by rw [k₁]; norm_num, o₁.2⟩
    · exact ⟨_, h, by rw [k₂]; norm_num, o₂.2⟩
    · exact ⟨_, h, by rw [k₃]; norm_num, o₃.2⟩
    · exact ⟨_, h, by rw [k₄]; norm_num, o₄.2⟩
    · exact ⟨_, h, by rw [k₅]; norm_num, o₄.1⟩
  obtain ⟨P, hxP, hPc, hP⟩ := key
  obtain ⟨y, n, hxy, hn, hnx⟩ := exists_conj_ne hP hPc hxP
  exact ker_toPermHom_eq (radical_le_stab hzC hinf hz hb hnd hV φ he) hSM.le
    (inf_centralizer_eq φ hSM.le hMN).le
    (conjClass_subset_radical hzC hsup hinf hz hb hnd hV φ he hMN)
    (fun _ hx _ hy => mul_comm_of_mem_radical hzC hinf hz hb hnd hV φ he hx hy)
    (eq_or_eq_of_le_stab hzC hsup hinf hb hnd hV φ he) hx hxy hn hnx

include hzC hsup hinf hz hb hnd hV he in
theorem simple_of_card_conjClass {M : Subgroup G} (hSM : 𝒮 < M) (hMN : M ≤ 𝒩)
    (hdeg : Nat.card (conjClass M z) = 15 ∨ Nat.card (conjClass M z) = 36) :
    ((ℛ).subgroupOf M).Normal ∧ ∀ [((ℛ).subgroupOf M).Normal],
      IsSimpleGroup (M ⧸ (ℛ).subgroupOf M) ∧ (∃ a c : M ⧸ (ℛ).subgroupOf M, a * c ≠ c * a) ∧
      IsPreprimitive M (conjClass M z) ∧
      (Nat.card (conjClass M z) = 15 → Nat.card (M ⧸ (ℛ).subgroupOf M) = 2520) ∧
      (Nat.card (conjClass M z) = 36 → Nat.card (M ⧸ (ℛ).subgroupOf M) = 6048) := by
  have hRS := radical_le_stab hzC hinf hz hb hnd hV φ he
  have hRM : ℛ ≤ M := hRS.trans hSM.le
  have hRM' : ℛ ≠ M := fun h => hSM.not_ge (h ▸ hRS)
  have hstab := inf_centralizer_eq φ hSM.le hMN
  have hidx := relIndex_radical_stab hzC hsup hinf hb hnd hV φ he
  have hker := ker_toPermHom_conjClass_eq hzC hsup hinf hz hb hnd hV φ he hSM hMN
  have hfaith : ∀ m ∈ M, (∀ x ∈ conjClass M z, m * x * m⁻¹ = x) → m ∈ ℛ := fun m hm h => by
    have : (⟨m, hm⟩ : M) ∈ (toPermHom M (conjClass M z)).ker :=
      (mem_ker_toPermHom_conjClass _).2 h
    rw [hker, mem_subgroupOf] at this
    exact this
  have hmax : ∀ K : Subgroup G, 𝒮 ≤ K → K ≤ M → K = 𝒮 ∨ K = M :=
    eq_or_eq_of_card_conjClass hSM.le hMN (fun K h1 h2 => inf_centralizer_eq φ h1 h2)
      (fun K h1 h2 => (fusionOrbitPattern hzC hsup hinf hz hb hnd hV φ he h1 h2).2.2.2.2.2.2.2.1)
      hdeg
  obtain ⟨g, hg, hg7⟩ := exists_orderOf_seven hzC hsup hinf hz hb hnd hV φ he
  have hJ : ∀ J : Subgroup G, ℛ ≤ J → J ≤ M → M ≤ normalizer (J : Set G) → J = ℛ ∨ J = M :=
    fun J hRJ hJM hJn => eq_or_eq_of_maximal hRS hSM.le inf_le_right hstab.le hMN
      (conjClass_subset_radical hzC hsup hinf hz hb hnd hV φ he hMN)
      (fun _ hx _ hy => mul_comm_of_mem_radical hzC hinf hz hb hnd hV φ he hx hy) hfaith
      (eq_or_eq_of_le_stab hzC hsup hinf hb hnd hV φ he) hmax hdeg hg hg7
      (fun _ hr => mul_self_of_mem_radical hzC hinf hz hb hnd hV φ he hr) hRJ hJM hJn
  have hRn : ((ℛ).subgroupOf M).Normal := ⟨fun r hr m => by
    rw [mem_subgroupOf] at hr ⊢
    simpa using (mem_normalizer_iff.1 (hMN m.2) r).1 hr⟩
  have hcardMR : (ℛ).relIndex M = 168 * Nat.card (conjClass M z) := by
    rw [← relIndex_mul_relIndex _ _ _ hRS hSM.le, hidx, ← card_conjClass_eq hstab]
  refine ⟨hRn, ?_⟩
  intro inst
  have hsimple : IsSimpleGroup (M ⧸ (ℛ).subgroupOf M) := isSimpleGroup_quotient hRM hRM' hJ
  refine ⟨hsimple, ?_, ?_, fun h => ?_, fun h => ?_⟩
  ·
    by_contra hab
    have hcomm : ∀ a c : M ⧸ (ℛ).subgroupOf M, a * c = c * a := fun a c => by
      by_contra h
      exact hab ⟨a, c, h⟩
    set H' := ((𝒮).subgroupOf M).map (QuotientGroup.mk' ((ℛ).subgroupOf M)) with hH'
    have hH'n : H'.Normal := ⟨fun n hn q => by
      rw [hcomm q n, mul_inv_cancel_right]
      exact hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H' with h | h
    · have hSR : 𝒮 ≤ ℛ := fun x hx => by
        have h1 : ((⟨x, hSM.le hx⟩ : M) : M ⧸ (ℛ).subgroupOf M) ∈ H' :=
          ⟨⟨x, hSM.le hx⟩, mem_subgroupOf.2 hx, rfl⟩
        rw [h, mem_bot, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
        exact h1
      have := relIndex_eq_one.2 hSR
      rw [hidx] at this
      exact absurd this (by norm_num)
    · apply hSM.not_ge
      intro m hm
      have h1 : ((⟨m, hm⟩ : M) : M ⧸ (ℛ).subgroupOf M) ∈ H' := h ▸ mem_top _
      obtain ⟨s, hs, hsm⟩ := h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf] at hsm
      have hsS : (s : G) ∈ 𝒮 := mem_subgroupOf.1 hs
      have : m = s * ((s : G)⁻¹ * m) := by group
      rw [this]
      exact Subgroup.mul_mem _ hsS (hRS (by simpa using hsm))
  ·
    have hnt : Nontrivial (conjClass M z) := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      rcases hdeg with h | h <;> rw [h] <;> norm_num
    rw [← isCoatom_stabilizer_iff_preprimitive M
      (⟨z, self_mem_conjClass M z⟩ : conjClass M z), stabilizer_conjClass]
    refine ⟨fun htop => ?_, fun K hK => ?_⟩
    · apply hSM.not_ge
      intro m hm
      have : (⟨m, hm⟩ : M) ∈ (centralizer ({z} : Set G)).subgroupOf M := htop ▸ mem_top _
      rw [mem_subgroupOf] at this
      rw [← hstab]
      exact mem_inf.2 ⟨hm, this⟩
    · have hSK : 𝒮 ≤ K.map M.subtype := fun x hx =>
        ⟨⟨x, hSM.le hx⟩, hK.le (mem_subgroupOf.2 (mem_inf.1 hx).2), rfl⟩
      rcases hmax _ hSK (map_subtype_le K) with h | h
      · exfalso
        apply hK.not_ge
        intro k hk
        rw [mem_subgroupOf]
        have : (k : G) ∈ K.map M.subtype := ⟨k, hk, rfl⟩
        rw [h] at this
        exact (mem_inf.1 this).2
      · rw [eq_top_iff]
        intro m _
        have : (m : G) ∈ K.map M.subtype := by
          rw [h]
          exact m.2
        obtain ⟨k, hk, hkm⟩ := this
        rw [← Subtype.ext hkm]
        exact hk
  · change ((ℛ).subgroupOf M).index = 2520
    change (ℛ).relIndex M = 2520
    rw [hcardMR, h]
  · change ((ℛ).subgroupOf M).index = 6048
    change (ℛ).relIndex M = 6048
    rw [hcardMR, h]

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Subgroup Module Matrix MulAction SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

theorem standard_binary_symplectic_six_fusion_orbit_lengths {G : Type} [Group G] [Finite G]
    (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) :
    (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype = zpowers z ∧
    z ∈ centralizer (L : Set G) ∧ L ⊔ zpowers z = centralizer ({z} : Set G) ∧
    L ⊓ zpowers z = ⊥ ∧
    ∀ {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      {b : BilinForm (ZMod 2) V}, b.IsAlt → b.Nondegenerate → finrank (ZMod 2) V = 6 →
      ∀ φ : L ≃* bilinIsometryGroup b,
        (∀ (y : G) (hy : y ∈ L), orderOf y = 2 →
          finrank (ZMod 2) (LinearMap.range (linOf (φ ⟨y, hy⟩) - 1)) ≤ 2 →
            ¬ ∃ g : G, g * z * g⁻¹ = y) ∧
        ∀ {W : Submodule (ZMod 2) V}, IsTotallyIsotropic b W → finrank (ZMod 2) W = 3 →
        ∀ e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V, IsSymplecticBasis b e → W = lagrangianOf e →
          let A := pullSub φ (pointwiseStabilizer b W)
          let R := A ⊔ zpowers z
          let N := normalizer (R : Set G)
          let N₀ := N ⊓ centralizer ({z} : Set G)
          let A₁ := tauSet φ e fun B => B.rank = 1
          let A₂a := tauSet φ e fun B => B.rank = 2 ∧ ∀ i, B i i = 0
          let A₂n := tauSet φ e fun B => B.rank = 2 ∧ ¬ ∀ i, B i i = 0
          let A₃ := tauSet φ e fun B => B.rank = 3
          (A : Set G) = tauSet φ e (fun _ => True) ∧
          A ⊓ zpowers z = ⊥ ∧ IsElementaryAbelian 2 R ∧ Nat.card R = 128 ∧
          centralizer (R : Set G) = R ∧
          conjClass N z = {x | ∃ g : G, g * z * g⁻¹ = x} ∩ (R : Set G) ∧
          conjClass N z ≠ {z} ∧
          stabilizer N (⟨z, self_mem_conjClass N z⟩ : conjClass N z) = N₀.subgroupOf N ∧
          (∃ ψ : N →* MulAut R, (∀ n r, (ψ n r : G) = n * r * (n : G)⁻¹) ∧
            ψ.ker = R.subgroupOf N) ∧
          (toPermHom N (conjClass N z)).ker = R.subgroupOf N ∧
          N₀ = (normalizer (A : Set G) ⊓ L) ⊔ zpowers z ∧
          (normalizer (A : Set G) ⊓ L) ⊓ zpowers z = ⊥ ∧
          (∃ ρ : (normalizer (A : Set G) ⊓ L : Subgroup G) →*
              LinearMap.GeneralLinearGroup (ZMod 2) W,
            Function.Surjective ρ ∧ ρ.ker = A.subgroupOf (normalizer (A : Set G) ⊓ L) ∧
            ∀ (n : (normalizer (A : Set G) ⊓ L : Subgroup G)) (w : W),
              (((ρ n : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w : V) =
                linOf (φ ⟨n, (Subgroup.mem_inf.1 n.2).2⟩) w) ∧
          (∃ σ : N₀ →* GL (Fin 3) (ZMod 2), Function.Surjective σ ∧ σ.ker = R.subgroupOf N₀ ∧
            (∀ (n : N₀) (hn : (n : G) ∈ L) (j : Fin 3), linOf (φ ⟨n, hn⟩) (e (Sum.inl j)) =
              ∑ i, (σ n : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j • e (Sum.inl i)) ∧
            ∀ (n : N₀) (a : G) (ha : a ∈ L) (B : Matrix (Fin 3) (Fin 3) (ZMod 2)), Bᵀ = B →
              LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
              ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
                LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
                  fromBlocks 1 ((σ n : Matrix (Fin 3) (Fin 3) (ZMod 2)) * B *
                    (σ n : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ) 0 1) ∧
          Nat.card (z • A₁ : Set G) = 7 ∧ Nat.card (z • A₂a : Set G) = 7 ∧
          Nat.card (z • A₂n : Set G) = 21 ∧ Nat.card (z • A₃ : Set G) = 28 ∧
          Nat.card A₃ = 28 ∧
          FusionOrbitPattern (conjClass N z) z (A : Set G) A₁ A₂a A₂n A₃ ∧
          ∀ M : Subgroup G, N₀ < M → M ≤ N →
            (toPermHom M (conjClass M z)).ker = R.subgroupOf M ∧
            FusionOrbitPattern (conjClass M z) z (A : Set G) A₁ A₂a A₂n A₃ ∧
            (Nat.card (conjClass M z) = 15 ∨ Nat.card (conjClass M z) = 36 →
              (R.subgroupOf M).Normal ∧ ∀ [(R.subgroupOf M).Normal],
                IsSimpleGroup (M ⧸ R.subgroupOf M) ∧
                (∃ a c : M ⧸ R.subgroupOf M, a * c ≠ c * a) ∧
                IsPreprimitive M (conjClass M z) ∧
                (Nat.card (conjClass M z) = 15 → Nat.card (M ⧸ R.subgroupOf M) = 2520) ∧
                (Nat.card (conjClass M z) = 36 → Nat.card (M ⧸ R.subgroupOf M) = 6048)) := by
  obtain ⟨hTz, hzC, hsup, hinf, -, hrest⟩ :=
    standard_binary_symplectic_six_cyclic_kernel_and_first_fusion hG hL hLn hZ hmodel T hT hzT hz
      hH
  refine ⟨hTz, hzC, hsup, hinf, fun {V} _ _ _ {b} hb hnd hV φ => ⟨fun y hy _ hrk =>
    not_conj_of_rank_le_two φ hzC hsup hinf hz hb hnd hV hy hrk, fun {W} hW hd e he hWe => ?_⟩⟩
  obtain ⟨hAz, hRe, hRc, hRC, hconj, hne, hψ, hN₀, hNAz, hρ, -⟩ := hrest hb hnd hV φ hW hd
  subst hWe
  intro A R N N₀ A₁ A₂a A₂n A₃
  have hne' : conjClass N z ≠ {z} := fun h => hne (hconj.symm.trans h)
  have hSN : N₀ < N := lt_of_le_of_ne inf_le_left fun h => hne' (by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hn' : n ∈ N₀ := by
        rw [h]
        exact hn
      rw [Set.mem_singleton_iff, mem_centralizer_singleton_iff.1 (mem_inf.1 hn').2,
        mul_inv_cancel_right]
    · intro hx
      rw [Set.mem_singleton_iff.1 hx]
      exact self_mem_conjClass N z)
  obtain ⟨k₁, k₂, k₃, k₄, k₅⟩ := card_pieces φ he (z := z)
  have hstab : stabilizer N (⟨z, self_mem_conjClass N z⟩ : conjClass N z) = N₀.subgroupOf N := by
    rw [stabilizer_conjClass]
    ext n
    rw [mem_subgroupOf, mem_subgroupOf, mem_inf]
    exact ⟨fun h => ⟨n.2, h⟩, fun h => h.2⟩
  exact ⟨(tauSet_top φ he).symm, hAz, hRe, hRc, hRC, hconj, hne', hstab, hψ,
    ker_toPermHom_conjClass_eq hzC hsup hinf hz hb hnd hV φ he hSN le_rfl, hN₀, hNAz, hρ,
    exists_sigma hzC hsup hinf hb hnd hV φ he, k₁, k₂, k₃, k₄, k₅,
    fusionOrbitPattern hzC hsup hinf hz hb hnd hV φ he hSN le_rfl, fun M h1 h2 =>
      ⟨ker_toPermHom_conjClass_eq hzC hsup hinf hz hb hnd hV φ he h1 h2,
        fusionOrbitPattern hzC hsup hinf hz hb hnd hV φ he h1 h2,
        simple_of_card_conjClass hzC hsup hinf hz hb hnd hV φ he h1 h2⟩⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
