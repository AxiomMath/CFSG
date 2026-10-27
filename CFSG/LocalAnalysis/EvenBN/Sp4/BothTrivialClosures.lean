module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialClosuresLayer
public import CFSG.LocalAnalysis.SteinbergSFBothTrivialClosureSetup
import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.KProperOddCoreFreeLayer
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.SteinbergBVSp6LayerStatements

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialRankOne

open Subgroup CFSG.Blueprint
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped MatrixGroups

section Generic

variable {G : Type} [Group G]

theorem barSub_le_normalClosure {X Y Z : Subgroup G} (hY : Y ≤ normalizer (X : Set G))
    (hZ : Z ≤ closure {x : G | ∃ g ∈ normalizer (X : Set G), ∃ y ∈ Y ⊔ X, x = g⁻¹ * y * g}) :
    barSub X Z ≤ normalClosure (barSub X Y : Set (BarM X)) := by
  set P : Subgroup G :=
    ((normalClosure (barSub X Y : Set (BarM X))).comap (barMap X)).map
      (normalizer (X : Set G)).subtype with hP
  have hYX : Y ⊔ X ≤ normalizer (X : Set G) := sup_le hY le_normalizer
  have hYbar : ∀ m : ↥(normalizer (X : Set G)), (m : G) ∈ Y ⊔ X → barMap X m ∈ barSub X Y := by
    intro m hm
    rw [sup_comm, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hY] at hm
    obtain ⟨x, hx, y, hy, hxy⟩ := hm
    have hyN : y ∈ normalizer (X : Set G) := hY hy
    have hxN : x ∈ normalizer (X : Set G) := le_normalizer hx
    have hm' : m = ⟨x, hxN⟩ * ⟨y, hyN⟩ := Subtype.ext hxy.symm
    rw [hm', map_mul, barMap_eq_one_iff.mpr hx, one_mul]
    exact ⟨⟨y, hyN⟩, mem_subgroupOf.mpr hy, rfl⟩
  have hNP : closure {x : G | ∃ g ∈ normalizer (X : Set G), ∃ y ∈ Y ⊔ X,
      x = g⁻¹ * y * g} ≤ P := by
    rw [closure_le]
    rintro _ ⟨g, hg, y, hy, rfl⟩
    have hyN := hYX hy
    refine ⟨⟨g, hg⟩⁻¹ * ⟨y, hyN⟩ * ⟨g, hg⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap, map_mul, map_mul, map_inv]
    have h1 := (normalClosure_normal (s := (barSub X Y : Set (BarM X)))).conj_mem _
      (subset_normalClosure (hYbar ⟨y, hyN⟩ hy)) (barMap X ⟨g, hg⟩)⁻¹
    rwa [inv_inv] at h1
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨m', hm', e⟩ := hNP (hZ (mem_subgroupOf.mp hm))
  rw [show m' = m from Subtype.ext e] at hm'
  exact hm'

theorem card_le_two_of_sylow_eq_zpowers [Finite G] {C : Subgroup G} {τ : G}
    (hτ : orderOf τ = 2) (hV : ∃ V : Sylow 2 C, (V : Subgroup C).map C.subtype = zpowers τ)
    {P : Subgroup G} (hPC : P ≤ C) (hP : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  obtain ⟨V, hV⟩ := hV
  refine GMSK.card_le_two_of_sylow (fun S => ?_) hPC hP
  rw [Nat.card_congr (Sylow.equiv S V).toEquiv,
    ← card_map_of_injective C.subtype_injective, hV, Nat.card_zpowers, hτ]

end Generic

section Closures

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (𝐗[Axis.one] ⊔ 𝐗[Axis.two] : Subgroup G)

theorem normalizer_X_ne_top [IsSimpleGroup G] (h : FCHyp L K n φ t) (i : Axis) :
    normalizer (𝐗[i] : Set G) ≠ ⊤ := by
  intro htop
  have hN : (𝐗[i]).Normal := normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (𝐗[i]) with hbot | htop'
  · have h1 := card_X h i
    rw [hbot, card_bot] at h1
    have : 0 < Nat.card K := Nat.card_pos
    have h4 := h.four_le_card
    have : 1 < Nat.card K ^ 6 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  · have htX : t ∈ 𝐗[i] ⊓ centralizer ({t} : Set G) :=
      ⟨htop' ▸ mem_top t, mem_centralizer_singleton_iff.mpr rfl⟩
    rw [X_inf_C h i] at htX
    exact h.setup.t_not_mem_L (pull_le φ _ htX)

theorem both_trivial_rank_one_closures (hsel : GMSK.FixedRootSelector fun D _ => Catalog D)
    (hsmall : SmallSurvivorsNoElementary) [IsSimpleGroup G]
    (hKp : CFSG.Assembly.KProper Catalog G) (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) :
    ∃ α : ↥(barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))) ≃* SL(2, K),
      (∀ (M : SL(2, K)) (m : ↥(normalizer (𝐗[i] : Set G))),
        (m : G) = ((φ.symm (sHom K i M) : L) : G) →
          ((α.symm M : ↥(barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)))) : BarM 𝐗[i]) =
            barMap 𝐗[i] m) ∧
      ClosureSelection (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))) α
        (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩) (barSub 𝐗[i] 𝐒) n := by
  have hf := closureSetupFacts h hbt i
  obtain ⟨e, he⟩ := hf.equiv_K
  refine ⟨e.symm, fun M m hm => by rw [MulEquiv.symm_symm]; exact he M m hm, ?_⟩
  let _ : Fintype K := Fintype.ofFinite K
  have hk : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, h.setup.card_K]
  set τ := barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩ with hτdef
  have hτ : orderOf τ = 2 := hf.orderOf_tau
  have hKτ := hf.K_le
  have hτK : τ ∈ centralizer ((barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) : Subgroup _) :
      Set (BarM 𝐗[i])) :=
    mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hKτ hx)
  have hsyl := GMSK.exists_sylow_inf_centralizer_eq_zpowers hτ hτK
    (fun P hPC hP => card_le_two_of_sylow_eq_zpowers hτ hf.sylow_Y hPC hP)
  have hM : CFSG.SectionRank.IsKGroupCat (BarM 𝐗[i]) :=
    GMSK.isKGroupCat_of_section_of_kProper hKp (normalizer_X_ne_top h i) _
  have hV2 : ∀ v ∈ barSub 𝐗[i] 𝐒, v * v = 1 := fun v hv => by
    have := hf.elem_S
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := barSub 𝐗[i] 𝐒) v hv
    rwa [pow_two] at this
  have hNC := hf.S_le_NC
  have hCU := hf.CU_le
  have hVA := barSub_le_normalClosure hCU hNC
  exact closure_layer_selection hsel hsmall hM h.setup.two_le hk e.symm hτ hKτ hf.K_normal hsyl
    hV2 hf.card_S hVA hf.tau_S

end Closures

end BothTrivialRankOne

end CFSG.LocalAnalysis.EvenBN.Sp4
