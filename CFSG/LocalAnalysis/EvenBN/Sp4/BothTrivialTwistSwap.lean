module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialField

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialTwistSwap

open Subgroup CFSG.Blueprint CFSG.Open
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer BothTrivialRankOne BothTrivialSlice BothTrivialField
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped MatrixGroups

section Setting

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
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐓₀" => (𝐑[Axis.one] ⊔ 𝐑[Axis.two] : Subgroup G)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)

theorem map_U_swap {u : G} (hU : ∀ x ∈ 𝐔[Axis.two], u * x * u⁻¹ ∈ 𝐔[Axis.one]) :
    (𝐔[Axis.two]).map (MulAut.conj u).toMonoidHom = 𝐔[Axis.one] := by
  refine eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hU x hx
  · rw [card_map_of_injective (MulAut.conj u).injective, FCHyp.card_U, FCHyp.card_U]

theorem map_C {u : G} (huC : u ∈ 𝐂) : (𝐂).map (MulAut.conj u).toMonoidHom = 𝐂 := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem huC hx) (inv_mem huC)
  · intro x hx
    refine ⟨u⁻¹ * x * u, mul_mem (mul_mem (inv_mem huC) hx) huC, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem map_D_swap {u : G} (huC : u ∈ 𝐂) (hU : ∀ x ∈ 𝐔[Axis.two], u * x * u⁻¹ ∈ 𝐔[Axis.one]) :
    (𝐃[Axis.two]).map (MulAut.conj u).toMonoidHom = 𝐃[Axis.one] := by
  have htu : u * t * u⁻¹ = t := by
    have := mem_centralizer_singleton_iff.mp huC
    rw [this]
    group
  have hV : (zpowers t ⊔ 𝐔[Axis.two]).map (MulAut.conj u).toMonoidHom =
      zpowers t ⊔ 𝐔[Axis.one] := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, map_U_swap hU]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, htu]
  rw [pCore_normalizer_map_conj u (zpowers t ⊔ 𝐔[Axis.two])]
  exact pCore_map_subtype_congr (congrArg (fun B : Subgroup G => normalizer (B : Set G)) hV)

theorem map_B_swap (h : FCHyp L K n φ t) {u : G} (huC : u ∈ 𝐂)
    (hU : ∀ x ∈ 𝐔[Axis.two], u * x * u⁻¹ ∈ 𝐔[Axis.one]) :
    (𝐁[Axis.two]).map (MulAut.conj u).toMonoidHom = 𝐁[Axis.one] := by
  rw [← h.D_inf_C Axis.two, Subgroup.map_inf_eq _ _ _ (MulAut.conj u).injective, map_C huC,
    map_D_swap huC hU, h.D_inf_C Axis.one]

theorem map_B_swap' (h : FCHyp L K n φ t) {u : G} (huC : u ∈ 𝐂)
    (huQ : u ∈ normalizer (𝐐 : Set G)) (hU : ∀ x ∈ 𝐔[Axis.two], u * x * u⁻¹ ∈ 𝐔[Axis.one]) :
    (𝐁[Axis.one]).map (MulAut.conj u).toMonoidHom = 𝐁[Axis.two] := by
  rcases h.map_B huQ Axis.one with h1 | h1
  · exfalso
    apply h.B_ne
    have h2 := map_B_swap h huC hU
    exact map_injective (MulAut.conj u).injective (h1.trans h2.symm)
  · exact h1

theorem map_X_swap (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) {u : G} (huC : u ∈ 𝐂)
    (huT : u ∈ normalizer (𝐓₀ : Set G))
    (hU : ∀ x ∈ 𝐔[Axis.two], u * x * u⁻¹ ∈ 𝐔[Axis.one]) :
    (𝐗[Axis.one]).map (MulAut.conj u).toMonoidHom = 𝐗[Axis.two] ∧
      (𝐗[Axis.two]).map (MulAut.conj u).toMonoidHom = 𝐗[Axis.one] := by
  have huQ : u ∈ normalizer (𝐐 : Set G) := centralizer_inf_normalizer_le h hbt ⟨huC, huT⟩
  exact ⟨map_X_eq h hbt (map_B_swap' h huC huQ hU), map_X_eq h hbt (map_B_swap h huC hU)⟩

end Setting

end BothTrivialTwistSwap

end CFSG.LocalAnalysis.EvenBN.Sp4
