module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductAxis
public import CFSG.LocalAnalysis.EvenBN.Common.ProductClosure

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialProduct

open Subgroup CFSG.Blueprint CFSG.Open
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer BothTrivialRankOne BothTrivialSlice BothTrivialField
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.LocalAnalysis.EvenBN.Common (prodFst)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (ProductAlternative)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductAxis
open scoped MatrixGroups

section Abstract

variable {G : Type} [Group G] {k : Type} [Field k]

theorem exists_rho_aux {X CU NC : Subgroup G} {t : G} {s : SL(2, k) →* G}
    (hNCN : NC ≤ normalizer (X : Set G))
    (hbar : barSub X NC = normalClosure (barSub X CU : Set (BarM X)))
    (ht : t ∈ normalizer (X : Set G)) (hτ : orderOf (barMap X ⟨t, ht⟩) = 2)
    (e : SL(2, k) ≃* ↥(barSub X CU))
    (he : ∀ (M : SL(2, k)) (m : ↥(normalizer (X : Set G))), (m : G) = s M →
      (e M : BarM X) = barMap X m)
    (α : ↥(barSub X CU) ≃* SL(2, k))
    (hP : ProductAlternative (barSub X CU) α (barMap X ⟨t, ht⟩)) :
    ∃ ρ : NC →* SL(2, k) × SL(2, k), Function.Surjective ρ ∧
      ρ.ker = X.subgroupOf NC ∧
      (∀ x y : NC, (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap) ∧
      ∃ β : SL(2, k) ≃* SL(2, k), ∀ (M : SL(2, k)) (hM : s M ∈ NC), ρ ⟨_, hM⟩ = (β M, β M) := by
  obtain ⟨ψ, hψdiag, hψswap⟩ := hP
  have hτ2 : barMap X ⟨t, ht⟩ * barMap X ⟨t, ht⟩ = 1 := by
    have := pow_orderOf_eq_one (barMap X ⟨t, ht⟩)
    rwa [hτ, pow_two] at this
  let ρ₁ : NC →* normalClosure (barSub X CU : Set (BarM X)) :=
    ((barMap X).comp (Subgroup.inclusion hNCN)).codRestrict _ fun n => by
      rw [← hbar]
      exact ⟨⟨(n : G), hNCN n.2⟩, mem_subgroupOf.mpr n.2, rfl⟩
  have hρ₁ : ∀ n : NC,
      ((ρ₁ n : normalClosure (barSub X CU : Set (BarM X))) : BarM X) =
        barMap X ⟨(n : G), hNCN n.2⟩ := fun _ => rfl
  have hρ₁surj : Function.Surjective ρ₁ := by
    rintro ⟨x, hx⟩
    rw [← hbar] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨⟨m, mem_subgroupOf.mp hm⟩, Subtype.ext rfl⟩
  refine ⟨ψ.toMonoidHom.comp ρ₁, ψ.surjective.comp hρ₁surj, ?_, ?_, e.trans α, ?_⟩
  · ext n
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change ψ (ρ₁ n) = 1 ↔ (n : G) ∈ X
    refine (map_eq_one_iff ψ ψ.injective).trans ?_
    rw [Subtype.ext_iff]
    exact barMap_eq_one_iff (a := ⟨(n : G), hNCN n.2⟩)
  · intro x y hxy
    change ψ (ρ₁ y) = (ψ (ρ₁ x)).swap
    refine hψswap (ρ₁ x) (ρ₁ y) ?_
    have hy : barMap X ⟨(y : G), hNCN y.2⟩ =
        barMap X ⟨t, ht⟩ * barMap X ⟨(x : G), hNCN x.2⟩ * (barMap X ⟨t, ht⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hxy)
    rw [hρ₁, hρ₁, hy, inv_eq_of_mul_eq_one_right hτ2]
  · intro M hM
    change ψ (ρ₁ ⟨_, hM⟩) = _
    exact hψdiag (e M) (ρ₁ ⟨_, hM⟩) ((hρ₁ _).trans (he M ⟨_, hNCN hM⟩ rfl).symm)

theorem sup_map_conj_weyl_eq_top [CharP k 2] (β : SL(2, k) ≃* SL(2, k)) :
    (upperSL2 k).map β.toMonoidHom ⊔
      ((upperSL2 k).map β.toMonoidHom).map (MulAut.conj (β (weylSL2 k))).toMonoidHom = ⊤ := by
  have h1 : ((upperSL2 k).map β.toMonoidHom).map (MulAut.conj (β (weylSL2 k))).toMonoidHom =
      ((upperSL2 k).map (MulAut.conj (weylSL2 k)).toMonoidHom).map β.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  rw [h1, ← Subgroup.map_sup, upperSL2_sup_conj_weyl, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top]
  exact β.surjective

end Abstract

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
local notation "𝐊[" i "]" => barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))
set_option quotPrecheck false in
local notation "𝐍𝐂[" i "]" => closure {x : G | ∃ g ∈ normalizer (𝐗[i] : Set G),
  ∃ y ∈ (L ⊓ centralizer (𝐔[i] : Set G) : Subgroup G) ⊔ 𝐗[i], x = g⁻¹ * y * g}

theorem exists_rho (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) (α : 𝐊[i] ≃* SL(2, K))
    (hP : ProductAlternative 𝐊[i] α (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩)) :
    ∃ ρ : 𝐍𝐂[i] →* SL(2, K) × SL(2, K), Function.Surjective ρ ∧
      ρ.ker = 𝐗[i].subgroupOf 𝐍𝐂[i] ∧
      (∀ x y : 𝐍𝐂[i], (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap) ∧
      ∃ β : SL(2, K) ≃* SL(2, K), ∀ (M : SL(2, K))
        (hM : ((φ.symm (sHom K i M) : L) : G) ∈ 𝐍𝐂[i]), ρ ⟨_, hM⟩ = (β M, β M) := by
  have hf := closureSetupFacts h hbt i
  obtain ⟨e, he⟩ := hf.equiv_K
  exact exists_rho_aux (NC_le_normalizer_X h i) (barSub_NC_eq h hbt i) hf.t_mem hf.orderOf_tau e he
    α hP

omit [Finite G] [Finite K] in
theorem X_sup_X_swap (i : Axis) : 𝐗[i] ⊔ 𝐗[i.swap] = 𝐒 := by
  cases i
  · rfl
  · exact sup_comm _ _

theorem card_F_inf_map_conj_sHom_weylSL2 (h : FCHyp L K n φ t) (i : Axis) :
    Nat.card (𝐅 ⊓ 𝐅.map (MulAut.conj ((φ.symm (sHom K i (weylSL2 K)) : L) : G)).toMonoidHom :
      Subgroup G) = (2 ^ n) ^ 2 := by
  have h1 := FullCenterWeyl.F_inf_Fw h i
  rw [FullCenterWeyl.w_inv] at h1
  rw [sHom_weylSL2, h1, FullCenterTorus.card_W h i, h.setup.card_K]

theorem exists_perfect_commuting_factor (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis)
    (ρ : 𝐍𝐂[i] →* SL(2, K) × SL(2, K)) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = 𝐗[i].subgroupOf 𝐍𝐂[i])
    (hswap : ∀ x y : 𝐍𝐂[i], (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap)
    (β : SL(2, K) ≃* SL(2, K))
    (hβ : ∀ (M : SL(2, K)) (hM : ((φ.symm (sHom K i M) : L) : G) ∈ 𝐍𝐂[i]),
      ρ ⟨_, hM⟩ = (β M, β M)) :
    ∃ P : Subgroup G, P ≤ prodFst ρ ∧ ⁅P, P⁆ = P ∧ P ⊔ 𝐗[i] = prodFst ρ ∧
      ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
      ∀ Q : Subgroup G, Q ≤ prodFst ρ → ⁅Q, Q⁆ = Q → Q ≤ P := by
  have hf := closureSetupFacts h hbt i
  have hrM := sup_le_NC (t := t) i (mem_sup_left (s_mem_CU h i (weylSL2 K)))
  have hPS := (BothTrivialSlice.S_inf_C h hbt).symm.le.trans inf_le_left
  have hScard := (card_barSub hf.X_le_S hf.S_le).symm
  rw [hf.card_S] at hScard
  exact Common.exists_perfect_commuting_factor_of_prodClosure (m := n) h.setup.card_K
    h.setup.two_le ρ hρ hker hf.NC_normal.1 (fun x hx => X_mul_self h hbt i hx)
    (fun x hx y hy => comm_of_mul_self (fun _ hz => X_mul_self h hbt i hz) hx hy)
    (mem_normalizer_of_conj_le fun z hz => conj_mem_NC i (t_mem_normalizer_X h i) hz)
    h.setup.t_mul_t hswap (B := (upperSL2 K).map β.toMonoidHom)
    (by rw [card_map_of_injective β.injective, card_upperSL2, h.setup.card_K])
    hf.S_le_NC hf.X_le_S
    (IsPGroup.of_card (n := 8 * n) (by rw [hScard, hf.card_X]; ring)) hScard
    (fun b hb => by
      obtain ⟨u, hu, rfl⟩ := hb
      have hsN := sup_le_NC (t := t) i (mem_sup_left (s_mem_CU h i u))
      exact ⟨⟨_, hsN⟩, hPS (symm_mem_pull.mpr (sHom_upper_le_antiUnipotent i ⟨u, hu, rfl⟩)),
        hβ u hsN⟩)
    (T_le_normalizer_S h hbt (t_mem_T h)) (X_elem h hbt i.swap) (X_sup_X_swap i) hrM
    (a := β (weylSL2 K)) (hβ (weylSL2 K) hrM) (sup_map_conj_weyl_eq_top β)
    (mem_centralizer_singleton_iff.mp (h.setup.L_le (φ.symm (sHom K i (weylSL2 K))).2)).symm
    le_sup_left
    (fun f hf' => mem_centralizer_iff.mpr fun s hs => BothTrivialHeisenberg.F_comm_S h hbt hf' hs)
    (H_le_normalizer_F h t_mem_H)
    (fun x hx => (BothTrivialHeisenberg.center_S h hbt).le (mem_center_map_iff.mpr
      ⟨hf.X_le_S hx.1, fun y hy => mem_centralizer_iff.mp hx.2 y hy⟩))
    hf.card_X (by rw [FullCenterTorus.card_F h, h.setup.card_K])
    (card_F_inf_map_conj_sHom_weylSL2 h i)

end Setting

end BothTrivialProduct

end CFSG.LocalAnalysis.EvenBN.Sp4
