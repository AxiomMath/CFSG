module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialField
public import CFSG.LocalAnalysis.EvenBN.Sp4.Main
import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialSwap
import CFSG.LocalAnalysis.EvenBN.Sp4.OneAxisNormalizer
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialCases

open Subgroup CFSG.Blueprint CFSG.Open
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer BothTrivialRankOne BothTrivialSlice BothTrivialField
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped MatrixGroups

@[expose] def ProductAlternative {M : Type} [Group M] (A : Subgroup M) {k : Type} [Field k]
    (α : A ≃* SL(2, k)) (τ : M) : Prop :=
  ∃ ψ : normalClosure (A : Set M) ≃* SL(2, k) × SL(2, k),
    (∀ (a : A) (x : normalClosure (A : Set M)), (x : M) = a → ψ x = (α a, α a)) ∧
    ∀ x y : normalClosure (A : Set M), (y : M) = τ⁻¹ * x * τ → ψ y = (ψ x).swap

@[expose] def FieldAlternative {M : Type} [Group M] (A : Subgroup M) (τ : M) (n : ℕ) : Prop :=
  ∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 ∧
    ∃ ψ : normalClosure (A : Set M) ≃* SL(2, k₂),
      (∀ x y : normalClosure (A : Set M), (y : M) = τ⁻¹ * x * τ →
        ((ψ y : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
          (ψ x : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ n)) ∧
      ∀ g : SL(2, k₂),
        g ∈ (A.subgroupOf (normalClosure (A : Set M))).map ψ.toMonoidHom ↔
          ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ n = (g : Matrix (Fin 2) (Fin 2) k₂) i j

theorem xor_of_exactClosure {M : Type} [Group M] {A : Subgroup M} {k : Type} [Field k]
    {α : A ≃* SL(2, k)} {τ : M} {V : Subgroup M} {n : ℕ} (h : ExactClosure A α τ V n) :
    Xor (ProductAlternative A α τ) (FieldAlternative A τ n) :=
  h.2.2.2.2

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
set_option quotPrecheck false in
local notation "𝐊[" i "]" => barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))

theorem mul_self_mem_P (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) {y s : G}
    (hyT : y ∈ normalizer (𝐓₀ : Set G)) (hy2 : y * y = 1) (hs : s ∈ 𝐒) (hus : y * s⁻¹ ∈ 𝐂) :
    y * s⁻¹ * (y * s⁻¹) ∈ 𝐏 := by
  have hyS : y ∈ normalizer (𝐒 : Set G) := normalizer_T_le_normalizer_S h hbt hyT
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  rw [← BothTrivialSlice.S_inf_C h hbt]
  refine mem_inf.mpr ⟨?_, mul_mem hus hus⟩
  have h1 : y * s⁻¹ * y⁻¹ ∈ 𝐒 := (mem_normalizer_iff.mp hyS _).mp (inv_mem hs)
  rw [hyinv] at h1
  rw [show y * s⁻¹ * (y * s⁻¹) = y * s⁻¹ * y * s⁻¹ by group]
  exact mul_mem h1 (inv_mem hs)

omit [Finite G] in
theorem noSwap_of_even (h : FCHyp L K n φ t) (hn : Even n) :
    ∀ u ∈ 𝐂, u ∈ normalizer (𝐓₀ : Set G) →
      (∀ x ∈ 𝐔[Axis.two], u * x * u⁻¹ ∈ 𝐔[Axis.one]) → u * u ∉ 𝐏 := fun u huC _ hU huu =>
  absurd (BothTrivialSwap.odd_of_swap h.setup huC hU (pull_le φ _ huu)
    (by rw [inv_mul_cancel]; exact one_mem _)) (Nat.not_odd_iff_even.mpr hn)

theorem mem_T_of_noSwap (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (hns : ∀ u ∈ 𝐂, u ∈ normalizer (𝐓₀ : Set G) →
      (∀ x ∈ 𝐔[Axis.two], u * x * u⁻¹ ∈ 𝐔[Axis.one]) → u * u ∉ 𝐏) (i : Axis)
    {N : Subgroup (BarM 𝐗[i])} [N.Normal]
    (hNO : N ⊓ standardComponentOddCore (BarM 𝐗[i]) = ⊥)
    (hC : centralizer (N : Set (BarM 𝐗[i])) = standardComponentOddCore (BarM 𝐗[i]))
    (hcyc : IsCyclic (Outer N)) (hSN : barSub 𝐗[i] 𝐒 ≤ N)
    (hSyl : ∃ P : Sylow 2 N, (P : Subgroup N).map N.subtype = barSub 𝐗[i] 𝐒) {y : G}
    (hyT : y ∈ normalizer (𝐓₀ : Set G)) (hy2 : y * y = 1) : y ∈ 𝐓₀ := by
  obtain ⟨s, hs, hus⟩ := exists_mul_inv_mem_C h hbt hyT
  have hsT : s ∈ normalizer (𝐓₀ : Set G) := le_normalizer (S_le_T h hs)
  have huT : y * s⁻¹ ∈ normalizer (𝐓₀ : Set G) := mul_mem hyT (inv_mem hsT)
  have huQ : y * s⁻¹ ∈ normalizer (𝐐 : Set G) :=
    centralizer_inf_normalizer_le h hbt (mem_inf.mpr ⟨hus, huT⟩)
  rcases h.conj_U huQ with ⟨h1, h2⟩ | ⟨-, h2⟩
  · have huX : ∀ j : Axis, y * s⁻¹ ∈ normalizer (𝐗[j] : Set G) := fun j => by
      cases j
      · exact mem_normalizer_X_of_mem_normalizer_U h hbt Axis.one hus h1
      · exact mem_normalizer_X_of_mem_normalizer_U h hbt Axis.two hus h2
    have hyX : y ∈ normalizer (𝐗[i] : Set G) := by
      have := mul_mem (huX i) (S_le_normalizer_X h hbt i hs)
      rwa [inv_mul_cancel_right] at this
    rcases mem_or_mul_mem_of_isCyclic_outer_bar (X := 𝐗[i]) (S := 𝐒) (T := 𝐓₀) (t := t)
        (y := y) (N := N) (X_le_S i) (S_le_T h) (isPGroup_T h hbt) (t_mem_T h)
        (BothTrivialHeisenberg.t_not_mem_S h hbt) h.setup.t_mul_t (T_le_normalizer_X h hbt i)
        hyX hyT hy2 hNO hC hcyc hSN hSyl with h3 | h3
    · exact S_le_T h h3
    · have := mul_mem (S_le_T h h3) (inv_mem (t_mem_T h))
      rwa [mul_inv_cancel_right] at this
  · exact absurd (mul_self_mem_P h hbt hyT hy2 hs hus) (hns _ hus huT h2)

theorem both_trivial_field_of_noSwap [IsSimpleGroup G]
    (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis)
    {α : 𝐊[i] ≃* SL(2, K)}
    (hex : ExactClosure 𝐊[i] α (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩) (barSub 𝐗[i] 𝐒) n)
    (hF : FieldAlternative 𝐊[i] (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩) n)
    (hns : ∀ u ∈ 𝐂, u ∈ normalizer (𝐓₀ : Set G) →
      (∀ x ∈ 𝐔[Axis.two], u * x * u⁻¹ ∈ 𝐔[Axis.one]) → u * u ∉ 𝐏) : False := by
  have := BothTrivialField.isPerfect φ
  obtain ⟨hNO, hC, hSN, hSyl, -⟩ := hex
  obtain ⟨k₂, _, _, hk₂, ψ, -, -⟩ := hF
  have hcyc := isCyclic_outer_of_mulEquiv_sl2 (by have := h.setup.two_le; omega) hk₂ ψ
  have hPS : 𝐏 ≤ 𝐒 := by
    rw [← BothTrivialSlice.S_inf_C h hbt]
    exact inf_le_left
  have hQT : 𝐐 ≤ 𝐓₀ := sup_le (hPS.trans (S_le_T h)) (zpowers_le.mpr (t_mem_T h))
  obtain ⟨R, hR⟩ := exists_sylow_pull (G := G) φ
  refine false_of_slice (L := L) (P := 𝐏) (T := 𝐓₀) (S := 𝐒) h.setup.order_t h.setup.cent_le
    ⟨R, hR⟩ (isPGroup_T h hbt) hQT (S_le_T h) (inf_le_right.trans (normalizer_Q_le_T h))
    (fun g hg => ?_) (BothTrivialHeisenberg.t_not_mem_S h hbt)
    (fun W hW hTW hWN => isMulCommutative_quot (S := 𝐒) (T := 𝐓₀) h.setup
      (fun g hg => exists_mul_inv_mem_C h hbt hg) (normalizer_T_le_normalizer_S h hbt) (S_le_T h)
      hPS hQT hW hTW hWN)
  refine exists_conj_of_conj_mem_T h hbt
    (mem_T_of_noSwap h hbt hns i hNO hC hcyc hSN hSyl hg ?_)
  rw [show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, h.setup.t_mul_t]
  group

variable (G L K n φ t) in
@[expose] def ProductCase : Prop :=
  IsSimpleGroup G → CFSG.Assembly.KProper Catalog G →
    (∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥) →
    standardComponentIsStandard L →
    ∀ h : FCHyp L K n φ t, (∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) →
    ∀ (i : Axis) (α : 𝐊[i] ≃* SL(2, K)),
      ExactClosure 𝐊[i] α (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩) (barSub 𝐗[i] 𝐒) n →
      ProductAlternative 𝐊[i] α (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩) → False

variable (G L K n φ t) in
@[expose] def OddFieldNoSwap : Prop :=
  IsSimpleGroup G → CFSG.Assembly.KProper Catalog G →
    (∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥) →
    standardComponentIsStandard L →
    ∀ h : FCHyp L K n φ t, (∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) → Odd n →
    (∀ i : Axis, ∃ α : 𝐊[i] ≃* SL(2, K),
      ExactClosure 𝐊[i] α (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩) (barSub 𝐗[i] 𝐒) n ∧
        FieldAlternative 𝐊[i] (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩) n) →
    ∀ u ∈ 𝐂, u ∈ normalizer (𝐓₀ : Set G) →
      (∀ x ∈ 𝐔[Axis.two], u * x * u⁻¹ ∈ 𝐔[Axis.one]) → u * u ∉ 𝐏

end Setting

@[expose] def BothTrivialProductExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [CharP K 2] [Finite K]
    (n : ℕ) (φ : L ≃* antiSp K) (t : G), ProductCase G L K n φ t

@[expose] def BothTrivialOddFieldNoSwap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [CharP K 2] [Finite K]
    (n : ℕ) (φ : L ≃* antiSp K) (t : G), OddFieldNoSwap G L K n φ t

section Final

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

set_option quotPrecheck false in
local notation "𝐃'[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄'[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐅'" => closure {x : G | ∃ e ∈ (𝐄'[Axis.one] ⊓ 𝐄'[Axis.two] : Subgroup G),
  ∃ j ∈ pull φ (diagTorus K), x = e⁻¹ * (j⁻¹ * e * j)}

theorem false_of_both_trivial
    (hsel : GMSK.FixedRootSelector fun D _ => Catalog D)
    (hsmall : SmallSurvivorsNoElementary) (hP : BothTrivialProductExclusion)
    (hF : BothTrivialOddFieldNoSwap) [IsSimpleGroup G]
    (hKp : CFSG.Assembly.KProper Catalog G)
    (hcore : ∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥)
    (hL : standardComponentIsStandard L) (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅pull φ (rootA K i), 𝐅' ⊓ 𝐃'[i.swap]⁆ = ⊥) : False := by
  obtain ⟨α₁, -, hex₁⟩ := both_trivial_rank_one_closures_exact hsel hsmall hKp h hbt Axis.one
  obtain ⟨α₂, -, hex₂⟩ := both_trivial_rank_one_closures_exact hsel hsmall hKp h hbt Axis.two
  rcases xor_of_exactClosure hex₁ with ⟨hP₁, -⟩ | ⟨hF₁, -⟩
  · exact hP G L K n φ t inferInstance hKp hcore hL h hbt Axis.one α₁ hex₁ hP₁
  · rcases xor_of_exactClosure hex₂ with ⟨hP₂, -⟩ | ⟨hF₂, -⟩
    · exact hP G L K n φ t inferInstance hKp hcore hL h hbt Axis.two α₂ hex₂ hP₂
    · rcases Nat.even_or_odd n with hn | hn
      · exact both_trivial_field_of_noSwap h hbt Axis.one hex₁ hF₁ (noSwap_of_even h hn)
      · refine both_trivial_field_of_noSwap h hbt Axis.one hex₁ hF₁
          (hF G L K n φ t inferInstance hKp hcore hL h hbt hn fun j => ?_)
        cases j
        · exact ⟨α₁, hex₁, hF₁⟩
        · exact ⟨α₂, hex₂, hF₂⟩

end Final

theorem bothTrivialExclusion_of_cases
    (hsel : GMSK.FixedRootSelector fun D _ => Catalog D)
    (hsmall : SmallSurvivorsNoElementary) (hP : BothTrivialProductExclusion)
    (hF : BothTrivialOddFieldNoSwap) : BothTrivialExclusion := by
  intro G _ _ _ hKp hcore L hL n hn K _ _ _ hK T hT t htT ht P φ hφP TG PG Q ZP U A V B M N D E
    E₀ J₀ F Fi hfull hb1 hb2
  have hct : standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥ :=
    hcore _ ((Subgroup.orderOf_coe t).trans ht)
  obtain ⟨hO, hLn, -⟩ := standard_simple_setting hL hn hK φ T hT htT ht hct
  have hS := setup_of_standard hL hn hK φ T hT htT ht hct
  have hPG : PG = pull φ (antiUnipotent K) := by
    change (P : Subgroup L).map L.subtype = ((antiUnipotent K).comap φ.toMonoidHom).map L.subtype
    rw [← hφP, comap_map_eq_self_of_injective φ.injective]
  have hZP : ZP = pull φ (antiUnipotentCenter K) := by
    change (center ↥PG).map PG.subtype = _
    rw [hPG, center_pull_antiUnipotent]
  have hfull' : {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) :
      Set G), x = m⁻¹ * t * m} = {x | ∃ z ∈ pull φ (antiUnipotentCenter K), x = t * z} := by
    rw [← hPG, ← hZP]
    exact hfull
  obtain ⟨-, h⟩ := FCHyp.of_setup hS (hO := hO) hLn hfull'
  exact false_of_both_trivial hsel hsmall hP hF hKp hcore hL h fun i => by
    cases i
    · exact hb1
    · exact hb2

end BothTrivialCases

end CFSG.LocalAnalysis.EvenBN.Sp4
