module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialClosures
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialClosuresLift
import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
public import Certificates.Certificate117

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialRankOne

open Subgroup CFSG.Blueprint
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.ComponentClassification.UnbalancedCatalog
open scoped MatrixGroups

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem weyl_two_conj_uElt (b : K) :
    weylElt K Axis.two * uElt 0 b 0 0 * weylElt K Axis.two = uElt b 0 0 0 := by
  apply antiSp_ext
  change glMat (weylElt K Axis.two : GL (Fin 4) K) * glMat (uElt 0 b 0 0 : GL (Fin 4) K) *
    glMat (weylElt K Axis.two : GL (Fin 4) K) = _
  rw [glMat_weylElt, glMat_uElt, glMat_uElt]
  ext k l
  fin_cases k <;> fin_cases l <;> simp [weylMat, uMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem weyl_one_conj_uElt (c : K) :
    weylElt K Axis.one * uElt 0 0 c 0 * weylElt K Axis.one = uElt 0 0 0 c := by
  apply antiSp_ext
  change glMat (weylElt K Axis.one : GL (Fin 4) K) * glMat (uElt 0 0 c 0 : GL (Fin 4) K) *
    glMat (weylElt K Axis.one : GL (Fin 4) K) = _
  rw [glMat_weylElt, glMat_uElt, glMat_uElt]
  ext k l
  fin_cases k <;> fin_cases l <;> simp [weylMat, uMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem weyl_conj_rootU_mem_rootC (i : Axis) {u : antiSp K} (hu : u ∈ rootU K i) :
    weylElt K i.swap * u * weylElt K i.swap ∈ rootC K i := by
  cases i
  · obtain ⟨b, rfl⟩ := hu
    change weylElt K Axis.two * uElt 0 b 0 0 * weylElt K Axis.two ∈ rootC K Axis.one
    rw [weyl_two_conj_uElt, rootC, mem_centralizer_iff]
    rintro _ ⟨b', rfl⟩
    rw [uElt_mul, uElt_mul]
    congr 1 <;> ring
  · obtain ⟨c, rfl⟩ := hu
    change weylElt K Axis.one * uElt 0 0 c 0 * weylElt K Axis.one ∈ rootC K Axis.two
    rw [weyl_one_conj_uElt, rootC, mem_centralizer_iff]
    rintro _ ⟨c', rfl⟩
    rw [uElt_mul, uElt_mul]
    congr 1 <;> ring

theorem eq_one_of_weyl_conj_rootU_mem_rootA (i : Axis) {u : antiSp K} (hu : u ∈ rootU K i)
    (hA : weylElt K i.swap * u * weylElt K i.swap ∈ rootA K i) : u = 1 := by
  cases i
  · obtain ⟨b, rfl⟩ := hu
    change weylElt K Axis.two * uElt 0 b 0 0 * weylElt K Axis.two ∈ radA1 K at hA
    rw [weyl_two_conj_uElt] at hA
    obtain ⟨b', c', d', e⟩ := hA
    have hb := (uElt_inj e).1
    rw [hb, uElt_zero_eq_one]
  · obtain ⟨c, rfl⟩ := hu
    change weylElt K Axis.one * uElt 0 0 c 0 * weylElt K Axis.one ∈ radA2 K at hA
    rw [weyl_one_conj_uElt] at hA
    obtain ⟨a', b', c', e⟩ := hA
    have hc := (uElt_inj e).2.2.2
    rw [hc, uElt_zero_eq_one]

end Model

section Generic

variable {G : Type} [Group G]

theorem barMap_comm_mem_barSub {X Y : Subgroup G} {m v t' : ↥(normalizer (X : Set G))}
    (hbm : barMap X m = barMap X v) (hz : ((v⁻¹ * (t'⁻¹ * v * t') : ↥(normalizer (X : Set G))) :
      G) ∈ Y) :
    (barMap X m)⁻¹ * ((barMap X t')⁻¹ * barMap X m * barMap X t') ∈ barSub X Y := by
  refine ⟨_, mem_subgroupOf.mpr hz, ?_⟩
  rw [hbm, map_mul, map_mul, map_mul, map_inv, map_inv]

theorem barMap_comm_eq_one_iff {X : Subgroup G} {m t' : ↥(normalizer (X : Set G))} :
    (barMap X m)⁻¹ * ((barMap X t')⁻¹ * barMap X m * barMap X t') = 1 ↔
      ((m⁻¹ * (t'⁻¹ * m * t') : ↥(normalizer (X : Set G))) : G) ∈ X := by
  rw [← barMap_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv]

theorem barSub_eq_normalClosure {X Y N : Subgroup G} (hY : Y ≤ normalizer (X : Set G))
    (hNn : (N.subgroupOf (normalizer (X : Set G))).Normal)
    (hN : N = closure {x : G | ∃ g ∈ normalizer (X : Set G), ∃ y ∈ Y ⊔ X, x = g⁻¹ * y * g}) :
    barSub X N = normalClosure (barSub X Y : Set (BarM X)) := by
  refine le_antisymm (barSub_le_normalClosure hY hN.le) ?_
  have : (barSub X N).Normal := hNn.map _ (QuotientGroup.mk'_surjective _)
  refine normalClosure_le_normal ?_
  rintro _ ⟨m, hm, rfl⟩
  refine ⟨m, mem_subgroupOf.mpr ?_, rfl⟩
  rw [hN]
  exact Subgroup.subset_closure ⟨1, one_mem _, m, mem_sup_left (mem_subgroupOf.mp hm), by group⟩

end Generic

section Commutator

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
local notation "𝐉" => pull φ (diagTorus K)
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐖'[" i "]" =>
  (𝐖[i].map (MulAut.conj 𝐰[Axis.swap i]⁻¹).toMonoidHom : Subgroup G)

omit [Finite G] [Finite K] [CharP K 2] in
theorem conj_w_eq (i : Axis) {u : G} (hu : u ∈ L) :
    𝐰[i.swap]⁻¹ * u * 𝐰[i.swap] =
      ((φ.symm (weylElt K i.swap * φ ⟨u, hu⟩ * weylElt K i.swap) : L) : G) := by
  rw [w_inv, map_mul, map_mul, MulEquiv.symm_apply_apply, coe_mul, coe_mul]

omit [Finite G] [Finite K] in
theorem conj_U_mem_CU (i : Axis) {u : G} (hu : u ∈ 𝐔[i]) :
    𝐰[i.swap]⁻¹ * u * 𝐰[i.swap] ∈ L ⊓ centralizer (𝐔[i] : Set G) := by
  obtain ⟨huL, hu'⟩ := mem_pull.mp hu
  rw [CU_eq, conj_w_eq i huL, symm_mem_pull]
  exact weyl_conj_rootU_mem_rootC i hu'

omit [Finite G] [Finite K] in
theorem eq_one_of_conj_U_mem_A (i : Axis) {u : G} (hu : u ∈ 𝐔[i])
    (hA : 𝐰[i.swap]⁻¹ * u * 𝐰[i.swap] ∈ 𝐀[i]) : u = 1 := by
  obtain ⟨huL, hu'⟩ := mem_pull.mp hu
  rw [conj_w_eq i huL, symm_mem_pull] at hA
  have h1 := eq_one_of_weyl_conj_rootU_mem_rootA i hu' hA
  have h2 : (⟨u, huL⟩ : L) = 1 := by
    rw [← φ.map_eq_one_iff]
    exact h1
  exact congrArg Subtype.val h2

omit [Finite G] [Finite K] in
theorem comm_W'_eq (h : FCHyp L K n φ t) (i : Axis) (w : G) :
    (𝐰[i.swap]⁻¹ * w * 𝐰[i.swap])⁻¹ * (t⁻¹ * (𝐰[i.swap]⁻¹ * w * 𝐰[i.swap]) * t) =
      𝐰[i.swap]⁻¹ * (t⁻¹ * (w⁻¹ * t * w))⁻¹ * 𝐰[i.swap] := by
  have hwt : 𝐰[i.swap] * t = t * 𝐰[i.swap] :=
    mem_centralizer_singleton_iff.mp (h.setup.L_le (w_mem_L i.swap))
  have hwt' : t⁻¹ * 𝐰[i.swap]⁻¹ = 𝐰[i.swap]⁻¹ * t⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hwt]
  calc (𝐰[i.swap]⁻¹ * w * 𝐰[i.swap])⁻¹ * (t⁻¹ * (𝐰[i.swap]⁻¹ * w * 𝐰[i.swap]) * t)
      = 𝐰[i.swap]⁻¹ * w⁻¹ * 𝐰[i.swap] * ((t⁻¹ * 𝐰[i.swap]⁻¹) * w * (𝐰[i.swap] * t)) := by
        group
    _ = 𝐰[i.swap]⁻¹ * w⁻¹ * 𝐰[i.swap] * ((𝐰[i.swap]⁻¹ * t⁻¹) * w * (t * 𝐰[i.swap])) := by
        rw [hwt', hwt]
    _ = 𝐰[i.swap]⁻¹ * (t⁻¹ * (w⁻¹ * t * w))⁻¹ * 𝐰[i.swap] := by group

theorem commutator_tau_le_K (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) :
    closure {x | ∃ v ∈ barSub 𝐗[i] 𝐒, x = v⁻¹ *
      ((barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩)⁻¹ * v * barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩)}
      ≤ barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) := by
  rw [closure_le]
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  obtain ⟨x, hx, v, hv, hmxv⟩ := exists_X_mul_W' h hbt i (mem_subgroupOf.mp hm)
  have hvN : v ∈ normalizer (𝐗[i] : Set G) :=
    S_le_normalizer_X h hbt i (X_le_S i.swap (W'_le_X i hv))
  have hxN : x ∈ normalizer (𝐗[i] : Set G) := le_normalizer hx
  have hm' : m = ⟨x, hxN⟩ * ⟨v, hvN⟩ := Subtype.ext hmxv
  have hbm : barMap 𝐗[i] m = barMap 𝐗[i] ⟨v, hvN⟩ := by
    rw [hm', map_mul, barMap_eq_one_iff.mpr hx, one_mul]
  obtain ⟨w, hw, rfl⟩ := hv
  have hconj : (MulAut.conj 𝐰[i.swap]⁻¹).toMonoidHom w = 𝐰[i.swap]⁻¹ * w * 𝐰[i.swap] := by
    simp
  have hκ : t⁻¹ * (w⁻¹ * t * w) ∈ 𝐔[i] := kappa_mem_U h i (mem_inf.mp (W_le_Fi h i hw)).2
  have hmem := conj_U_mem_CU i (inv_mem hκ)
  rw [← comm_W'_eq h i w, ← hconj] at hmem
  exact barMap_comm_mem_barSub hbm hmem

theorem commutator_tau_ne_bot (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) :
    closure {x | ∃ v ∈ barSub 𝐗[i] 𝐒, x = v⁻¹ *
      ((barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩)⁻¹ * v * barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩)}
      ≠ ⊥ := by
  intro hbot
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ 𝐔[i], u ≠ 1 := by
    have hc : 1 < Nat.card 𝐔[i] := by rw [FCHyp.card_U]; have := h.four_le_card; omega
    obtain ⟨⟨u, hu⟩, hu1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp ((Subgroup.one_lt_card_iff_ne_bot _).mp hc)
    exact ⟨u, hu, fun e => hu1 (Subtype.ext e)⟩
  obtain ⟨w, hw, hwu⟩ := exists_kappa_eq_W h i (inv_mem hu)
  set v : G := (MulAut.conj 𝐰[i.swap]⁻¹).toMonoidHom w with hv
  have hvW : v ∈ 𝐖'[i] := ⟨w, hw, rfl⟩
  have hvS : v ∈ 𝐒 := X_le_S i.swap (W'_le_X i hvW)
  have hvN : v ∈ normalizer (𝐗[i] : Set G) := S_le_normalizer_X h hbt i hvS
  have hgen := Subgroup.subset_closure (k := {x | ∃ v ∈ barSub 𝐗[i] 𝐒, x = v⁻¹ *
      ((barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩)⁻¹ * v * barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩)})
    ⟨barMap 𝐗[i] ⟨v, hvN⟩, ⟨⟨v, hvN⟩, mem_subgroupOf.mpr hvS, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, hbot, mem_bot] at hgen
  have hX := barMap_comm_eq_one_iff.mp hgen
  have hconj : v = 𝐰[i.swap]⁻¹ * w * 𝐰[i.swap] := by simp [hv]
  have e : (((⟨v, hvN⟩ : ↥(normalizer (𝐗[i] : Set G)))⁻¹ * (⟨t, t_mem_normalizer_X h i⟩⁻¹ *
      ⟨v, hvN⟩ * ⟨t, t_mem_normalizer_X h i⟩) : ↥(normalizer (𝐗[i] : Set G))) : G) =
      𝐰[i.swap]⁻¹ * u * 𝐰[i.swap] := by
    rw [coe_mul, coe_inv, coe_mul, coe_mul, coe_inv]
    change v⁻¹ * (t⁻¹ * v * t) = _
    rw [hconj, comm_W'_eq h i w, hwu, inv_inv]
  rw [e] at hX
  have hC : 𝐰[i.swap]⁻¹ * u * 𝐰[i.swap] ∈ centralizer ({t} : Set G) :=
    h.setup.L_le (mul_mem (mul_mem (inv_mem (w_mem_L _)) (pull_le φ _ hu)) (w_mem_L _))
  have hA : 𝐰[i.swap]⁻¹ * u * 𝐰[i.swap] ∈ 𝐀[i] := by
    rw [← X_inf_C h i]
    exact ⟨hX, hC⟩
  exact hu1 (eq_one_of_conj_U_mem_A i hu hA)

theorem perfect_and_centralizes (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) :
    Group.IsPerfect (normalClosure (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) :
      Set (BarM 𝐗[i]))) ∧
      ∀ A : Subgroup (BarM 𝐗[i]), A.Normal → Odd (Nat.card A) →
        ⁅A, normalClosure (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) : Set (BarM 𝐗[i]))⁆ =
          ⊥ := by
  have hf := closureSetupFacts h hbt i
  have := hf.simple_K
  have := hf.elem_S
  obtain ⟨e, -⟩ := hf.equiv_K
  have hnab : ∃ x y : ↥(barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := GMSK.sl2_exists_mul_ne (K := K)
    exact ⟨e x, e y, fun h' => hxy (e.injective (by rw [map_mul, map_mul, h']))⟩
  obtain ⟨hperf, hcent, -⟩ :=
    ComponentInitial.elementary_involution_commutator_centralizes_odd_normal_core
      hf.orderOf_tau hnab hf.K_le hf.K_normal hf.tau_S (commutator_tau_ne_bot h hbt i)
      (commutator_tau_le_K h hbt i) rfl
  exact ⟨hperf, hcent⟩

theorem barSub_NC_eq (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) :
    barSub 𝐗[i] (closure {x : G | ∃ g ∈ normalizer (𝐗[i] : Set G),
      ∃ y ∈ (L ⊓ centralizer (𝐔[i] : Set G) : Subgroup G) ⊔ 𝐗[i], x = g⁻¹ * y * g}) =
      normalClosure (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) : Set (BarM 𝐗[i])) := by
  have hf := closureSetupFacts h hbt i
  have hCU := hf.CU_le
  have hNn := hf.NC_normal.2.2
  exact barSub_eq_normalClosure hCU hNn rfl

theorem both_trivial_rank_one_closures_exact
    (hsel : GMSK.FixedRootSelector fun D _ => Catalog D)
    (hsmall : SmallSurvivorsNoElementary) [IsSimpleGroup G]
    (hKp : CFSG.Assembly.KProper Catalog G) (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) :
    ∃ α : ↥(barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))) ≃* SL(2, K),
      (∀ (M : SL(2, K)) (m : ↥(normalizer (𝐗[i] : Set G))),
        (m : G) = ((φ.symm (sHom K i M) : L) : G) →
          ((α.symm M : ↥(barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)))) : BarM 𝐗[i]) =
            barMap 𝐗[i] m) ∧
      ExactClosure (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))) α
        (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩) (barSub 𝐗[i] 𝐒) n := by
  obtain ⟨α, hα, hcs⟩ := both_trivial_rank_one_closures hsel hsmall hKp h hbt i
  refine ⟨α, hα, ?_⟩
  have hf := closureSetupFacts h hbt i
  let _ : Fintype K := Fintype.ofFinite K
  have hk : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, h.setup.card_K]
  obtain ⟨hperf, hcent⟩ := perfect_and_centralizes h hbt i
  have hNC := hf.S_le_NC
  have hCU := hf.CU_le
  have hVA := barSub_le_normalClosure hCU hNC
  exact exactClosure_of_selection h.setup.two_le hk α hcs hperf
    (hcent _ inferInstance (GMSK.odd_card_standardComponentOddCore _)) hf.card_S hVA

end Commutator

end BothTrivialRankOne

end CFSG.LocalAnalysis.EvenBN.Sp4
