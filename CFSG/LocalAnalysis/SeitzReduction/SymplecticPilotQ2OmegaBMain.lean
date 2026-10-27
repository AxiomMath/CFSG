module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OuterTwo
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaSpA
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCoresModel
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftDecomp

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (coords)

section Structure

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem mem_or_mul_mem_of_mem_centralizer_two (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    {N : ℕ} (hN : 3 ≤ N) (e : L ≃* StatedSp N K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {c : G}
    (hc : c ∈ centralizer ({t} : Set G)) : c ∈ L ∨ t * c ∈ L := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hcN : c ∈ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht hc
  obtain ⟨s, σ, hs⟩ := exists_eq_conj_mul_fieldSp hN
    (MulAut.congr e (L.normalizerMonoidHom ⟨c, hcN⟩))
  have hf1 : fieldSp N K σ = 1 := by
    rw [SeitzQ2.ringEquiv_eq_refl_of_card_eq_two hK σ]
    exact map_one (fieldSp N K)
  rw [hf1, mul_one] at hs
  set l₀ : G := ((e.symm s : L) : G) with hl₀
  have hconj : ∀ l (hl : l ∈ L), c * l * c⁻¹ = l₀ * l * l₀⁻¹ := by
    intro l hl
    have h1 : (MulAut.congr e (L.normalizerMonoidHom ⟨c, hcN⟩)) (e ⟨l, hl⟩) =
        s * e ⟨l, hl⟩ * s⁻¹ := by
      rw [hs]
      rfl
    have h2 : e (L.normalizerMonoidHom ⟨c, hcN⟩ ⟨l, hl⟩) = s * e ⟨l, hl⟩ * s⁻¹ := by
      rw [← h1]
      simp [MulAut.congr_apply]
    have h3 := congrArg (fun z => ((e.symm z : L) : G)) h2
    simp only [MulEquiv.symm_apply_apply, map_mul, map_inv, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
    rw [hl₀]
    exact h3
  have hl₀L : l₀ ∈ L := (e.symm s).2
  have hdC : l₀⁻¹ * c ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    have h1 := hconj l hl
    calc l * (l₀⁻¹ * c) = l₀⁻¹ * (l₀ * l * l₀⁻¹) * c := by group
      _ = l₀⁻¹ * (c * l * c⁻¹) * c := by rw [h1]
      _ = l₀⁻¹ * c * l := by group
  have hl₀t : l₀ * t = t * l₀ := mem_centralizer_iff.1 htC l₀ hl₀L
  have hdt : l₀⁻¹ * c ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hct : c * t = t * c := mem_centralizer_singleton_iff.1 hc
    calc l₀⁻¹ * c * t = l₀⁻¹ * (t * c) := by rw [mul_assoc, hct]
      _ = (l₀⁻¹ * t) * c := by group
      _ = (t * l₀⁻¹) * c := by
          rw [show l₀⁻¹ * t = t * l₀⁻¹ by
            calc l₀⁻¹ * t = l₀⁻¹ * (t * l₀) * l₀⁻¹ := by group
              _ = l₀⁻¹ * (l₀ * t) * l₀⁻¹ := by rw [hl₀t]
              _ = t * l₀⁻¹ := by group]
      _ = t * (l₀⁻¹ * c) := by group
  have hmem : l₀⁻¹ * c ∈ zpowers t := by
    rw [← hKt]
    exact ⟨hdC, hdt⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hk2 : t ^ (k % 2) = l₀⁻¹ * c := by
    rw [← hk]
    have h1 := zpow_mod_orderOf t k
    rw [ht] at h1
    exact_mod_cast h1
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero] at hk2
    have : c = l₀ := by
      calc c = l₀ * (l₀⁻¹ * c) := by group
        _ = l₀ := by rw [← hk2, mul_one]
    rw [this]
    exact hl₀L
  · right
    rw [h1, zpow_one] at hk2
    have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
    have : t * c = l₀ := by
      calc t * c = t * (l₀ * (l₀⁻¹ * c)) := by group
        _ = t * (l₀ * t) := by rw [← hk2]
        _ = t * (t * l₀) := by rw [hl₀t]
        _ = l₀ := by rw [← mul_assoc, htt, one_mul]
    rw [this]
    exact hl₀L

omit [Finite K] [CharP K 2] in
theorem not_mem_of_inf_eq_zpowers_two (hset : SeitzSetting G L) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) : t ∉ L :=
  LinearPilot.not_mem_of_mem_centralizer hset.center_eq_bot
    (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt)
    (fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by decide))

theorem mem_of_odd_of_mem_centralizer_two (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    {N : ℕ} (hN : 3 ≤ N) (e : L ≃* StatedSp N K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {c : G}
    (hc : c ∈ centralizer ({t} : Set G)) (hodd : Odd (orderOf c)) : c ∈ L := by
  rcases mem_or_mul_mem_of_mem_centralizer_two hset hK hN e ht hKt hc with h | h
  · exact h
  · exfalso
    have hct : Commute t c := (mem_centralizer_singleton_iff.1 hc).symm
    have h1 : (t * c) ^ orderOf c = t := by
      rw [hct.mul_pow, pow_orderOf_eq_one, mul_one]
      obtain ⟨m, hm⟩ := hodd
      rw [hm, pow_succ, pow_mul, ← ht, pow_orderOf_eq_one, one_pow, one_mul]
    exact not_mem_of_inf_eq_zpowers_two hset ht hKt (h1 ▸ pow_mem h _)

theorem card_inf_centralizer_eq_two_mul (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    {N : ℕ} (hN : 3 ≤ N) (e : L ≃* StatedSp N K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {x : G}
    (hxL : x ∈ L) :
    Nat.card (centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) =
      2 * Nat.card (L ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htL := not_mem_of_inf_eq_zpowers_two hset ht hKt
  set A : Subgroup G := centralizer ({t} : Set G) ⊓ centralizer ({x} : Set G) with hA
  set C : Subgroup G := L ⊓ centralizer ({x} : Set G) with hC
  have hCA : C ≤ A := fun y hy => ⟨mem_centralizer_singleton_iff.2
    (mem_centralizer_iff.1 htC y hy.1), hy.2⟩
  have htA : t ∈ A := ⟨mem_centralizer_singleton_iff.2 rfl,
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC x hxL).symm⟩
  have hidx : (C.subgroupOf A).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htA⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    have hbt : (b : G) * t = t * b :=
      mem_centralizer_singleton_iff.1 (mem_inf.1 b.2).1
    rcases mem_or_mul_mem_of_mem_centralizer_two hset hK hN e ht hKt (mem_inf.1 b.2).1 with
      hb | hb
    · refine Or.inr ⟨⟨hb, (mem_inf.1 b.2).2⟩, fun h => htL ?_⟩
      have := L.mul_mem (L.inv_mem hb) h.1
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨⟨by rw [hbt]; exact hb, mul_mem (mem_inf.1 b.2).2 (mem_inf.1 htA).2⟩,
        fun h => htL ?_⟩
      have := L.mul_mem hb (L.inv_mem h.1)
      rwa [mul_inv_cancel_right] at this
  have h1 := Subgroup.card_mul_index (C.subgroupOf A)
  have h2 : Nat.card (C.subgroupOf A) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv
  rw [hidx, h2] at h1
  rw [← h1, mul_comm]

theorem mem_of_odd_of_index_eq_two {X : Type*} [Group X] {H : Subgroup X} (hH : H.index = 2)
    {y : X} (hy : Odd (orderOf y)) : y ∈ H := by
  have : H.Normal := Subgroup.normal_of_index_eq_two hH
  have h2 : y ^ 2 ∈ H := hH ▸ Subgroup.pow_index_mem H y
  obtain ⟨m, hm⟩ := hy
  have h3 : y = (y ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h3]
  exact pow_mem h2 _

end Structure

section Model

variable {K : Type} [Field K]

theorem spARep_mem_complSp {N j : ℕ} {k : Fin N} (hk : 2 * j ≤ k.val) :
    spARep N j ∈ complSp K k := by
  rw [mem_complSp]
  intro x y hxy
  have hxy' : x ∈ coords k ∨ y ∈ coords k := by
    by_cases hx : x ∈ coords k
    · exact Or.inl hx
    · exact Or.inr ((by simpa using hxy : x ∉ coords k → y ∈ coords k) hx)
  have hC : ∀ a b : Fin N, (a = k ∨ b = k) →
      (spARepMat N j : Matrix (Fin N) (Fin N) K) a b = 0 := by
    intro a b hab
    simp only [spARepMat, Matrix.of_apply, ite_eq_right_iff]
    rintro ⟨-, -, ha, hb⟩
    exfalso
    rcases hab with rfl | rfl <;> omega
  rw [spARep, mat_upperUnipotentSp]
  rcases x with a | a <;> rcases y with b | b
  · rw [Matrix.fromBlocks_apply₁₁, Matrix.one_apply, Matrix.one_apply]
    simp
  · rw [Matrix.fromBlocks_apply₁₂, Matrix.one_apply_ne (by simp)]
    apply hC
    simp only [coords, Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, or_false, false_or] at hxy'
    exact hxy'
  · rw [Matrix.fromBlocks_apply₂₁, Matrix.one_apply_ne (by simp)]
    rfl
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.one_apply]
    simp

theorem nsTorusSp_le_centralizer_spARep {N j : ℕ} {k : Fin N} (hk : 2 * j ≤ k.val) :
    nsTorusSp K k ≤ centralizer ({spARep N j} : Set (StatedSp N K)) := by
  intro y hy
  rw [mem_centralizer_singleton_iff]
  exact mem_centralizer_iff.1 (complSp_le_centralizer_nsTorusSp k (spARep_mem_complSp hk))
    y hy

end Model

end CFSG.SeitzReduction.SymplecticPilot
