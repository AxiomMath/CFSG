module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotKernel
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamilies
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinear
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearSchreier

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL conjAut fieldAut dualAut)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)

section Field

theorem finite_of_card_eq_two_pow {α : Type*} {f : ℕ} (hK : Nat.card α = 2 ^ f) : Finite α :=
  Nat.finite_of_card_ne_zero (by rw [hK]; positivity)

theorem four_le_card_iff_two_le {α : Type*} {f : ℕ} (hK : Nat.card α = 2 ^ f) :
    4 ≤ Nat.card α ↔ 2 ≤ f := by
  rw [hK]
  constructor
  · intro h
    by_contra hf
    interval_cases f <;> norm_num at h
  · intro h
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h

variable {K : Type*} [Field K] {f : ℕ}

theorem one_le_of_card_eq_two_pow (hK : Nat.card K = 2 ^ f) : 1 ≤ f := by
  have := finite_of_card_eq_two_pow hK
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · have h1 := Finite.one_lt_card (α := K)
    rw [hK, pow_zero] at h1
    exact absurd h1 (lt_irrefl 1)
  · exact hf

theorem charP_two_of_card_eq_two_pow (hK : Nat.card K = 2 ^ f) : CharP K 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
    (one_le_of_card_eq_two_pow hK) hK

theorem card_eq_two_or_four_le (hK : Nat.card K = 2 ^ f) :
    (f = 1 ∧ Nat.card K = 2) ∨ (2 ≤ f ∧ 4 ≤ Nat.card K) := by
  rcases (show f = 1 ∨ 2 ≤ f by have := one_le_of_card_eq_two_pow hK; omega) with rfl | hf
  · exact Or.inl ⟨rfl, by rw [hK, pow_one]⟩
  · exact Or.inr ⟨hf, (four_le_card_iff_two_le hK).2 hf⟩

end Field

section Parameters

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem ne_four_one (hset : SeitzSetting G L) {n f : ℕ}
    (hL : CFSG.Blueprint.LieModel L .PSL n 2 f) : (n, f) ≠ (4, 1) := by
  intro h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  exact hset.not_exception (Or.inr (Or.inr (Or.inl hL)))

open CFSG.LocalAnalysis.ComponentInitial in
theorem ne_four_one_of_mulEquiv (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K]
    (e : L ≃* projectiveSL n K) (hK : Nat.card K = 2 ^ f) : (n, f) ≠ (4, 1) := by
  intro h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  have := finite_of_card_eq_two_pow hK
  have e' : L ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 4 K) :=
    e.trans ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 K).symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K))
  have hL : CFSG.Blueprint.LieModel L .PSL 4 2 1 :=
    Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, K,
      inferInstance, inferInstance, hK, ⟨e'⟩⟩
  exact ne_four_one hset hL rfl

end Parameters

theorem isSolvable_outer_of_mulEquiv {X : Type*} [Group X] {n : ℕ} {K : Type*} [Field K]
    [Finite K] (hn : 3 ≤ n) (e : X ≃* projectiveSL n K) : Group.IsSolvable (Outer X) := by
  have := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.linear_higher_schreier
    (K := K) hn).2
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm

section Kernel

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem hypothesisOne_quotient_center (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K]
    (e : L ≃* projectiveSL n K) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) :
    HypothesisOne (L ⧸ center L) :=
  hypothesisOne_of_mulEquiv (e.symm.trans (quotientCenterMulEquiv hset.center_eq_bot).symm)
    (hypothesisOne_projectiveSL hn hK fun h =>
      ne_four_one_of_mulEquiv hset e hK (by rw [h.1, h.2]))

theorem card_sylow_eq_two (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K]
    (e : L ≃* projectiveSL n K) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 :=
  card_sylow_eq_two_of_standard_of_center_eq_bot hset.standardSetting hset.center_eq_bot
    (hypothesisOne_quotient_center hset e hK hn) S

theorem inf_centralizer_eq_zpowers (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K]
    (e : L ≃* projectiveSL n K) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
  inf_centralizer_eq_zpowers_of_standard_of_center_eq_bot hset.standardSetting
    hset.center_eq_bot (hypothesisOne_quotient_center hset e hK hn) htC ht

theorem kernel (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K]
    (e : L ≃* projectiveSL n K) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (L : Set G) ∧
      (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) ∧
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
      centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      (∀ u ∈ centralizer (L : Set G), orderOf u = 2 →
        ∃ c ∈ centralizer (L : Set G), Odd (orderOf c) ∧ c * t * c⁻¹ = u) ∧
      ∀ x ∈ centralizer (L : Set G), Odd (orderOf x) → t * x * t⁻¹ = x⁻¹ :=
  F4Pilot.kernel hset.standardSetting hset.center_eq_bot
    (hypothesisOne_quotient_center hset e hK hn)

end Kernel

section Involution

variable {G : Type*} [Group G] {L : Subgroup G}

theorem mem_centralizer_of_inf_eq_zpowers {t : G}
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    t ∈ centralizer (L : Set G) :=
  (show t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) from hKt ▸ mem_zpowers t).1

theorem not_mem_of_mem_centralizer (hZ : center L = ⊥) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : t ≠ 1) : t ∉ L := by
  intro htL
  have hz : (⟨t, htL⟩ : L) ∈ center L :=
    mem_center_iff.2 fun l => Subtype.ext (mem_centralizer_iff.1 htC l l.2)
  rw [hZ, mem_bot] at hz
  exact ht (congrArg Subtype.val hz)

theorem inf_zpowers_eq_bot (hZ : center L = ⊥) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) : L ⊓ zpowers t = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxt⟩
  rcases F4Pilot.eq_one_or_eq_of_mem_zpowers ht hxt with rfl | rfl
  · exact one_mem _
  · exact absurd hxL (not_mem_of_mem_centralizer hZ htC fun h1 => by
      rw [h1, orderOf_one] at ht
      exact absurd ht (by decide))

end Involution

section ZStar

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_ne_commute (hset : SeitzSetting G L) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ g : G, g⁻¹ * t * g ≠ t ∧ (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) ∧
      g⁻¹ * t * g ∈ normalizer (L : Set G) ∧ g⁻¹ * t * g ∉ centralizer (L : Set G) :=
  F4Pilot.exists_conj_mem_normalizer_not_mem_centralizer hset.standardSetting
    (mem_centralizer_of_inf_eq_zpowers hKt) ht hKt

end ZStar

section Automizer

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]

@[expose] noncomputable def normalizerAut (e : L ≃* projectiveSL n K) :
    normalizer (L : Set G) →* MulAut (projectiveSL n K) :=
  (MulAut.congr e).toMonoidHom.comp L.normalizerMonoidHom

theorem coe_symm_normalizerAut_apply (e : L ≃* projectiveSL n K) (x : normalizer (L : Set G))
    (l : L) : ((e.symm (normalizerAut e x (e l)) : L) : G) = x * l * x⁻¹ := by
  simp [normalizerAut, MulAut.congr_apply]

theorem ker_normalizerAut (e : L ≃* projectiveSL n K) :
    (normalizerAut e).ker = (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) := by
  rw [← normalizerMonoidHom_ker]
  ext x
  simp only [MonoidHom.mem_ker, normalizerAut, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

theorem normalizerAut_eq_one_of_mem_centralizer (e : L ≃* projectiveSL n K) {x : G}
    (hx : x ∈ centralizer (L : Set G)) :
    normalizerAut e ⟨x, centralizer_le_normalizer L hx⟩ = 1 := by
  rw [← MonoidHom.mem_ker, ker_normalizerAut, mem_subgroupOf]
  exact hx

theorem normalizerAut_coe (e : L ≃* projectiveSL n K) (l : L) :
    normalizerAut e ⟨l, le_normalizer l.2⟩ = MulAut.conj (e l) := by
  ext y
  obtain ⟨m, rfl⟩ := e.surjective y
  rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  simp only [normalizerAut, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  congr 1

theorem ker_normalizerAut_comp_inclusion (e : L ≃* projectiveSL n K) {t : G}
    (hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ((normalizerAut e).comp (inclusion hCtN)).ker =
      (zpowers t).subgroupOf (centralizer ({t} : Set G)) := by
  ext x
  have hker := congrArg (fun A : Subgroup (normalizer (L : Set G)) => inclusion hCtN x ∈ A)
    (ker_normalizerAut e)
  simp only [MonoidHom.mem_ker] at hker
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hker, mem_subgroupOf, mem_subgroupOf, ← hKt,
    mem_inf, coe_inclusion]
  exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩

theorem exists_normalizerAut_eq [Finite K] (hn : 3 ≤ n) (e : L ≃* projectiveSL n K)
    (x : normalizer (L : Set G)) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
      normalizerAut e x = conjAut n K A * fieldAut n K σ * dualAut n K ^ ε :=
  (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation hn).2 _

end Automizer

section Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_setup (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n)
    (hL : CFSG.Blueprint.LieModel L .PSL n 2 f) :
    (n, f) ≠ (4, 1) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
        Nonempty (L ≃* projectiveSL n K) ∧ Group.IsSolvable (Outer L) ∧
          ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (L : Set G) ∧ t ∉ L ∧
            (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) ∧
            centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
            centralizer ({t} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have := charP_two_of_card_eq_two_pow hK
  obtain ⟨t, ht, htC, hsyl, hKt, hCtN, -⟩ := kernel hset e hK hn
  refine ⟨ne_four_one hset hL, K, inferInstance, inferInstance, inferInstance, hK, ⟨e⟩,
    isSolvable_outer_of_mulEquiv (by omega) e, t, ht, htC, ?_, hsyl, hKt, hCtN⟩
  exact not_mem_of_mem_centralizer hset.center_eq_bot htC fun h1 => by
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)

end Setup

theorem seitzExclusion_highPSL_of_forall
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 4 ≤ n →
        (n, f) ≠ (4, 1) → ∀ (_ : L ≃* projectiveSL n K) (t : G), orderOf t = 2 →
          centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False) :
    SeitzExclusion HighPSL := by
  rintro G _ _ L hset ⟨n, f, hn, -, hL⟩
  obtain ⟨hnf, K, _, _, _, hK, ⟨e⟩, -, t, ht, -, -, -, hKt, -⟩ := exists_setup hset hn hL
  exact h G L hset n f K hK hn hnf e t ht hKt

theorem seitzExclusion_highPSL_of_cases
    (h4 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
        4 ≤ n → ∀ (_ : L ≃* projectiveSL n K) (t : G), orderOf t = 2 →
          centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False)
    (h2 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 5 ≤ n →
        ∀ (_ : L ≃* projectiveSL n K) (t : G), orderOf t = 2 →
          centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False) :
    SeitzExclusion HighPSL := by
  refine seitzExclusion_highPSL_of_forall fun G _ _ L hset n f K _ _ _ hK hn hnf e t ht hKt => ?_
  rcases card_eq_two_or_four_le hK with ⟨rfl, hK2⟩ | ⟨hf, -⟩
  · refine h2 G L hset n K hK2 ?_ e t ht hKt
    by_contra hn5
    exact hnf (by rw [show n = 4 by omega])
  · exact h4 G L hset n f K hK hf hn e t ht hKt

end CFSG.SeitzReduction.LinearPilot
