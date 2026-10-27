module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2FusionTwoCentral
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticLagrangianAssembly

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)

section Outer

variable {r : ℕ} {K : Type} [Field K]

theorem spLinearAutGroup_le_inner [Finite K] [CharP K 2] [NeZero r] :
    SymplecticHigher.spLinearAutGroup r K ≤ inner (StatedProj (StatedSp r K)) := by
  rw [SymplecticHigher.spLinearAutGroup, Subgroup.closure_le]
  rintro _ ⟨A, rfl⟩
  obtain ⟨s, hs⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
  rw [SetLike.mem_coe, hs, SymplecticHigher.conjAut_statedSp]
  exact ⟨_, rfl⟩

theorem isCyclic_outer_statedProj [Finite K] [CharP K 2] (hr : 3 ≤ r) :
    IsCyclic (Outer (StatedProj (StatedSp r K))) := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨hE, -⟩ := SymplecticHigher.automorphism_generation (K := K) hr
  obtain ⟨-, -, -, -, ⟨g, -, hg⟩, -⟩ :=
    SymplecticHigher.standard_outer_quotient (K := K) (by omega : 1 ≤ r)
  refine ⟨⟨QuotientGroup.mk g, fun x => ?_⟩⟩
  induction x using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨k, hk⟩ := hg x (by rw [hE]; exact Subgroup.mem_top x)
    refine ⟨-k, ?_⟩
    have hin : g ^ k * x ∈ inner (StatedProj (StatedSp r K)) := spLinearAutGroup_le_inner hk
    change (QuotientGroup.mk g : Outer (StatedProj (StatedSp r K))) ^ (-k) = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, zpow_neg, inv_inv]
    exact hin

theorem isCyclic_outer_of_mulEquiv [Finite K] [CharP K 2] (hr : 3 ≤ r) {L : Type*} [Group L]
    (e : L ≃* StatedProj (StatedSp r K)) : IsCyclic (Outer L) := by
  have := isCyclic_outer_statedProj (K := K) hr
  exact isCyclic_of_surjective (equivalence e).symm (equivalence e).symm.surjective

theorem isCyclic_outer_of_mulEquiv_statedSp [Finite K] [CharP K 2] (hr : 3 ≤ r) {L : Type*}
    [Group L] (e : L ≃* StatedSp r K) : IsCyclic (Outer L) := by
  have : NeZero r := ⟨by omega⟩
  exact isCyclic_outer_of_mulEquiv hr (e.trans (F4Pilot.spProjEquiv r K))

theorem isSolvable_outer_of_isCyclic {X : Type*} [Group X] (h : IsCyclic (Outer X)) :
    Group.IsSolvable (Outer X) := by
  let := IsCyclic.commGroup (α := Outer X)
  exact Group.isSolvable_of_comm fun a b => mul_comm a b

end Outer

section Model

theorem exists_mulEquiv_statedSp_of_lieModel {L : Type} [Group L] {n f : ℕ}
    (hL : CFSG.Blueprint.LieModel L .PSp n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (L ≃* StatedSp n K) := by
  rcases hL with ⟨-, ⟨-, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
    have : NeZero n := ⟨by omega⟩
    exact ⟨K, inferInstance, inferInstance, inferInstance, hK,
      ⟨e.trans (F4Pilot.spProjEquiv n K).symm⟩⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem lieModel_of_mulEquiv_statedSp {L : Type} [Group L] {n f : ℕ} {K : Type} [Field K]
    (e : L ≃* StatedSp n K) (hK : Nat.card K = 2 ^ f) (hn : 2 ≤ n) (hnf : (n, f) ≠ (2, 1)) :
    CFSG.Blueprint.LieModel L .PSp n 2 f := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hK
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have : NeZero n := ⟨by omega⟩
  have hf := LinearPilot.one_le_of_card_eq_two_pow hK
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, hf, hn, ?_⟩, K, inferInstance, inferInstance, hK,
    ⟨e.trans (F4Pilot.spProjEquiv n K)⟩⟩
  intro h
  obtain ⟨rfl, h2⟩ := Prod.mk.inj h
  have hf1 : f = 1 := by
    by_contra hf1
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hnf (by rw [hf1])

end Model

section Kernel

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem hypothesisOne_quotient_center (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hL : CFSG.Blueprint.LieModel L .PSp n 2 f) : HypothesisOne (L ⧸ center L) :=
  CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv (quotientCenterMulEquiv hset.center_eq_bot).symm
    (hypothesisOne_of_lieModel_PSp_of_three_le hn hL)

theorem card_sylow_eq_two (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hL : CFSG.Blueprint.LieModel L .PSp n 2 f) (S : Sylow 2 (centralizer (L : Set G))) :
    Nat.card S = 2 :=
  card_sylow_eq_two_of_standard_of_center_eq_bot hset.standardSetting hset.center_eq_bot
    (hypothesisOne_quotient_center hset hn hL) S

theorem inf_centralizer_eq_zpowers (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hL : CFSG.Blueprint.LieModel L .PSp n 2 f) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
  inf_centralizer_eq_zpowers_of_standard_of_center_eq_bot hset.standardSetting
    hset.center_eq_bot (hypothesisOne_quotient_center hset hn hL) htC ht

theorem kernel (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hL : CFSG.Blueprint.LieModel L .PSp n 2 f) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (L : Set G) ∧
      (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) ∧
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
      centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      (∀ u ∈ centralizer (L : Set G), orderOf u = 2 →
        ∃ c ∈ centralizer (L : Set G), Odd (orderOf c) ∧ c * t * c⁻¹ = u) ∧
      ∀ x ∈ centralizer (L : Set G), Odd (orderOf x) → t * x * t⁻¹ = x⁻¹ :=
  F4Pilot.kernel hset.standardSetting hset.center_eq_bot
    (hypothesisOne_quotient_center hset hn hL)

end Kernel

section Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_setup (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hL : CFSG.Blueprint.LieModel L .PSp n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (L ≃* StatedSp n K) ∧ Group.IsSolvable (Outer L) ∧ IsCyclic (Outer L) ∧
        ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (L : Set G) ∧ t ∉ L ∧
          (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) ∧
          centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
          centralizer ({t} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_statedSp_of_lieModel hL
  have hcyc := isCyclic_outer_of_mulEquiv_statedSp hn e
  obtain ⟨t, ht, htC, hsyl, hKt, hCtN, -⟩ := kernel hset hn hL
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, ⟨e⟩,
    isSolvable_outer_of_isCyclic hcyc, hcyc, t, ht, htC, ?_, hsyl, hKt, hCtN⟩
  exact LinearPilot.not_mem_of_mem_centralizer hset.center_eq_bot htC fun h1 => by
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)

end Setup

section Fusion

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {r : ℕ} {K : Type} [Field K]

theorem exists_conj_eq_mul_twoCentral (hset : SeitzSetting G L) (hr : 3 ≤ r) [Finite K]
    [CharP K 2] (e : L ≃* StatedSp r K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u)
    (hAutU : ∀ (U : Sylow 2 L) (β : MulAut L), (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  have hOut : IsCyclic (Outer L) := isCyclic_outer_of_mulEquiv_statedSp hr e
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  exact LinearPilot.exists_conj_eq_mul_of_commutator_eq_top
    (SeitzQ2.commutator_eq_top_of_standardSetting hset.standardSetting) ht
    (SeitzQ2.le_centralizer_singleton_of_mem_centralizer htC) hCN hKt hnot hAutU
    (SeitzQ2.commutator_mem_of_sylow_le_centralizer_of_isCyclic_outer htC ht hCN hKt hOut)

theorem exists_conj_eq_mul_twoCentral_twoSided (hset : SeitzSetting G L) (hr : 3 ≤ r)
    [Finite K] [CharP K 2] (e : L ≃* StatedSp r K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u)
    (hAutU : ∀ (U : Sylow 2 L) (β : MulAut L), (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧ z ≠ 1 ∧
      (∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) ∧
      (∃ U' : Sylow 2 (CFSG.conjugate L x),
        ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ :=
  SeitzQ2.exists_conj_eq_mul_twoCentral_twoSided_of_isCyclic_outer hset.standardSetting
    (isCyclic_outer_of_mulEquiv_statedSp hr e) ht hKt hnot hAutU

end Fusion

theorem seitzExclusion_highPSp_of_forall
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 3 ≤ n →
        (n, f) ≠ (3, 1) → ∀ (_ : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
          centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False) :
    SeitzExclusion HighPSp := by
  rintro G _ _ L hset ⟨n, f, hn, hnf, hL⟩
  obtain ⟨K, _, _, _, hK, ⟨e⟩, -, -, t, ht, -, -, -, hKt, -⟩ := exists_setup hset hn hL
  exact h G L hset n f K hK hn hnf e t ht hKt

theorem seitzExclusion_highPSp_of_cases
    (h4 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
        3 ≤ n → ∀ (_ : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
          centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False)
    (h2 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
        ∀ (_ : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
          centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t → False) :
    SeitzExclusion HighPSp := by
  refine seitzExclusion_highPSp_of_forall fun G _ _ L hset n f K _ _ _ hK hn hnf e t ht hKt => ?_
  rcases LinearPilot.card_eq_two_or_four_le hK with ⟨rfl, hK2⟩ | ⟨hf, -⟩
  · refine h2 G L hset n K hK2 ?_ e t ht hKt
    by_contra hn4
    exact hnf (by rw [show n = 3 by omega])
  · exact h4 G L hset n f K hK hf hn e t ht hKt

end CFSG.SeitzReduction.SymplecticPilot
