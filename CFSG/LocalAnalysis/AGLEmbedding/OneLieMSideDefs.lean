module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockData
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbedding.TorusIrreducible
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section MData

variable {G : Type} [Group G] [Finite G]

structure D1OneLieMData (p : ℕ) [Fact p.Prime] (n e : ℕ) (P : Sylow p G)
    (M H R Np Z : Subgroup G) : Prop where
  ph3 : D1PhaseThree p P M H R
  ind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q
  two_le : 2 ≤ n
  e_cases : e = 1 ∨ (e = 2 ∧ 3 ≤ n)
  le_R : Z ≤ R
  torus : ∃ φ : Multiplicative (GaloisField p n) ≃* Z, ∀ μ : (GaloisField p n)ˣ,
    ∃ t ∈ H ⊓ M, ∀ a : Multiplicative (GaloisField p n),
      t * (φ a : G) * t⁻¹ =
        φ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ e * Multiplicative.toAdd a))
  plus_le : Np ≤ H ⊓ M
  plus_normal : H ≤ Subgroup.normalizer (Np : Set G)
  core_le : GLBPrimeCore p H ≤ Np
  plus_cyclic : ∀ A : Subgroup G, A ≤ Np → IsPGroup p A → IsCyclic A
  inf_plus : Z ⊓ Np = ⊥
  dichotomy : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    Z ≤ Y ∨ Y ≤ Np
  perfect_le : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ Np
  comm_le : ∀ z ∈ Z, ∀ c ∈ Np, z * c * z⁻¹ * c⁻¹ ∈ GLBPrimeCore p H
  pRank_le : Open.pRank p (H ⊓ M) ≤ (if e = 2 then n else 2 * n) + 1
  pair : n = 2 → ∃ U : Subgroup G, Z ≤ U ∧ U ≤ R ∧ ⁅U, U⁆ = Z ∧
    Z ≤ Subgroup.centralizer (U : Set G) ∧ (∀ u ∈ U, u ^ p = 1) ∧ Nat.card U = p ^ 6 ∧
    ∀ r : ℕ, r.Prime → r ∣ p ^ 4 - 1 → (∀ k : ℕ, 0 < k → k < 4 → ¬ r ∣ p ^ k - 1) →
      ∃ t : G, t ∈ H ⊓ M ∧ t ∈ Subgroup.normalizer (U : Set G) ∧
        IsPGroup r (Subgroup.zpowers t) ∧ (∀ z ∈ Z, t * z * t⁻¹ = z) ∧
        (∀ u ∈ U, t ^ r * u * (t ^ r)⁻¹ = u) ∧
        (∃ u ∈ U, t * u * t⁻¹ * u⁻¹ ∉ Z) ∧
        ∀ V : Subgroup G, Z ≤ V → V ≤ U → t ∈ Subgroup.normalizer (V : Set G) → V = Z ∨ V = U

end MData

section MDataBasic

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n e : ℕ} {P : Sylow p G}
  {M H R Np Z : Subgroup G}

theorem D1OneLieMData.isElemAbelian (h : D1OneLieMData p n e P M H R Np Z) :
    IsElemAbelian p Z := by
  obtain ⟨φ, -⟩ := h.torus
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', rfl⟩ := φ.surjective a
    obtain ⟨b', rfl⟩ := φ.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    have hap : a ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    have : (⟨x, hx⟩ : Z) ^ p = 1 := by rw [← ha, ← map_pow, hap, map_one]
    simpa using congrArg Subtype.val this

theorem D1OneLieMData.card_eq (h : D1OneLieMData p n e P M H R Np Z) : Nat.card Z = p ^ n := by
  obtain ⟨φ, -⟩ := h.torus
  have hn := h.two_le
  rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
    GaloisField.card p n (by omega)]

theorem D1OneLieMData.two_le_card (h : D1OneLieMData p n e P M H R Np Z) :
    p ^ 2 ≤ Nat.card Z := by
  rw [h.card_eq]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos h.two_le

theorem D1OneLieMData.isElemAbelian_barM' (h : D1OneLieMData p n e P M H R Np Z) :
    IsElemAbelian p (barM M Z) := by
  have hZel := h.isElemAbelian
  have : IsMulCommutative Z := hZel.1
  refine CFSG.SectionRank.isElemAbelian_map ⟨inferInstance, fun x hx => Subtype.ext ?_⟩ _
  simpa using hZel.2 x (Subgroup.mem_subgroupOf.mp hx)

theorem D1OneLieMData.card_barM' (h : D1OneLieMData p n e P M H R Np Z) :
    Nat.card (barM M Z) = Nat.card Z :=
  card_barM_of_isPGroup Fact.out h.ph3.ne_two (h.le_R.trans h.ph3.le_M)
    fun x => ⟨1, Subtype.ext (by simpa using h.isElemAbelian.2 x x.2)⟩

theorem D1OneLieMData.torus_sq (h : D1OneLieMData p n e P M H R Np Z) :
    ∃ φ : Multiplicative (GaloisField p n) ≃* Z, ∀ μ : (GaloisField p n)ˣ,
      ∃ t ∈ H ⊓ M, ∀ a : Multiplicative (GaloisField p n),
        t * (φ a : G) * t⁻¹ =
          φ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 * Multiplicative.toAdd a)) := by
  obtain ⟨φ, htor⟩ := h.torus
  refine ⟨φ, fun μ => ?_⟩
  rcases h.e_cases with he | ⟨he, -⟩
  · subst he
    obtain ⟨t, ht, hta⟩ := htor (μ ^ 2)
    exact ⟨t, ht, fun a => by simpa using hta a⟩
  · subst he
    exact htor μ

theorem D1OneLieMData.exists_irr (h : D1OneLieMData p n e P M H R Np Z) :
    ∃ (r : ℕ) (t : G), 4 ≤ r ∧ t ∈ H ⊓ M ∧ t ∈ Subgroup.normalizer (Z : Set G) ∧
      ∀ k : ℕ, ¬ r ∣ k → ∀ Y : Subgroup G, Y ≤ Z →
        t ^ k ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = Z := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ph3.ne_two
  rcases Nat.lt_or_ge n 3 with hn | hn
  ·
    obtain ⟨φ, htor⟩ := h.torus
    have hn2 : n = 2 := by have := h.two_le; omega
    have he : e = 1 := by rcases h.e_cases with he | ⟨-, he⟩ <;> omega
    subst hn2 he
    obtain ⟨t, htK, htZ, hirr⟩ := exists_torus_element_two (B := H ⊓ M)
      ⟨φ, fun μ => by simpa using htor μ⟩
    exact ⟨p + 1, t, by have := hp.two_le; omega, htK, htZ, hirr⟩
  ·
    obtain ⟨r, t, hr, hnr, hr2, hr3, -, -, htK, htZ, -, -, -, hirr⟩ :=
      exists_ppd_torus_element hp2 hn h.torus_sq
    exact ⟨r, t, by have := hr.five_le_of_ne_two_of_ne_three hr2 hr3; omega, htK, htZ, hirr⟩

theorem D1OneLieMData.cyc (h : D1OneLieMData p n e P M H R Np Z) :
    ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) → ⁅Y, Y⁆ = Y →
      ∀ A : Subgroup G, A ≤ Y → IsPGroup p A → IsCyclic A := fun Y hY hperf A hAY hA =>
  h.plus_cyclic A (hAY.trans (h.perfect_le Y (h.ph3.inf_eq_inf_normalizer_twoCore ▸ hY) hperf))
    hA

theorem D1OneLieMData.mem_normalizer_block (h : D1OneLieMData p n e P M H R Np Z)
    (hB3 : StmtBlockThree) (hp5 : 5 ≤ p) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) {t : G}
    (htK : t ∈ H ⊓ M) (htr : IsPGroup r (Subgroup.zpowers t)) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : t ∈ Subgroup.normalizer (L : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  by_contra htL
  have hle := h.ph3.le_pRank_three_of_not_mem_normalizer' stmtComponentRank stmtBarPRankLift
    (fun L' hL' => hB3 h.ph3 hL') htK htr hL htL
  exact h.ph3.false_of_four_le_pRank' h.ind Nat.prime_three (by decide) (by omega) (by omega)

end MDataBasic

@[expose] def StmtOneLieCompThree : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n e : ℕ} {P : Sylow p G}
    {M H R Np Z : Subgroup G}, KFactThreeOrFiveDvd → KFactOutElemRankOdd → StmtBlockThree →
    D1OneLieMData p n e P M H R Np Z → p = 3 →
    ∀ L : Subgroup G, IsTwoPrimeComponent M L → L ≤ GLBPrimeCore p H →
      barM M Z ≤ Subgroup.centralizer (barM M L : Set _)

@[expose] def StmtOneLieBlocksThree : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n e : ℕ} {P : Sylow p G}
    {M H R Np Z : Subgroup G}, StmtLemmaBRelCyc → StmtBlockThree → Asc81bEightFour →
    Asc81bEightFive → Asc81bEightSix → D1NoXBlock → D1OneLieMData p n e P M H R Np Z → p = 3 →
    pCorePreimage p M ⊓ Z = ⊥ →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M Z ≤ Subgroup.centralizer (barM M L : Set _)

@[expose] def StmtOneLieMData : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}, KFactOneLie → KFactOneLieTorus →
    D1OneLieData p P M H R Rbar K →
    ∃ n e : ℕ, D1OneLieMData p n e P M H R (d1PlusCore p H K)
      (d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))

end CFSG.AGLEmbedding
