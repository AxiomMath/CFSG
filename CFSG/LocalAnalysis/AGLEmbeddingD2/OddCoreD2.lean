module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairTools
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreScalar
import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

theorem barM_conj_pow_eq_pow {G : Type} [Group G] {M X : Subgroup G} {t : G} (htM : t ∈ M)
    {m lam : ℕ} (hscal : ∀ x ∈ X, t ^ m * x * (t ^ m)⁻¹ = x ^ lam)
    (x : ↥M ⧸ CFSG.pCore 2 ↥M) (hx : x ∈ barM M X) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ^ m * x *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ^ m)⁻¹ = x ^ lam := by
  obtain ⟨y, hy, rfl⟩ := hx
  have heq : (⟨t, htM⟩ : M) ^ m * y * ((⟨t, htM⟩ : M) ^ m)⁻¹ = y ^ lam :=
    Subtype.ext (hscal _ (Subgroup.mem_subgroupOf.mp hy))
  rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, heq, map_pow]

namespace D2L2Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {M H R X : Subgroup G}

theorem eq_of_mk_eq (h : D2L2Data p M H R X) {x y : ↥M} (hx : (x : G) ∈ X) (hy : (y : G) ∈ X)
    (hxy : QuotientGroup.mk' (CFSG.pCore 2 ↥M) x = QuotientGroup.mk' (CFSG.pCore 2 ↥M) y) :
    x = y := by
  have hXM : X ≤ M := h.eq_R.le.trans h.pair.le_M
  let f : X → barM M X := fun x =>
    ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hXM x.2⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)⟩
  have hfs : Function.Surjective f := by
    rintro ⟨_, z, hz, rfl⟩
    exact ⟨⟨z, Subgroup.mem_subgroupOf.mp hz⟩, rfl⟩
  have hfb : Function.Bijective f :=
    hfs.bijective_of_nat_card_le (by rw [h.card_eq, h.card_barM])
  have h1 := hfb.1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext hxy)
  exact Subtype.ext (congrArg (fun z : X => (z : G)) h1)

theorem pow_notMem_normalizer_barM (h : D2L2Data p M H R X) {t : G} (htM : t ∈ M)
    (htX : t ∈ Subgroup.normalizer (X : Set G)) {m : ℕ}
    (horb : ∀ k, 0 < k → k < m → ∀ Y₀ : Subgroup G, Y₀ ≤ X → Nat.card Y₀ = p →
      t ^ k ∉ Subgroup.normalizer (Y₀ : Set G))
    {k : ℕ} (hk0 : 0 < k) (hkm : k < m) {Y₀ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hY₀ : Y₀ ≤ barM M X) (hcard : Nat.card Y₀ = p) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ^ k ∉ Subgroup.normalizer (Y₀ : Set _) := by
  intro hgY₀
  have hXM : X ≤ M := h.eq_R.le.trans h.pair.le_M
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have htk : mk ⟨t, htM⟩ ^ k = mk ⟨t ^ k, M.pow_mem htM k⟩ := by
    rw [← map_pow]
    rfl
  rw [htk] at hgY₀
  set Y₁ : Subgroup G := X ⊓ (Y₀.comap mk).map M.subtype with hY₁
  have hgY₁ : t ^ k ∈ Subgroup.normalizer (Y₁ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.pow_mem _ htX k,
      Subgroup.le_normalizer_map M.subtype
        (Subgroup.mem_map_of_mem _ (Subgroup.le_normalizer_comap mk hgY₀))⟩
  have hmem : ∀ (x : G) (hx : x ∈ X), x ∈ Y₁ ↔ mk ⟨x, hXM hx⟩ ∈ Y₀ := by
    intro x hx
    refine ⟨fun h => ?_, fun h => ⟨hx, ⟨x, hXM hx⟩, h, rfl⟩⟩
    obtain ⟨m, hm, hmx⟩ := h.2
    have : m = ⟨x, hXM hx⟩ := Subtype.ext hmx
    rw [← this]
    exact hm
  have hcard₁ : Nat.card Y₁ = p := by
    rw [← hcard]
    refine Nat.card_eq_of_bijective
      (fun y => ⟨mk ⟨y, hXM y.2.1⟩, (hmem y y.2.1).mp y.2⟩) ⟨fun y y' hyy' => ?_, ?_⟩
    · have h1 : mk ⟨(y : G), hXM y.2.1⟩ = mk ⟨(y' : G), hXM y'.2.1⟩ := congrArg Subtype.val hyy'
      exact Subtype.ext (congrArg (fun z : ↥M => (z : G)) (h.eq_of_mk_eq y.2.1 y'.2.1 h1))
    · rintro ⟨_, hy⟩
      obtain ⟨z, hz, rfl⟩ := hY₀ hy
      have hzX : (z : G) ∈ X := Subgroup.mem_subgroupOf.mp hz
      exact ⟨⟨z, (hmem z hzX).mpr hy⟩, rfl⟩
  exact horb k hk0 hkm Y₁ inf_le_left hcard₁ hgY₁

theorem false_of_oddCore_not_centralized (h : D2L2Data p M H R X) (hD1 : D1For G)
    (hp5 : 5 ≤ p) (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsp : s ≠ p)
    (hns : ¬ barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)) :
    False := by
  have hp : p.Prime := Fact.out
  have := Fact.mk hs
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  obtain ⟨t, lam, htK, htX, hlam, -, hscal, horb⟩ := exists_scalar_torus_element hp5 h.torus
  have htM : t ∈ M := htK.2
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  have hrank : 4 ≤ Open.pRank s Sg :=
    stmtOddCoreRankScalar hs hs2 hp hp5 hsp Sg (barM M X) (mk ⟨t, htM⟩) lam
      CFSG.pCore_isPGroup (le_top.trans hSgN) h.isElemAbelian_barM h.card_barM
      (hSgN (Subgroup.mem_top _)) (mem_normalizer_barM htM htX) hlam
      (barM_conj_pow_eq_pow htM hscal)
      (fun k hk0 hkm _ hY₀ hcard => h.pow_notMem_normalizer_barM htM htX horb hk0 hkm hY₀ hcard)
      hns
  have hSgK : Sg ≤ barM M (H ⊓ M) :=
    h.pair.le_barM_inf_of_le_centralizer
      ((pCore_le_pPrimeCore_two hs hs2).trans (h.pair.oddCore_le_centralizer h84 hD2))
  have h4 : 4 ≤ Open.pRank s (H ⊓ M) :=
    hrank.trans ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono s hs hSgK).trans
      (pRank_barM_le hs hs2 M (H ⊓ M) inf_le_right))
  exact h.pair.false_of_four_le_pRank hD1 hs hs2 h4

theorem le_pCore_of_forall_le_centralizer_components (h : D2L2Data p M H R X)
    (hD1 : D1For G) (hp5 : 5 ≤ p) (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G)
    (hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M X ≤ Subgroup.centralizer (Lbar : Set _)) :
    barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) :=
  h.le_pCore_of_forall_le_centralizer h84 hD2 hcomp fun _ hs hs2 hsp =>
    by_contra fun hns => h.false_of_oddCore_not_centralized hD1 hp5 h84 hD2 hs hs2 hsp hns

end D2L2Data

end CFSG.AGLEmbeddingD2
