module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ITits
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IInner
public import CFSG.LieType.BorelTits.Classical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointReindexCovarianceBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (plusIndexEquiv)
open CFSG.Assembly.LowTwoRank
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section General

variable {G : Type} [Group G] [Finite G] (r : ℕ) [Fact r.Prime]

theorem pCoreOf_le_sylow {H : Subgroup G} (S : Sylow r G) (hSH : (S : Subgroup G) ≤ H) :
    pCoreOf r H ≤ S := by
  haveI : (pCore r H).Normal := CFSG.LieType.BorelTits.pCore_normal r
  have h1 : pCore r H ≤ (S.subtype hSH : Subgroup H) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := H) r).le_sylow_of_normal (S.subtype hSH)
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSH] at h2
  exact h2

end General

theorem holds_D4Model_three {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 3 ^ n)
    (hn : 1 ≤ n) : Holds (D4Model K) 3 :=
  holds_of_statedClassicalModel (t := .POmegaPlus) (n := 4) (p := 3) (f := n)
    ⟨⟨Nat.prime_three, hn, le_rfl⟩, K, inferInstance, inferInstance, hK,
      ⟨(statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm⟩⟩

@[expose] def D3InnerLevi : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∀ t : MulAut (D4Model K), t ^ 3 = 1 → t ∉ D4Img K →
      ∀ z : MulAut (D4Model K), z ^ 2 = 1 → z ≠ 1 →
        z ∈ Inn (D4Model K) → z * t = t * z →
        ∀ V : Subgroup (D4Model K), V ≠ ⊥ → IsPGroup 3 V →
          V.map t.toMonoidHom = V → V.map z.toMonoidHom = V →
          pCoreOf 3 (Subgroup.normalizer (V : Set (D4Model K))) = V →
          Subgroup.normalizer (V : Set (D4Model K)) ≠ ⊤ →
          (∃ S : Sylow 3 (D4Model K),
            Subgroup.normalizer ((S : Subgroup (D4Model K)) : Set (D4Model K)) ≤
              Subgroup.normalizer (V : Set (D4Model K))) →
          ∃ S : Sylow 3 (D4Model K),
            (S : Subgroup (D4Model K)) ≤ Subgroup.normalizer (V : Set (D4Model K)) ∧
            (S : Subgroup (D4Model K)).map t.toMonoidHom = S ∧
            (S : Subgroup (D4Model K)).map z.toMonoidHom = S

theorem d3InnerSylow_of_levi (h : D3InnerLevi) : D3InnerSylow := by
  intro K _ _ n hK t ht3 htE z hz2 hz1 hzI hzt A hA hA1 hAt hAz
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : 1 ≤ n := by
    by_contra hn0
    have hn0' : n = 0 := by omega
    subst hn0'
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h2
    simp at h2
  have hBT := holds_D4Model_three hK hn
  have hAp : IsPGroup 3 A := fun a => ⟨1, by
    apply Subtype.ext
    simpa using hA.2 a.1 a.2⟩
  have hmapt : A.map t.toMonoidHom = A := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      change t a ∈ A
      rw [hAt a ha]; exact ha
    · intro hx
      exact ⟨x, hx, hAt x hx⟩
  have hmapz : A.map z.toMonoidHom = A := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      change z a ∈ A
      rw [hAz a ha]; exact ha
    · intro hx
      exact ⟨x, hx, hAz x hx⟩
  obtain ⟨V, hAV, hV1, hVp, hVφ, hVtop, hVc, hVS⟩ :=
    exists_canonical_parabolic 3 hBT hA1 hAp
  obtain ⟨S, hSV, hSt, hSz⟩ := h K n hK t ht3 htE z hz2 hz1 hzI hzt V hV1 hVp
    (hVφ t hmapt) (hVφ z hmapz) hVc hVtop hVS
  refine ⟨S, hAV.trans ?_, hSt, hSz⟩
  rw [← hVc]
  exact pCoreOf_le_sylow 3 S hSV

end CFSG.LocalAnalysis.GLTheoremA
