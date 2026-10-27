module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcToral
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamTransfer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace CrossExcU

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Subgroup

section Props

@[expose] noncomputable def unitaryOrder (ℓ f p : ℕ) : ℕ :=
  orderOf (-((ℓ ^ f : ℕ) : ZMod p))

@[expose] def UnitaryRankAt (ℓ f : ℕ) (K : Type) [Field K] [Finite K] (n p e' : ℕ) : Prop :=
  4 * e' ≤ n → ∀ Y : unitarySU ℓ f K n, Y ^ p = 1 →
    3 ≤ CFSG.Open.pRank p (centralizer ({Y} : Set (unitarySU ℓ f K n)))

@[expose] def UnitaryAbelianAt (ℓ f : ℕ) (K : Type) [Field K] [Finite K] (n p e' : ℕ) : Prop :=
  n / e' < p → ∀ P : Subgroup (unitarySU ℓ f K n), IsPGroup p P → IsMulCommutative P

@[expose] def UnitaryRankProp : Prop :=
  ∀ (ℓ f : ℕ) (K : Type) [Field K] [Finite K], UnitaryFieldData ℓ f K → ∀ (n p : ℕ),
    p.Prime → 5 ≤ p → ¬ p ∣ ℓ → UnitaryRankAt ℓ f K n p (unitaryOrder ℓ f p)

@[expose] def UnitaryAbelianProp : Prop :=
  ∀ (ℓ f : ℕ) (K : Type) [Field K] [Finite K], UnitaryFieldData ℓ f K → ∀ (n p : ℕ),
    p.Prime → 5 ≤ p → ¬ p ∣ ℓ → UnitaryAbelianAt ℓ f K n p (unitaryOrder ℓ f p)

end Props

section Bookkeeping

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K] {n p : ℕ} [hp : Fact p.Prime]

theorem crossExcU_not_dvd_card_scalars (h : UnitaryFieldData ℓ f K) (hn : 1 ≤ n)
    (hg : ¬ (p ∣ n ∧ p ∣ ℓ ^ f + 1)) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (unitarySU ℓ f K n)) := by
  rw [← unitaryScalars_eq h hn, card_unitaryScalars h hn]
  intro hd
  exact hg ⟨hd.trans (Nat.gcd_dvd_left _ _), hd.trans (Nat.gcd_dvd_right _ _)⟩

theorem crossExcU_rank_statedProj (h : UnitaryFieldData ℓ f K) (hn : 1 ≤ n)
    (hg : ¬ (p ∣ n ∧ p ∣ ℓ ^ f + 1))
    (hR : ∀ Y : unitarySU ℓ f K n, Y ^ p = 1 →
      3 ≤ CFSG.Open.pRank p (centralizer ({Y} : Set (unitarySU ℓ f K n))))
    (y : StatedProj (StatedSU n (ℓ ^ f) K)) (hy : y ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (StatedProj (StatedSU n (ℓ ^ f) K)))) := by
  have hN := crossExcU_not_dvd_card_scalars h hn hg
  obtain ⟨ŷ, hŷp, rfl⟩ := exists_pow_eq_one_lift
    ((StatedScalars (Fin n) K).subgroupOf (unitarySU ℓ f K n)) hN y hy
  obtain ⟨F, hFle, hF, hFcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt
    (centralizer ({ŷ} : Set (unitarySU ℓ f K n)))
  have hFy : ∀ x ∈ F, x * ŷ = ŷ * x := fun x hx => by
    have := hFle hx
    rwa [Subgroup.mem_centralizer_singleton_iff] at this
  exact (hR ŷ hŷp).trans
    (le_pRank_centralizer_quotient _ hN hF hFcard hFy)

theorem crossExcU_abelian_statedProj (h : UnitaryFieldData ℓ f K) (hn : 1 ≤ n) (hp5 : 5 ≤ p)
    (hg : ¬ (p ∣ n ∧ p ∣ ℓ ^ f + 1)) {e' : ℕ} (he' : 0 < e')
    (hR1 : 4 * e' ≤ n → ∀ Y : unitarySU ℓ f K n, Y ^ p = 1 →
      3 ≤ CFSG.Open.pRank p (centralizer ({Y} : Set (unitarySU ℓ f K n))))
    (hR2 : n / e' < p → ∀ P : Subgroup (unitarySU ℓ f K n), IsPGroup p P → IsMulCommutative P)
    (h2 : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K))) = 2)
    (R : Sylow p (StatedProj (StatedSU n (ℓ ^ f) K))) :
    IsMulCommutative (R : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K))) := by
  by_cases h4 : 4 * e' ≤ n
  · exfalso
    have h3 := crossExcU_rank_statedProj h hn hg (hR1 h4) 1 (one_pow p)
    have hc : centralizer ({1} : Set (StatedProj (StatedSU n (ℓ ^ f) K))) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.2 (by simp)
    rw [hc, h2] at h3
    omega
  · have hsmall : n / e' < p := by
      rw [Nat.div_lt_iff_lt_mul he']
      nlinarith [not_le.1 h4]
    exact isMulCommutative_sylow_of_surjective
      (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (unitarySU ℓ f K n)))
      (QuotientGroup.mk'_surjective _)
      (fun S => hR2 hsmall _ S.isPGroup') R

theorem crossExcU_rank_statedProj_full (h : UnitaryFieldData ℓ f K) (hn : 1 ≤ n) (hp5 : 5 ≤ p)
    (hg : ¬ (p ∣ n ∧ p ∣ ℓ ^ f + 1)) {e' : ℕ} (he' : 0 < e')
    (hR1 : 4 * e' ≤ n → ∀ Y : unitarySU ℓ f K n, Y ^ p = 1 →
      3 ≤ CFSG.Open.pRank p (centralizer ({Y} : Set (unitarySU ℓ f K n))))
    (hR2 : n / e' < p → ∀ P : Subgroup (unitarySU ℓ f K n), IsPGroup p P → IsMulCommutative P)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K))))
    (y : StatedProj (StatedSU n (ℓ ^ f) K)) (hy : y ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set (StatedProj (StatedSU n (ℓ ^ f) K)))) := by
  by_cases h4 : 4 * e' ≤ n
  · exact crossExcU_rank_statedProj h hn hg (hR1 h4) y hy
  · have hsmall : n / e' < p := by
      rw [Nat.div_lt_iff_lt_mul he']
      nlinarith [not_le.1 h4]
    exact three_le_pRank_centralizer_of_sylow_abelian
      (fun R => isMulCommutative_sylow_of_surjective
        (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (unitarySU ℓ f K n)))
        (QuotientGroup.mk'_surjective _) (fun S => hR2 hsmall _ S.isPGroup') R) h3 hy

end Bookkeeping

end CrossExcU

end CFSG.LocalAnalysis.RankFourTheoremC
