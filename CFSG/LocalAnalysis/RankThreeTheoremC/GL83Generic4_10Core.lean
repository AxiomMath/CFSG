module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCase
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Absorb
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u3main_core_facts (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {x : G} (hgen : IsGenericPoint p P M x) {J : Subgroup G}
    (hJC : J ≤ centralizer ({x} : Set G))
    (hCJ : centralizer ({x} : Set G) ≤ normalizer (J : Set G)) :
    rankThreePrimeCore p J ≤ M ∧ Odd (Nat.card (rankThreePrimeCore p J)) := by
  obtain ⟨-, ⟨-, -, -, -, hCM⟩, -, hrk⟩ := hgen
  have hsub : IsSubnormal J (centralizer ({x} : Set G)) :=
    IsSubnormal.step hJC ((normal_subgroupOf_iff_le_normalizer hJC).mpr hCJ) (IsSubnormal.refl _)
  have h1 : rankThreePrimeCore p J ≤
      CFSG.ABGTheoremB.pPrimeCoreIn p (centralizer ({x} : Set G)) := by
    have h : GLBPrimeCore p J ≤ GLBPrimeCore p (centralizer ({x} : Set G)) := by
      rw [glbPrimeCore_eq_primeComplementCoreOf, glbPrimeCore_eq_primeComplementCoreOf]
      exact cfsg_subnormal_primeComplementCoreOf_le p hsub
    exact h.trans (glbPrimeCore_le_pPrimeCoreIn p _)
  refine ⟨h1.trans (pPrimeCoreIn_centralizer_le hS hp hM hrk.ge), ?_⟩
  have h2 := odd_card_pPrimeCoreIn_of_not_le hS hD1 hp hM hrk.ge hCM
  exact (Nat.odd_iff.mpr (by omega)).of_dvd_nat (Subgroup.card_dvd_of_le h1)

omit [Finite G] in
private theorem u3main_zpow_of_sq_eq_one {z : G} (hz : z ^ 2 = 1) (k : ℤ) :
    z ^ k = 1 ∨ z ^ k = z := by
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul]
    simp [hz]
  · right
    rw [zpow_add, zpow_mul]
    simp [hz]

omit [Finite G] in
theorem u3main_isTwoLocal_centralizer {z : G} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    IsTwoLocal (centralizer ({z} : Set G)) := by
  refine ⟨zpowers z, by rwa [Ne, zpowers_eq_bot], IsPGroup.of_card (n := 1) ?_, ?_⟩
  · rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one]
  · ext g
    rw [mem_centralizer_singleton_iff, mem_normalizer_iff]
    constructor
    · intro hg y
      have hc : Commute g z := hg
      have hc' : ∀ k : ℤ, g * z ^ k = z ^ k * g := fun k => (hc.zpow_right k).eq
      constructor
      · intro hy
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
        refine mem_zpowers_iff.2 ⟨k, ?_⟩
        rw [hc' k]
        group
      · intro hy
        obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy
        refine mem_zpowers_iff.2 ⟨k, ?_⟩
        have : g * y = g * z ^ k := by
          rw [hc' k, hk]
          group
        exact (mul_left_cancel this).symm
    · intro hn
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 ((hn z).1 (mem_zpowers z))
      have hne : g * z * g⁻¹ ≠ 1 := by
        intro h
        apply hz1
        have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
        rw [this, h]
        group
      rcases u3main_zpow_of_sq_eq_one hz2 k with h | h
      · exact absurd (hk.symm.trans h) hne
      · have : g * z * g⁻¹ = z := hk.symm.trans h
        calc g * z = (g * z * g⁻¹) * g := by group
          _ = z * g := by rw [this]

theorem u3main_centralizer_le (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {R E : Subgroup G} (hRe : IsElemAbelian p R)
    (hRc : Nat.card R = p ^ 2) (hEe : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (hEM : E ≤ M) (hER : E ≤ centralizer (R : Set G)) {z : G} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hRz : R ≤ centralizer ({z} : Set G))
    (h2 : CFSG.Open.pRank p (centralizer ({z} : Set G)) ≤ 2 → centralizer ({z} : Set G) ≤ M) :
    centralizer ({z} : Set G) ≤ M := by
  by_cases h : CFSG.Open.pRank p (centralizer ({z} : Set G)) ≤ 2
  · exact h2 h
  · exact le_of_isTwoLocal_of_three_le_pRank hS hD1 hU0 hp hM hRe hRc hEe hEc hEM hER
      (u3main_isTwoLocal_centralizer hz1 hz2) hRz (by omega)

theorem u3main_plane_cube {p : ℕ} [Fact p.Prime] {P J E₂ : Subgroup G} {x c : G}
    (hxP : x ∈ P) (hcP : c ∈ P) (hE₂P : E₂ ≤ P) (hxp : x ^ p = 1) (hc1 : c ≠ 1)
    (hcp : c ^ p = 1) (hcJ : c ∈ J) (hE₂J : E₂ ≤ J) (hxJ : x ∉ J)
    (hJC : J ≤ centralizer ({x} : Set G)) (hE₂e : IsElemAbelian p E₂)
    (hE₂c : Nat.card E₂ = p ^ 2) (hcE : ∀ e ∈ E₂, e * c = c * e) :
    ∃ R E : Subgroup G, R ≤ P ∧ IsElemAbelian p R ∧ Nat.card R = p ^ 2 ∧ x ∈ R ∧
      (∀ z ∈ J, z * c = c * z → R ≤ centralizer ({z} : Set G)) ∧
      E ≤ P ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ E ≤ centralizer (R : Set G) := by
  have hp : p.Prime := Fact.out
  have hxJc : ∀ y ∈ J, y * x = x * y := fun y hy => mem_centralizer_singleton_iff.mp (hJC hy)
  have hcz : zpowers c ≤ J := zpowers_le.mpr hcJ
  have hxE₂ : x ∉ E₂ := fun h => hxJ (hE₂J h)
  have hEc' : E₂ ⊔ zpowers x ≤ centralizer ({c} : Set G) :=
    sup_le (fun e he => mem_centralizer_singleton_iff.mpr (hcE e he))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hxJc c hcJ).symm))
  have hEx' : E₂ ⊔ zpowers x ≤ centralizer ({x} : Set G) :=
    sup_le (fun e he => mem_centralizer_singleton_iff.mpr (hxJc e (hE₂J he)))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  refine ⟨zpowers c ⊔ zpowers x, E₂ ⊔ zpowers x,
    sup_le (zpowers_le.mpr hcP) (zpowers_le.mpr hxP), ?_, ?_, mem_sup_right (mem_zpowers x), ?_,
    sup_le hE₂P (zpowers_le.mpr hxP), ?_, ?_, ?_⟩
  · refine CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup
      (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hcp)
      (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hxp) ?_
    rintro a ⟨m, rfl⟩ b ⟨n, rfl⟩
    exact ((Commute.zpow_zpow (hxJc c hcJ) m n)).eq
  · have hxc : x ∉ zpowers c := fun h => hxJ (hcz h)
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers c) hxp hxc
      (fun e he => hxJc e (hcz he)), Nat.card_zpowers, orderOf_eq_prime hcp hc1, sq]
  · intro z hzJ hzc
    exact sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzc.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hxJc z hzJ).symm))
  · refine CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup hE₂e
      (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hxp) ?_
    rintro a ha b ⟨n, rfl⟩
    exact (Commute.zpow_right (hxJc a (hE₂J ha)) n).eq
  · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp E₂ hxp hxE₂
      (fun e he => hxJc e (hE₂J he)), hE₂c]
    ring
  · rw [Subgroup.le_centralizer_iff]
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · exact mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hEc' hh)
    · exact mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hEx' hh)

end CFSG.LocalAnalysis.RankThreeTheoremC
