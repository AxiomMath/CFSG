module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
import CFSG.LocalAnalysis.RankThreeTheoremC.FusionControl

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace EightTwo

theorem normalizer_le_of_isAlperinSubgroup {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2)
    {P : Sylow p G} {M : Subgroup G} (hP : ¬ IsCyclic (P : Subgroup G))
    (hΓ : rankThreeGamma 2 p (P : Subgroup G) ≤ M) {Q : Subgroup G}
    (hQ : CFSG.RankTwoShapes.IsAlperinSubgroup p (P : Subgroup G) Q) :
    normalizer (Q : Set G) ≤ M := by
  have hQp : IsPGroup p Q := P.isPGroup'.to_le hQ.1
  have h2 : 2 ≤ CFSG.Open.pRank p Q :=
    two_le_pRank_of_not_isCyclic hp.out hodd hQp
      (not_isCyclic_of_isAlperinSubgroup P.isPGroup' hP hQ)
  exact (gamma_normalizer_le 2 p (P : Subgroup G) Q hQ.1 h2).trans hΓ

theorem mem_of_alperinDecomposition {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2)
    {P : Sylow p G} {M : Subgroup G} (hP : ¬ IsCyclic (P : Subgroup G))
    (hΓ : rankThreeGamma 2 p (P : Subgroup G) ≤ M) {A : Subgroup G} {c : G}
    (hdec : CFSG.RankTwoShapes.AlperinDecomposition p (P : Subgroup G) A c) : c ∈ M := by
  induction hdec with
  | one => exact M.one_mem
  | step _ hQ _ hn ih => exact M.mul_mem ih (normalizer_le_of_isAlperinSubgroup hodd hP hΓ hQ hn)

theorem exists_mem_conj_eq {p : ℕ} [hp : Fact p.Prime] (hodd : p ≠ 2)
    {P : Sylow p G} {M : Subgroup G} (hP : ¬ IsCyclic (P : Subgroup G))
    (hΓ : rankThreeGamma 2 p (P : Subgroup G) ≤ M) {a g : G} (ha : a ∈ (P : Subgroup G))
    (hg : g * a * g⁻¹ ∈ (P : Subgroup G)) : ∃ m ∈ M, m * a * m⁻¹ = g * a * g⁻¹ := by
  have hA : zpowers a ≤ (P : Subgroup G) := zpowers_le.2 ha
  have hAg : (zpowers a).map (MulAut.conj g⁻¹⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    simpa [MulAut.conj_apply] using hg
  obtain ⟨c, hdec, hc⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion P hA hAg
  refine ⟨c⁻¹, M.inv_mem (mem_of_alperinDecomposition hodd hP hΓ hdec), ?_⟩
  simpa using hc a (mem_zpowers a)

theorem not_hasNormalIndex {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G} {M : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hperf : commutator G = ⊤)
    (hfus : ∀ a g : G, a ∈ (P : Subgroup G) → g * a * g⁻¹ ∈ (P : Subgroup G) →
      ∃ m ∈ M, m * a * m⁻¹ = g * a * g⁻¹) :
    ¬ HasNormalIndex M p := by
  rintro ⟨N, hNM, hNn, hNidx⟩
  haveI : (N.subgroupOf M).Normal := hNn
  haveI : IsCyclic (M ⧸ N.subgroupOf M) := isCyclic_of_prime_card (p := p) hNidx
  have hker := Abelianization.commutator_subset_ker (QuotientGroup.mk' (N.subgroupOf M))
  rw [QuotientGroup.ker_mk'] at hker
  have hcomm : ∀ x ∈ M, ∀ m ∈ M, x⁻¹ * m * x * m⁻¹ ∈ N := by
    intro x hx m hm
    have h1 : ⁅(⟨x⁻¹, M.inv_mem hx⟩ : M), (⟨m, hm⟩ : M)⁆ ∈ commutator M :=
      commutator_mem_commutator (mem_top _) (mem_top _)
    have h2 := mem_subgroupOf.mp (hker h1)
    simpa [commutatorElement_def] using h2
  have hPN : (P : Subgroup G) ≤ N := by
    have hfoc := CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup p P
    rw [CFSG.derivedSubgroup, derivedSeries_one, hperf, inf_top_eq] at hfoc
    rw [hfoc, closure_le]
    rintro _ ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
    obtain ⟨m, hm, hmx⟩ := hfus x g hx hy
    rw [← hmx]
    simpa [mul_assoc] using hcomm x (hPM hx) m hm
  apply P.not_dvd_index
  have hdvd : N.relIndex M ∣ N.index := relIndex_dvd_index_of_le hNM
  have hp' : N.relIndex M = p := hNidx
  rw [hp'] at hdvd
  exact hdvd.trans (index_dvd_of_le hPN)

omit [Finite G] in
theorem commutator_eq_top_of_simple [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) :
    commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · obtain ⟨a, b, hab⟩ := hnab
    refine (hab ?_).elim
    have hmem : ⁅a, b⁆ ∈ commutator G :=
      commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  · exact h

end EightTwo

theorem agl81EightTwo_holds : AGL81EightTwo G := by
  intro hS p P M H₁ R₁ hesc hΓ
  haveI : Fact p.Prime := ⟨hesc.prime⟩
  have hP3 : 3 ≤ CFSG.Open.pRank p (P : Subgroup G) :=
    hesc.three_le_pRank.trans (pRank_mono p hesc.prime.one_lt hesc.le_P)
  have hP : ¬ IsCyclic (P : Subgroup G) := not_isCyclic_of_two_le_pRank hesc.prime (by omega)
  have hfus : ∀ a g : G, a ∈ (P : Subgroup G) → g * a * g⁻¹ ∈ (P : Subgroup G) →
      ∃ m ∈ M, m * a * m⁻¹ = g * a * g⁻¹ :=
    fun a g ha hg => EightTwo.exists_mem_conj_eq hesc.ne_two hP hΓ ha hg
  haveI := hS.simple
  exact ⟨hfus, EightTwo.not_hasNormalIndex hesc.sylow_le
    (EightTwo.commutator_eq_top_of_simple hS.nonab) hfus⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
