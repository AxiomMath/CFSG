module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3PlaneCount
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34e
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_fixes_of_mem_centralizer {x n : G} (hn : n ∈ centralizer ({x} : Set G)) :
    n * x * n⁻¹ = x :=
  mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hn)

theorem GL83GenericPrimeThreeM11Lemma42.of_planes (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree)
    (hno : NoExcludedSection3 G) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hKT : KFactM11SylowTransitive) (hL : KFactsL34Full)
    (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three) (hE3 : KFactL28BorelCore) :
    GL83GenericPrimeThreeM11Lemma42 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ hprop
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ : IsM11Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨K₀, hK₀Q, hK₀el, hK₀c, hxK₀, htr⟩ := p34_exists_K₀ hS hU0 hKM hKA hKT hp hM hgen hJ
  have hxLO : IsLargeObstruction 3 M x := hgen.2.1
  have hK₀M : K₀ ≤ M := (hK₀Q.trans inf_le_left).trans hPM
  have hK₀N : normalizer (K₀ : Set G) ≤ M := normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM
    (elementary_isPGroup 3 K₀ hK₀el) hK₀M (le_pRank_of_elemAbelian_card le_rfl hK₀el hK₀c)
  have hcomm : ∀ k ∈ K₀, k * x = x * k := fun k hk =>
    mem_centralizer_singleton_iff.mp (hK₀Q hk).2
  have htr' : ∀ a ∈ K₀, ∀ b ∈ K₀, a ≠ 1 → b ≠ 1 →
      ∃ n ∈ M, n * x * n⁻¹ = x ∧ n * a * n⁻¹ = b := by
    intro a ha b hb ha1 hb1
    obtain ⟨n, hnC, hnN, hnab⟩ := htr a ha b hb ha1 hb1
    exact ⟨n, hK₀N hnN, conj_fixes_of_mem_centralizer hnC, hnab⟩
  have hx3 : x ^ 3 = 1 := hxLO.2.2.1
  have hPc : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hprop.1.is_comm.comm (⟨a, ha⟩ : (P : Subgroup G)) ⟨b, hb⟩)
  have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (hPc g hg x hgen.1)
  have hrank : CFSG.Open.pRank 3 (P : Subgroup G) = 3 := by
    have h := hgen.2.2.2
    rwa [inf_of_le_left hPC] at h
  have hKz : K₀ ≤ centralizer ((zpowers x : Subgroup G) : Set G) := fun k hk => by
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ha
    exact ((Commute.zpow_right (show Commute k x from hcomm k hk) j).eq).symm
  have hEel : IsElemAbelian 3 (K₀ ⊔ zpowers x) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hK₀el
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3) hKz
  have hEcard : Nat.card ↥(K₀ ⊔ zpowers x) = 3 ^ 3 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three K₀ hx3 hxK₀ hcomm, hK₀c]
    norm_num
  have hEP : K₀ ⊔ zpowers x ≤ (P : Subgroup G) :=
    sup_le (hK₀Q.trans inf_le_left) (zpowers_le.mpr hgen.1)
  intro U hUP hU hUc hxU u huU hux
  exact lemma42_of_transitive_plane hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM
    hxLO hK₀M hK₀el hK₀c hxK₀ hcomm htr'
    (mem_elem27_of_pow_three hPc hrank hEP hEel hEcard (hUP huU) (hU.2 u huU)) hux

theorem GL83GenericPrimeThreeL34Lemma42.of_planes (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree)
    (hno : NoExcludedSection3 G) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hL : KFactsL34Full) (hA1 : A6SylowData)
    (hA3 : A6BorelCore) (hE1 : KFactL28Three) (hE3 : KFactL28BorelCore) :
    GL83GenericPrimeThreeL34Lemma42 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ hprop
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ : IsL34Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨-, hEel, -, hΩ, -⟩ := hprop
  have hxLO : IsLargeObstruction 3 M x := hgen.2.1
  set K₀ : Subgroup G := (P : Subgroup G) ⊓ J with hK₀
  have hK₀c : Nat.card K₀ = 3 ^ 2 :=
    l34Sign_card_inf hS hU0 hL.twoSignalizer hL.three hp hM hgen hJ
  have hxJ : x ∉ J := l34_x_not_mem_J hS hU0 hL.twoSignalizer hL.three hp hM hgen hJ
  have hK₀E : K₀ ≤ K₀ ⊔ zpowers x := le_sup_left
  have hK₀el : IsElemAbelian 3 K₀ :=
    ⟨⟨⟨fun a b => Subtype.ext (by
      have h := congrArg Subtype.val (hEel.1.is_comm.comm (⟨a, hK₀E a.2⟩ : ↥(K₀ ⊔ zpowers x))
        ⟨b, hK₀E b.2⟩)
      exact h)⟩⟩, fun a ha => hEel.2 a (hK₀E ha)⟩
  have hK₀M : K₀ ≤ M := inf_le_left.trans hPM
  have hxK₀ : x ∉ K₀ := fun h => hxJ h.2
  have hcomm : ∀ k ∈ K₀, k * x = x * k := fun k hk =>
    mem_centralizer_singleton_iff.mp (hJ.le_centralizer hk.2)
  have hK₀N : normalizer (K₀ : Set G) ≤ M := normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM
    (elementary_isPGroup 3 K₀ hK₀el) hK₀M (le_pRank_of_elemAbelian_card le_rfl hK₀el hK₀c)
  have htr := l34_transitive hL.sylowTransitive hgen hJ
  have htr' : ∀ a ∈ K₀, ∀ b ∈ K₀, a ≠ 1 → b ≠ 1 →
      ∃ n ∈ M, n * x * n⁻¹ = x ∧ n * a * n⁻¹ = b := by
    intro a ha b hb ha1 hb1
    obtain ⟨n, hnC, hnN, hnab⟩ := htr a ha b hb ha1 hb1
    exact ⟨n, hK₀N hnN, conj_fixes_of_mem_centralizer hnC, hnab⟩
  intro U hUP hU hUc hxU u huU hux
  exact lemma42_of_transitive_plane hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM
    hxLO hK₀M hK₀el hK₀c hxK₀ hcomm htr' (hΩ u (hUP huU) (hU.2 u huU)) hux

end CFSG.LocalAnalysis.RankThreeTheoremC
