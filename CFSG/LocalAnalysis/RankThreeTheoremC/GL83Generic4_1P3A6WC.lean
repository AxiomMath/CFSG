module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6QStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3FusionLines
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowLift
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a6_prop34_of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hAct : KFactA6SylowAction) (hAut : A6AutData)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J) :
    A6Prop34 3 P J x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hQab, hΩ⟩ := a6_prop34_abel hS hU0 hA1 hAut hp hM hgen hJ
  refine ⟨hQab, hΩ, ?_⟩
  obtain ⟨hxP, hxLO, -, -⟩ := id hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := id hxLO
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hJC := hJ.le_centralizer
  have hxJ : x ∉ J := a6_x_not_mem_J hS hU0 hp hM hgen hJ
  set K₀ : Subgroup G := (P : Subgroup G) ⊓ J with hK₀
  have hK₀el : IsElemAbelian 3 K₀ := a6_inf_isElemAbelian hA1 hgen hJ
  have hK₀c : Nat.card K₀ = 3 ^ 2 := (a6_T_data hS hU0 hA1 hp hM hgen hJ).2.2
  have hK₀M : K₀ ≤ M := inf_le_left.trans hPM
  have hK₀N : normalizer (K₀ : Set G) ≤ M := normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM
    (elementary_isPGroup 3 K₀ hK₀el) hK₀M (le_pRank_of_elemAbelian_card le_rfl hK₀el hK₀c)
  have hK₀x : ∀ t ∈ K₀, ∀ c ∈ zpowers x, t * c = c * t := fun t ht c hc => by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (show Commute t x from
      mem_centralizer_singleton_iff.mp (hJC ht.2)) j).eq
  intro g hg
  have hyQ : g * x * g⁻¹ ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    hg ⟨x, mem_zpowers x, rfl⟩
  have hyLO : IsLargeObstruction 3 M (g * x * g⁻¹) :=
    isLargeObstruction_conj_of_map_le hS hU0 hp hM hxP hxLO (hg.trans inf_le_left)
  have hconj : (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers (g * x * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [hconj]
  obtain ⟨k, hk, v, hv, hyeq⟩ := u3l42_decomp hK₀x (hΩ _ hyQ hyLO.2.2.1)
  by_cases hk1 : k = 1
  ·
    left
    have hyx : g * x * g⁻¹ ∈ zpowers x := by
      rw [hyeq, hk1, one_mul]
      exact hv
    exact p34_zpowers_eq_of_mem (orderOf_eq_prime hx3 hx1) hyx hyLO.2.1
  by_cases hv1 : v = 1
  ·
    right
    have hyJ : g * x * g⁻¹ ∈ J := by
      rw [hyeq, hv1, mul_one]
      exact hk.2
    exact zpowers_le.mpr hyJ
  exfalso
  obtain ⟨n, hnC, hnN, hninv⟩ := a6_exists_inverting hAct hgen hJ
  have hnM : n ∈ M := hK₀N hnN
  have hnx : n * x * n⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hnC)
  have hk3 : k ^ 3 = 1 := hK₀el.2 k hk
  have hxk : x ∉ zpowers k := fun h => hxJ (zpowers_le.mpr hk.2 h)
  have hkx : k * x = x * k := hK₀x k hk x (mem_zpowers x)
  have hyD : g * x * g⁻¹ ∈ zpowers k ⊔ zpowers x := by
    rw [hyeq]
    exact Subgroup.mul_mem _ (mem_sup_left (mem_zpowers k)) (mem_sup_right hv)
  have hyk : g * x * g⁻¹ ∉ zpowers k := fun h => by
    have hv' : v ∈ zpowers k := by
      rw [hyeq] at h
      simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_zpowers k)) h
    have hcx : zpowers v = zpowers x := p34_zpowers_eq_of_mem (orderOf_eq_prime hx3 hx1) hv hv1
    have hxv : x ∈ zpowers v := by
      rw [hcx]
      exact mem_zpowers x
    exact hxk (zpowers_le.mpr hv' hxv)
  have hyx : g * x * g⁻¹ ∉ zpowers x := fun h => by
    have hk' : k ∈ zpowers x := by
      rw [hyeq] at h
      simpa using Subgroup.mul_mem _ h (Subgroup.inv_mem _ hv)
    have hcx : zpowers k = zpowers x := p34_zpowers_eq_of_mem (orderOf_eq_prime hx3 hx1) hk' hk1
    have hxk' : x ∈ zpowers k := by
      rw [hcx]
      exact mem_zpowers x
    exact hxk hxk'
  exact false_of_mixed_pair hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hxLO
    (hK₀M hk) hk1 hk3 hxk hkx hnM hnx (hninv k hk) hyD hyk hyx hyLO

theorem GL83GenericPrimeThreeA6Prop34.of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree)
    (hno : NoExcludedSection3 G) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore)
    (hE1 : KFactL28Three) (hE3 : KFactL28BorelCore) (hAct : KFactA6SylowAction)
    (hAut : A6AutData) : GL83GenericPrimeThreeA6Prop34 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  subst hp3
  exact a6_prop34_of_kfacts hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hAct hAut hp hM
    hgen ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
