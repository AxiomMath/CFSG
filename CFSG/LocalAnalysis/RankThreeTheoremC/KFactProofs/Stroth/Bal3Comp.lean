module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Elem
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Reduce

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

section Reduced

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem exists_mem_inf_center_of_normalizing (hp : p.Prime) {P N : Subgroup X}
    (hP : IsPGroup p P) (hN : N ≠ ⊥) (hNP : N ≤ P) (hnorm : P ≤ normalizer (N : Set X)) :
    ∃ y ∈ N, orderOf y = p ∧ y ∈ centralizer (P : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  let N' : Subgroup P := N.subgroupOf P
  haveI : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).2 hnorm
  have hN' : N' ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hNP hx⟩ : P) ∈ N' := hx
    rw [h, mem_bot] at hx'
    exact mem_bot.2 (congrArg Subtype.val hx')
  obtain ⟨hdvd, -⟩ := CFSG.SectionRank.Ccomm.normal_inf_center_card (p := p) hP hN'
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(N' ⊓ center P)) p hdvd
  obtain ⟨hyN, hyZ⟩ := mem_inf.1 y.2
  refine ⟨(((y : ↥(N' ⊓ center P)) : P) : X), hyN, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hy
  · rw [mem_centralizer_iff]
    intro g hg
    have := mem_center_iff.1 hyZ ⟨g, hg⟩
    exact congrArg Subtype.val this

theorem mem_of_normalizing_ne_bot (hp : p.Prime) {P N : Subgroup X} (hP : IsPGroup p P)
    (hN : N ≠ ⊥) (hNP : N ≤ P) (hnorm : P ≤ normalizer (N : Set X)) {z : X}
    (hz : orderOf z = p) (hunique : ∀ y ∈ P, y ∈ centralizer (P : Set X) → y ^ p = 1 →
      y ∈ zpowers z) : z ∈ N := by
  obtain ⟨y₀, hy0N, hy0ord, hy0C⟩ := exists_mem_inf_center_of_normalizing hp hP hN hNP hnorm
  have hy0P : y₀ ∈ P := hNP hy0N
  have hy0p : y₀ ^ p = 1 := hy0ord ▸ pow_orderOf_eq_one y₀
  have hmem := hunique y₀ hy0P hy0C hy0p
  have hle : zpowers y₀ ≤ zpowers z := zpowers_le.2 hmem
  have hcard : Nat.card (zpowers z) ≤ Nat.card (zpowers y₀) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hy0ord, hz]
  have heq : zpowers y₀ = zpowers z := eq_of_le_of_card_ge hle hcard
  have : z ∈ zpowers y₀ := by rw [heq]; exact mem_zpowers z
  exact (zpowers_le.2 hy0N) this

theorem mem_centralizer_component_of_mem_pCore (hp : p.Prime)
    (hcore : primeComplementCore (G := X) p = ⊥) {z : X} (hz : z ∈ CFSG.pCore p X)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) : z ∈ centralizer (K : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  have hF : CFSG.fittingSubgroup X = CFSG.pCore p X := CFSG.Fitting_eq_pcore X p hcore
  have hEC : CFSG.layer X ≤ centralizer (CFSG.pCore p X : Set X) := by
    rw [← hF]
    exact le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp CFSG.LocalCores.fitting_layer_commute)
  have hKL : K ≤ CFSG.layer X := le_layer_of_isComponentOf hK
  rw [mem_centralizer_iff]
  intro k hk
  exact (mem_centralizer_iff.1 (hEC (hKL hk)) z hz).symm

end Reduced

section RedConfigLemmas

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {P : Sylow p X} {z : X} {D : Subgroup X}

theorem RedConfig.pRank_top (h : RedConfig p P z D) :
    CFSG.Open.pRank p (⊤ : Subgroup X) = 3 := by
  rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p h.prime P]
  exact h.rank

theorem RedConfig.mem_pCore (h : RedConfig p P z D) (hQ : CFSG.pCore p X ≠ ⊥) :
    z ∈ CFSG.pCore p X := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (CFSG.pCore p X).Normal := CFSG.pCore_normal
  refine mem_of_normalizing_ne_bot hp P.isPGroup' hQ
    (CFSG.pCore_isPGroup.le_sylow_of_normal P) ?_ h.ord h.unique
  rw [normalizer_eq_top]
  exact le_top

theorem RedConfig.le_normalizer_component (h : RedConfig p P z D) (hz : z ∈ CFSG.pCore p X)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) : (P : Subgroup X) ≤ normalizer (K : Set X) := by
  have hp := h.prime
  have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h.ne_two)
  refine le_normalizer_of_card_components_le hp (m := 2) hp3 ?_ P.isPGroup' hK
  intro S hS
  have hzp : z ^ p = 1 := h.ord ▸ pow_orderOf_eq_one z
  have hA : IsElemAbelian p (zpowers z) := isElemAbelian_zpowers hzp
  have hAcard : Nat.card (zpowers z) = p ^ 1 := by rw [Nat.card_zpowers, h.ord, pow_one]
  have hAC : ∀ K ∈ S, zpowers z ≤ centralizer (K : Set X) := fun K hK =>
    zpowers_le.2 (mem_centralizer_component_of_mem_pCore hp h.core hz (hS K hK))
  have := card_add_le_pRank_of_components hp h.ne_two h.core S hS hA hAcard hAC
  rw [h.pRank_top] at this
  omega

theorem RedConfig.mem_component (h : RedConfig p P z D) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hnorm : (P : Subgroup X) ≤ normalizer (K : Set X)) : z ∈ K := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, htRK, ht, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core P hK
  have hN : (P : Subgroup X) ⊓ K ≠ ⊥ := by
    intro hbot
    have ht1 : t = 1 := by
      have := htRK
      rw [hbot, mem_bot] at this
      exact this
    rw [ht1, orderOf_one] at ht
    exact hp.one_lt.ne ht
  have hz := mem_of_normalizing_ne_bot hp P.isPGroup' hN inf_le_left
    ((le_inf le_normalizer hnorm).trans inf_normalizer_le_normalizer_inf) h.ord h.unique
  exact hz.2

theorem RedConfig.dvd_card_center_component (h : RedConfig p P z D) (hz : z ∈ CFSG.pCore p X)
    {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hnorm : (P : Subgroup X) ≤ normalizer (K : Set X)) : p ∣ Nat.card (center K) := by
  have hzK := h.mem_component hK hnorm
  have hzc := mem_centralizer_component_of_mem_pCore h.prime h.core hz hK
  have hZ : (⟨z, hzK⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k
    apply Subtype.ext
    exact mem_centralizer_iff.1 hzc k k.2
  have hord : orderOf (⟨⟨z, hzK⟩, hZ⟩ : center K) = p := by
    rw [← h.ord, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
  rw [← hord]
  exact orderOf_dvd_natCard _

end RedConfigLemmas

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
