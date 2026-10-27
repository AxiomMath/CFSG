module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockCMBorel
import CFSG.LocalAnalysis.RankFourTheoremC.FullCoreBridge
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeAux
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointList

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace IsPPoint

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem centralizer_le_redCentM_of_involution [Fact p.Prime] (hS : D1Global G) (hD1 : D1For G)
    (hloc : D1Local p P M) (h : IsPPoint p P M x) {J : RedCent p x}
    (hJX : J ∈ redCentM p M x) (hJ2 : J ^ 2 = 1) (hJ1 : J ≠ 1) {Y : Subgroup (RedCent p x)}
    (hYp : IsPGroup p Y) (hYX : Y ≤ redCentM p M x)
    (hYJ : Y ≤ centralizer ({J} : Set (RedCent p x))) (hY3 : 3 ≤ Open.pRank p Y) :
    centralizer ({J} : Set (RedCent p x)) ≤ redCentM p M x := by
  have hp : p.Prime := Fact.out
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set OC : Subgroup C := primeComplementCore (G := C) p with hOC
  set ρ := QuotientGroup.mk' OC with hρ
  have hOcop : p.Coprime (Nat.card OC) := primeComplementCore_coprime p
  have hOM : ∀ o : C, o ∈ OC → (o : G) ∈ M := fun o ho => by
    have ho' : o ∈ (GLBPrimeCore p C).subgroupOf C := by
      rw [glbPrimeCore_subgroupOf]
      exact ho
    exact h.primeCore_le hloc ho'
  have hodd : Nat.Coprime 2 (Nat.card OC) := by
    have h2 := h.not_two_dvd_card_primeCore hS hD1 hloc
    have hcard : Nat.card OC = Nat.card (GLBPrimeCore p C) := by
      have e : (GLBPrimeCore p C).subgroupOf C = OC := glbPrimeCore_subgroupOf p C
      rw [← e]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (glbPrimeCore_le p C)).toEquiv
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2
  have hmemM : ∀ g : C, ρ g ∈ redCentM p M x → (g : G) ∈ M := by
    intro g hg
    obtain ⟨c, hc, hcg⟩ := hg
    have h1 : c⁻¹ * g ∈ OC := by
      rw [← QuotientGroup.ker_mk' OC, MonoidHom.mem_ker, map_mul, map_inv]
      exact inv_mul_eq_one.mpr hcg
    simpa using M.mul_mem hc.2 (hOM _ h1)
  obtain ⟨c, hc, hcJ⟩ := hJX
  obtain ⟨m, hj2, hjJ⟩ := exists_isPGroup_zpowers_pow_eq ρ (y := c) (by rw [hcJ, hJ2])
  set j : C := c ^ m with hj
  have hjJ' : ρ j = J := hjJ.trans hcJ
  have hlift : ∀ x' ∈ centralizer ({J} : Set (RedCent p x)),
      ∃ g ∈ centralizer ({j} : Set C), ρ g = x' := fun x' hx' =>
    exists_mem_centralizer_mk_eq Nat.prime_two OC hodd hj2 (by rw [hjJ']; exact hx')
  set W : Subgroup C := centralizer ({j} : Set C) ⊓ M.subgroupOf C with hW
  have hYW : Y ≤ W.map ρ := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := hlift y (hYJ hy)
    exact ⟨g, ⟨hg, hmemM g (hYX hy)⟩, rfl⟩
  obtain ⟨T, hTW, hTp, hTY⟩ := exists_isPGroup_le_map_eq ρ hYp hYW
  set Yh : Subgroup G := T.map C.subtype with hYh
  have hYhr : 3 ≤ Open.pRank p Yh := by
    rw [← pRank_map_mk_eq_pRank_map_subtype hp OC hOcop T, hTY]
    exact hY3
  set N : Subgroup G := normalizer ((zpowers (j : G) : Subgroup G) : Set G) with hN
  have hj2G : IsPGroup 2 (zpowers (j : G)) := by
    have := hj2.map C.subtype
    rwa [MonoidHom.map_zpowers] at this
  have hj1 : (j : G) ≠ 1 := fun hj1 => hJ1 (by
    rw [← hjJ', show j = 1 from Subtype.ext hj1, map_one])
  have hNloc : IsTwoLocal N := ⟨_, by rwa [Ne, Subgroup.zpowers_eq_bot], hj2G, rfl⟩
  have hCN : ∀ g : C, g ∈ centralizer ({j} : Set C) → (g : G) ∈ N := fun g hg =>
    mem_normalizer_zpowers_of_mem_zpowers (by
      rw [show (g : G) * (j : G) * (g : G)⁻¹ = j by
        rw [← Subgroup.coe_mul, mem_centralizer_singleton_iff.mp hg, Subgroup.coe_mul,
          mul_inv_cancel_right]]
      exact Subgroup.mem_zpowers _)
  have hYhN : Yh ≤ N := by
    rintro _ ⟨t, ht, rfl⟩
    exact hCN t (hTW ht).1
  have hYhM : Yh ≤ M := by
    rintro _ ⟨t, ht, rfl⟩
    exact (hTW ht).2
  have hNM : N ≤ M := le_of_three_le_pRank_inf (theoremD1_of_d1For hS.rank hD1)
    (mem_sigmaA_of_mem_betaFour hloc.beta) hloc.isCoreMaxLocal hNloc
    (hYhr.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf hYhN hYhM)))
  intro x' hx'
  obtain ⟨g, hg, rfl⟩ := hlift x' hx'
  exact ⟨g, ⟨g.2, hNM (hCN g hg)⟩, rfl⟩

end IsPPoint

section Three

variable {P : Sylow 3 G} {M : Subgroup G} {x : G}

theorem IsPPoint.false_of_borelData (h243 : GL83ComponentPCoreTrivial) (hS : D1Global G)
    (hD1 : D1For G) (hloc : D1Local 3 P M) (h : IsPPoint 3 P M x)
    {R : Sylow 3 (RedCent 3 x)} {K : Subgroup (RedCent 3 x)} (hRK : PPointReduced 3 M x R K)
    {n : ℕ} (hn : 2 ≤ n) (hB : ∀ T : Sylow 3 K, BorelInvolutionData K T n) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hzc, hzp⟩ := h.central_xbar hloc
  set z : RedCent 3 x := QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
    ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ with hz
  have hZ := hRK.center_eq_bot (by norm_num) h243 (h.catalogSimpleSections hS Nat.prime_three)
  have hzK : z ∉ K := by
    intro hzK
    have hzZ : (⟨z, hzK⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (mem_center_iff.mp hzc k)
    rw [hZ, mem_bot] at hzZ
    have : z = 1 := congrArg Subtype.val hzZ
    rw [this, orderOf_one] at hzp
    omega
  have hATb : zpowers z ≤ (R : Subgroup (RedCent 3 x)) :=
    zpowers_le.mpr (mem_sylow_of_mem_center hzc hzp R)
  obtain ⟨J, hJX, hJ2, hJ1, Ys, hYp, hYX, hYJ, -, hYrk, hCJ⟩ :=
    exists_involution_of_borelData hRK.red hzc hzp hRK.normal hzK hn hB hATb (mem_zpowers z)
      (CFSG.RankThree.zpowers_inf_eq_bot_of_not_mem Nat.prime_three hzp hzK)
  exact hCJ (h.centralizer_le_redCentM_of_involution hS hD1 hloc hJX hJ2 hJ1 hYp hYX hYJ
    (by omega))

theorem PPointReduced.false_of_excluded_three (h243 : GL83ComponentPCoreTrivial)
    (hUB : KFactUnitaryBorelMaximal) (hUI : KFactUnitaryInvolution)
    (hRB : KFactReeBorelMaximal) (hRI : KFactReeInvolution) (hS : D1Global G) (hD1 : D1For G)
    (hloc : D1Local 3 P M) (h : IsPPoint 3 P M x)
    {R : Sylow 3 (RedCent 3 x)} {K : Subgroup (RedCent 3 x)} (hRK : PPointReduced 3 M x R K)
    {i : TauCeti.CFSGIndex} (hi : PPointExcluded 3 i) (e : Nonempty (K ≃* i.Group)) : False := by
  cases hi with
  | altTwoP _ hp => omega
  | fiTwentyTwo hp => omega
  | monster hp => omega
  | @unitary d hd hn =>
    exact h.false_of_borelData h243 hS hD1 hloc hRK hn
      fun T => borelData_of_unitary hUB hUI hd e T
  | @ree d hd =>
    exact h.false_of_borelData h243 hS hD1 hloc hRK
      (by have := hd.three_le_fieldExponent; omega) fun T => borelData_of_ree hRB hRI hd e T

end Three

end CFSG.LocalAnalysis.RankFourTheoremC
