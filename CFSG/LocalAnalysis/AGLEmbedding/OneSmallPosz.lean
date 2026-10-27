module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Posz

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.posz_mem (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K) (hV0 : d1MapPCore p M H ≠ ⊥)
    (hVC : d1MapPCore p M H ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    {z : G} (hz : D1SmallCZElt p H R K z) :
    z ∈ Subgroup.centralizer (P : Set G) ∧ z ∈ pCorePreimage p M ∧
      ¬ Subgroup.centralizer ({z} : Set G) ≤ M := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hO := primeComplementCore_coprime (G := H) p
  obtain ⟨zb, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨-, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  have hRC : IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) : Subgroup _) :=
    hd.cfg.red.isCyclic_of_le_centralizer hd.comp hKX₀ (Rbar.isPGroup'.to_le inf_le_left)
      inf_le_right
  have hcyc : IsCyclic (d1MapPCore p M H) := Subgroup.isCyclic_of_le hVC
  have hheq := h3.d1MapPCore_eq h84 hD2
  have hXp : IsPGroup p (R ⊓ pCorePreimage p M : Subgroup G) :=
    hd.cfg.ext.isPGroup.to_le inf_le_left
  have hX1 : R ⊓ pCorePreimage p M ≠ ⊥ := by
    intro hbot
    apply hV0
    rw [hheq, hbot, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  obtain ⟨e₀, he₀⟩ : ∃ x : (R ⊓ pCorePreimage p M : Subgroup G), orderOf x = p := by
    refine exists_prime_orderOf_dvd_card' p ?_
    rcases hXp.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hX1
    · exact h1
  have heX : (e₀ : G) ∈ R ⊓ pCorePreimage p M := e₀.2
  have hep : orderOf (e₀ : G) = p := (Subgroup.orderOf_coe e₀).trans he₀
  set e : H := ⟨e₀, hd.cfg.ext.le_H heX.1⟩
  have heH : orderOf e = p := (Subgroup.orderOf_coe e).symm.trans hep
  have hemp : orderOf (QuotientGroup.mk' (primeComplementCore (G := H) p) e) = p :=
    orderOf_mk_of_coprime hp _ hO heH
  have hemV : QuotientGroup.mk' (primeComplementCore (G := H) p) e ∈ d1MapPCore p M H :=
    Subgroup.mem_map_of_mem _ (show e ∈ (pCorePreimage p M).subgroupOf H from heX.2)
  have hΩ : ∀ v ∈ d1MapPCore p M H, v ^ p = 1 →
      v ∈ Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) e) := by
    intro v hv hvp
    by_cases hv1 : v = 1
    · rw [hv1]
      exact Subgroup.one_mem _
    · exact mem_zpowers_of_orderOf_eq_of_isCyclic hv hemV
        (by rw [orderOf_eq_prime hvp hv1, hemp])
  have hK1 : ∀ y ∈ pCorePreimage p M, y ^ p = 1 →
      ∃ k : ℤ, ((e : G) ^ k)⁻¹ * y ∈ pCoreOf 2 M := fun y hy hyp =>
    h3.exists_zpow_inv_mul_mem_twoCore h84 hD2 heX.2 hΩ hy (hyp ▸ (pCoreOf 2 M).one_mem)
  have hcen := mem_centralizer_of_forall_exists_zpow hp hp2 P.isPGroup' hd.cfg.ext.sylow_le
    (hd.cfg.ext.le_P heX.1) heX.2 hep hK1
  have hCM := hd.centralizer_not_le hz
  obtain ⟨hzR', hzp', hzH, hzC⟩ := hz
  have hzRb : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ ∈
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hd.cfg.rbar]
    exact Subgroup.mem_map_of_mem _ (show (⟨z, hzH⟩ : H) ∈ R.subgroupOf H from hzR')
  have hzmp : orderOf (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩) = p :=
    orderOf_mk_of_coprime hp _ hO ((Subgroup.orderOf_coe _).symm.trans hzp')
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_orderOf_eq_of_isCyclic
    (Z := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    ⟨hzRb, hzC⟩ (hVC hemV) (by rw [hzmp, hemp]))
  have hzk : (⟨z, hzH⟩ : H) = e ^ k := by
    have h1 : (e ^ k)⁻¹ * ⟨z, hzH⟩ ∈ primeComplementCore (G := H) p := by
      rw [← QuotientGroup.ker_mk' (primeComplementCore (G := H) p), MonoidHom.mem_ker,
        map_mul, map_inv, map_zpow, hk, inv_mul_cancel]
    have hRH : IsPGroup p (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
    have h2 : (e ^ k)⁻¹ * ⟨z, hzH⟩ ∈ R.subgroupOf H :=
      (R.subgroupOf H).mul_mem ((R.subgroupOf H).inv_mem ((R.subgroupOf H).zpow_mem
        (show e ∈ R.subgroupOf H from heX.1) k)) hzR'
    have hdisj : Disjoint (R.subgroupOf H) (primeComplementCore (G := H) p) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hRH
      exact Subgroup.disjoint_of_coprime_natCard (by rw [hn]; exact hO.pow_left n)
    have h3' := Subgroup.disjoint_def.mp hdisj h2 h1
    rw [inv_mul_eq_one] at h3'
    exact h3'.symm
  have hzG : z = (e : G) ^ k := by
    have := congrArg Subtype.val hzk
    simpa using this
  refine ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_, ?_, hCM⟩
  · rw [hzG]
    have hc : Commute x (e : G) := Subgroup.mem_centralizer_iff.mp hcen x hx
    exact (hc.zpow_right k).eq
  · rw [hzG]
    exact (pCorePreimage p M).zpow_mem heX.2 k

theorem D1OneSmallData.czSP_of_le (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K) (hV0 : d1MapPCore p M H ≠ ⊥)
    (hVC : d1MapPCore p M H ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    {z : G} (hz : D1SmallCZElt p H R K z) : D1CzSP p z := by
  obtain ⟨hzP, -, -⟩ := hd.posz_mem h3 h84 hD2 hV0 hVC hz
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzP x hx)
  exact (betaFour_all_sylows_rank_ge_four hd.cfg.loc.beta P).trans
    (PreuniquenessRankFour.Helpers.pRank_mono p hd.cfg.red.prime hPC)

theorem D1OneSmallData.d1MapPCore_le_inf_centralizer (hKS : KFactOneSmall)
    (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) (hL : ¬ (p = 3 ∧ IsLinThreeFour K))
    (hF : ¬ (p = 5 ∧ IsFi22 K)) (hVK : d1MapPCore p M H ⊓ K = ⊥) :
    d1MapPCore p M H ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
  obtain ⟨T₁, hT₁, hF'⟩ := hd.oneSmallFacts hKS hL hF
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨hWp, hWR, hWn, -, -⟩ := hd.d1MapPCore_facts h3 h84 hD2
  obtain ⟨T₀, hT₀N, hT₀p, hT₀C⟩ := hF'.torus
  exact le_inf_centralizer_of_torus hd.cfg.red.prime T₁ hT₁ T₀ hT₀N hT₀p hT₀C hWp
    (le_sup_of_oneSmallFacts T₁ hT₁ hF' hWp hWR hWn) hWn hVK hWR

theorem D1OneSmallData.d1MapPCore_le_inf_centralizer_l34 (hK5 : KFactL34Local)
    (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) (hL34 : p = 3 ∧ IsLinThreeFour K)
    (hR : ¬ D1SmallOuterR p H Rbar K) (hVK : d1MapPCore p M H ⊓ K = ⊥) :
    d1MapPCore p M H ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨T₁, hT₁, -, -, -, -, -, -⟩ := hd.exists_sylow
  obtain ⟨hWp, hWR, hWn, -, -⟩ := hd.d1MapPCore_facts h3 h84 hD2
  have hRK : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
      K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) :=
    not_not.mp hR
  have hle := le_inf_sup_inf_centralizer hd.center T₁ hT₁ hWp hWR (hWR.trans hRK)
  obtain ⟨hp3, hL⟩ := hL34
  subst hp3
  obtain ⟨⟨T₀, hT₀N, hT₀p, hT₀C⟩, -⟩ := hK5 K hL T₁
  exact le_inf_centralizer_of_torus hp T₁ hT₁ T₀ hT₀N hT₀p hT₀C hWp hle hWn hVK hWR

theorem D1OneSmallData.phaseThree_and_le_of_posz (hUP : KFactUPrimeSmall)
    (hUE : KFactUPrimeExc) (hKS : KFactOneSmall) (hK5 : KFactL34Local) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K) (hLa : D1SmallLa p M H Rbar K)
    (hF : ¬ (p = 5 ∧ IsFi22 K)) (hVK : d1MapPCore p M H ⊓ K = ⊥) :
    D1PhaseThree p P M H R ∧ d1MapPCore p M H ≤
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
  by_cases hL : p = 3 ∧ IsLinThreeFour K
  · have h3 := hd.toPhaseThree_of_exc hUE (Or.inl hL) (hLa hL.1 hL.2).2
    exact ⟨h3, hd.d1MapPCore_le_inf_centralizer_l34 hK5 h3 h84 hD2 hL (hLa hL.1 hL.2).1 hVK⟩
  · have h3 := hd.toPhaseThree hUP hL hF
    exact ⟨h3, hd.d1MapPCore_le_inf_centralizer hKS h3 h84 hD2 hL hF hVK⟩

end Posz

theorem stmtSmallPoszSP_of (hUP : KFactUPrimeSmall) (hUE : KFactUPrimeExc)
    (hKS : KFactOneSmall) (hK5 : KFactL34Local) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) :
    StmtSmallPoszSP := by
  intro G _ _ p P M H R Rbar K hd hLa hF hV0 hVK z hz
  obtain ⟨h3, hVC⟩ := hd.phaseThree_and_le_of_posz hUP hUE hKS hK5 h84 hD2 hLa hF hVK
  exact hd.czSP_of_le h3 h84 hD2 hV0 hVC hz

end CFSG.AGLEmbedding
