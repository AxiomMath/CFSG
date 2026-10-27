module

public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZGen
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedB
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieZNAux
import CFSG.LocalAnalysis.AGLEmbedding.ZNCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Reduced

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.pCore_le_centralizer (h : ReducedNongeneration p Y Rb Y₀)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    CFSG.pCore p Y ≤ Subgroup.centralizer (L : Set Y) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hEC : CFSG.layer Y ≤ Subgroup.centralizer (CFSG.pCore p Y : Set Y) := by
    rw [← CFSG.Fitting_eq_pcore Y p h.core_eq_bot]
    exact Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp CFSG.LocalCores.fitting_layer_commute)
  exact Subgroup.le_centralizer_iff.mp ((le_layer_of_isComponentOf hL).trans hEC)

theorem ReducedNongeneration.centralizer_le_of_pCore (h : ReducedNongeneration p Y Rb Y₀)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {z : Y} (hz : z ∈ CFSG.pCore p Y) (hzp : orderOf z = p) :
    Subgroup.centralizer (L : Set Y) ≤ Y₀ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  have : IsCyclic (CFSG.pCore p Y) := h.isCyclic_pCore_of_component hL
  obtain ⟨t, ⟨htR, htL⟩, ht, -⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot Rb hL
  have hzC : z ∈ Subgroup.centralizer (L : Set Y) := h.pCore_le_centralizer hL hz
  have hzt : z ∉ Subgroup.zpowers t := by
    intro hzt
    have hz1 := h.eq_one_of_mem_centralizer_of_isCyclic hL hcyc (Subgroup.zpowers_le.mpr htL hzt)
      hzC
    rw [hz1, orderOf_one] at hzp
    exact hp.one_lt.ne hzp
  have hzconj : ∀ g : Y, g * z * g⁻¹ ∈ Subgroup.zpowers z := fun g =>
    conj_mem_zpowers_of_isCyclic rfl hz (‹(CFSG.pCore p Y).Normal›.conj_mem z hz g)
  have hQR : Subgroup.zpowers t ⊔ Subgroup.zpowers z ≤ Rb :=
    sup_le (Subgroup.zpowers_le.mpr htR)
      (Subgroup.zpowers_le.mpr (CFSG.pCore_isPGroup.le_sylow_of_normal Rb hz))
  have hQ2 : 2 ≤ Open.pRank p (Subgroup.zpowers t ⊔ Subgroup.zpowers z) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp ht (hzp ▸ pow_orderOf_eq_one z) hzt
      (Subgroup.mem_centralizer_iff.mp hzC t htL)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hC := h.three_le_pRank_inf_centralizer_sup_zpowers ht hzp
    (fun v hv => h.conj_mem_zpowers_of_component hL hcyc ⟨htR, htL⟩ hv) fun v _ => hzconj v
  have hNQ : Subgroup.normalizer
      ((Subgroup.zpowers t ⊔ Subgroup.zpowers z : Subgroup Y) : Set Y) ≤ Y₀ :=
    (normalizer_le_weakCore p hQR hQ2 (hC.trans (pRank_mono p hp le_sup_right))).trans
      h.weakCore_le
  intro g hg
  refine hNQ (mem_normalizer_sup_zpowers ?_ (Subgroup.mem_sup_right (hzconj g)))
  rw [← Subgroup.mem_centralizer_iff.mp hg t htL, mul_inv_cancel_right]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)

end Reduced

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.inf_le_sup_of_not_mem (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hd : D1CaseTwoDataAt p P M H R Rbar)
    {L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₁ : IsComponentOf L₁ ⊤)
    (huL : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁)
    (hmeet : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥)
    {E : Subgroup G} (hED : E ≤ pCoreCentralizerPreimage p M)
    (hME : M ≤ Subgroup.normalizer (E : Set G)) {z : H} (hzR : (z : G) ∈ R)
    (hzp : orderOf z = p)
    (hzO : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      CFSG.pCore p (H ⧸ primeComplementCore (G := H) p))
    (hzE : (z : G) ∉ E) :
    E ⊓ H ≤ R ⊔ GLBPrimeCore p H := by
  have h3 := hd.toPhaseThree hAut hS hKL
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.pCore p (H ⧸ primeComplementCore (G := H) p)).Normal := CFSG.pCore_normal
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set C := Subgroup.centralizer (L₁ : Set (H ⧸ primeComplementCore (G := H) p))
  set W := ((E ⊓ H).subgroupOf H).map π
  set X₀ := ((H ⊓ M).subgroupOf H).map π
  have hL₁X₀ : ¬ L₁ ≤ X₀ := by
    obtain ⟨L, hL, hLX₀⟩ := hd.exists_not_le hAut
    rwa [huL L hL] at hLX₀
  have hiso := hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog (hAut _ _ _ _ hd.cfg.red
      hd.cfg.catalog) hS hd.cyclic hd.rank hL₁
    hL₁X₀
  have hL₁n : L₁.Normal := ⟨fun n hn g => huL _
    ((ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L₁).mpr hL₁) ▸
      (⟨n, hn, rfl⟩ : g * n * g⁻¹ ∈ L₁.map (MulAut.conj g).toMonoidHom)⟩
  have hzbR : π z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hd.cfg.rbar]
    exact Subgroup.mem_map_of_mem π (show z ∈ R.subgroupOf H from hzR)
  have hzbC : π z ∈ C := hd.cfg.red.pCore_le_centralizer hL₁ hzO
  have hzbp : orderOf (π z) = p := by
    have hdvd : orderOf (π z) ∣ p := hzp ▸ orderOf_map_dvd π z
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exfalso
      have hzN : (z : G) ∈ GLBPrimeCore p H :=
        (mk'_primeComplementCore_eq_one_iff p z).mp (orderOf_eq_one_iff.mp h1)
      have hpN := Subgroup.orderOf_dvd_natCard _ hzN
      rw [Subgroup.orderOf_coe, hzp] at hpN
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp (glbPrimeCore_coprime p H) hpN
    · exact h1
  have hCX₀ : C ≤ X₀ := hd.cfg.red.centralizer_le_of_pCore hL₁ (hd.cyclic L₁ hL₁) hzO hzbp
  have hX₀W : X₀ ≤ Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)) :=
    map_le_normalizer_map π inf_le_right ((le_inf (inf_le_right.trans hME)
      (inf_le_left.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf)
  obtain ⟨t, ⟨htV, htR, htL⟩, htp, -⟩ := exists_mem_centralizer_orderOf_eq
    (Rbar.isPGroup'.to_le (inf_le_right.trans inf_le_left)) hmeet
  have hWRC : W ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊔ C := by
    rintro _ ⟨x, hx, rfl⟩
    refine hd.cfg.red.centralizer_le_sup_of_caseTwo hKL hL₁ hiso (hd.cyclic L₁ hL₁) ⟨htR, htL⟩
      htp (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htV) ?_)
    exact mk_mem_centralizer_d1MapPCore h3.twoCore_M_le_glbPrimeCore (hED hx.1) x.2
  have hV : W ⊓ C = ⊥ := by
    by_contra hV
    have hCV : C ≤ Subgroup.normalizer ((W ⊓ C : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) p)) :=
      (le_inf (hCX₀.trans hX₀W) Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hcyc : IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ C :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
      hd.cfg.red.isCyclic_of_le_centralizer hL₁ hL₁X₀ (Rbar.isPGroup'.to_le inf_le_left)
        inf_le_right
    obtain ⟨e, he, hez⟩ := (mem_of_isCyclic_inf_of_ne_bot hd.cfg.red.core_eq_bot Rbar hcyc hzbR
      hzbC hzbp inf_le_right hCV hV).1
    have hn : (e : G)⁻¹ * z ∈ GLBPrimeCore p H :=
      (mk'_primeComplementCore_eq_one_iff p (e⁻¹ * z)).mp
        (by rw [map_mul, map_inv, hez, inv_mul_cancel])
    have hzpg : IsPGroup p (Subgroup.zpowers (z : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hzp, pow_one])
    have hze : (z : G) * ((e : G)⁻¹ * z)⁻¹ = e := by group
    have hzeE : (z : G) * ((e : G)⁻¹ * z)⁻¹ ∈ E := by
      rw [hze]
      exact he.1
    exact hzE (mem_of_mul_mem_of_coprime hzpg (glbPrimeCore_coprime p H).symm
      (h3.primeCore_le.trans hME) ((GLBPrimeCore p H).inv_mem hn) hzeE)
  have hWp : IsPGroup p W := by
    intro w
    have hw : (w : H ⧸ primeComplementCore (G := H) p) ∈
        (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊔ C :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) :
            Set (H ⧸ primeComplementCore (G := H) p)) := hWRC w.2
    rw [Subgroup.mul_normal] at hw
    obtain ⟨r, hrR, c, hcC, hrc⟩ := hw
    obtain ⟨k, hk⟩ := Rbar.isPGroup' ⟨r, hrR⟩
    have hk' : r ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hwC : (w : H ⧸ primeComplementCore (G := H) p) ^ p ^ k ∈ C := by
      have hc1 : QuotientGroup.mk' C c = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
        exact hcC
      have h1 : (w : H ⧸ primeComplementCore (G := H) p) ^ p ^ k ∈ (QuotientGroup.mk' C).ker := by
        rw [MonoidHom.mem_ker, map_pow, ← hrc, map_mul, hc1, mul_one, ← map_pow, hk', map_one]
      rwa [QuotientGroup.ker_mk'] at h1
    have hwWC : (w : H ⧸ primeComplementCore (G := H) p) ^ p ^ k ∈ W ⊓ C :=
      ⟨W.pow_mem w.2 _, hwC⟩
    rw [hV, Subgroup.mem_bot] at hwWC
    exact ⟨k, Subtype.ext hwWC⟩
  have hRX₀ : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤ X₀ := by
    rw [hd.cfg.rbar]
    exact Subgroup.map_mono (Subgroup.comap_mono h3.le_inf)
  have hWR : W ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    have h2 : IsPGroup p (W ⊔ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
      IsPGroup.to_sup_of_normal_left' hWp Rbar.isPGroup' (hRX₀.trans hX₀W)
    exact le_sup_left.trans (Rbar.is_maximal' h2 le_sup_right).le
  rintro x ⟨hxE, hxH⟩
  have hxW : π ⟨x, hxH⟩ ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
    hWR ⟨⟨x, hxH⟩, ⟨hxE, hxH⟩, rfl⟩
  rw [hd.cfg.rbar] at hxW
  obtain ⟨r, hr, hrx⟩ := hxW
  have hn : (r : G)⁻¹ * x ∈ GLBPrimeCore p H :=
    (mk'_primeComplementCore_eq_one_iff p (r⁻¹ * ⟨x, hxH⟩)).mp
      (by rw [map_mul, map_inv, hrx, inv_mul_cancel])
  have e : x = r * ((r : G)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hr hn

end Data

end CFSG.AGLEmbedding
