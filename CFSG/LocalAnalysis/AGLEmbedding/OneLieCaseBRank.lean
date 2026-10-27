module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJ
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.Quasithin.Background.A1cRank
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Rank

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mem_centralizer_of_pRank_le {p : ℕ} (hp : p.Prime) {R₁ S : Subgroup G}
    (hle : R₁ ≤ S) (hrk : Open.pRank p S ≤ Open.pRank p R₁) {a : G} (haS : a ∈ S)
    (hac : a ∈ Subgroup.centralizer (S : Set G)) (hap : orderOf a = p) : a ∈ R₁ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra haR
  obtain ⟨E, hER, hE, hcard⟩ := pRank_attained p hp R₁
  have hac' : ∀ e ∈ E, Commute e a := fun e he =>
    Subgroup.mem_centralizer_iff.mp hac e (hle (hER he))
  obtain ⟨hE', hcard'⟩ := exists_elemAbelian_sup_zpowers hE hap hac' (fun h => haR (hER h))
  have hle' : E ⊔ Subgroup.zpowers a ≤ S :=
    sup_le (hER.trans hle) ((Subgroup.zpowers_le).mpr haS)
  have h1 : Open.pRank p R₁ + 1 ≤ Open.pRank p S :=
    le_csSup (pRank_bddAbove p hp S) ⟨_, hle', hE', by rw [hcard', hcard, pow_succ]⟩
  omega

theorem pRank_le_pRank_add_one_of_card_eq {p : ℕ} (hp : p.Prime) {R₁ R : Subgroup G}
    (hle : R₁ ≤ R) (hcard : Nat.card R = p * Nat.card R₁) :
    Open.pRank p R ≤ Open.pRank p R₁ + 1 := by
  obtain ⟨E, hER, hE, hEc⟩ := pRank_attained p hp R
  set m := Open.pRank p R
  have hR₁ : R₁.relIndex R = p := by
    have h := Subgroup.relIndex_mul_card (H := R₁) (K := R)
    rw [inf_eq_left.mpr hle, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hle1 : R₁.relIndex E ≤ p :=
    hR₁ ▸ Subgroup.relIndex_le_of_le_right hER (by rw [hR₁]; exact hp.ne_zero)
  have hmul := Subgroup.relIndex_mul_card (H := R₁) (K := E)
  rw [hEc] at hmul
  obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro _ hmul)
  have hi1 : i ≤ 1 := by
    by_contra h
    have : p ^ 2 ≤ p ^ i := Nat.pow_le_pow_right hp.pos (by omega)
    have : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  have hF : IsElemAbelian p (R₁ ⊓ E) :=
    ⟨⟨⟨fun x y => Subtype.ext <| by
      have := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, x.2.2⟩ ⟨y, y.2.2⟩)
      exact this⟩⟩, fun x hx => hE.2 x hx.2⟩
  interval_cases i
  · rw [hieq, pow_zero, one_mul] at hmul
    have : m ≤ Open.pRank p R₁ := le_csSup (pRank_bddAbove p hp R₁) ⟨_, inf_le_left, hF, hmul⟩
    omega
  · rw [hieq, pow_one] at hmul
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · omega
    · have hc : Nat.card (R₁ ⊓ E : Subgroup G) = p ^ (m - 1) := by
        have : p ^ m = p * p ^ (m - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [this] at hmul
        exact Nat.eq_of_mul_eq_mul_left hp.pos hmul
      have : m - 1 ≤ Open.pRank p R₁ :=
        le_csSup (pRank_bddAbove p hp R₁) ⟨_, inf_le_left, hF, hc⟩
      omega

end Rank

section Hom

variable {G : Type} [Group G] [Finite G]

theorem exists_competitorHom_apply_of_map_eq {p : ℕ} {H X : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hπJ : ((nclIn H X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K)
    {H₁ : Subgroup G} (hJH₁ : nclIn H X ≤ H₁) :
    ∃ φ : ((nclIn H X).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) →*
        K, Function.Surjective φ ∧ p.Coprime (Nat.card φ.ker) ∧
      ∀ (j : G) (hj : j ∈ nclIn H X),
        ((φ ⟨QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hJH₁ hj⟩,
            Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hj)⟩ : K) :
          H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H X hj⟩ := by
  have hJH : nclIn H X ≤ H := nclIn_le_self H X
  set ρ := (QuotientGroup.mk' (primeComplementCore (G := H₁) p)).subgroupMap
    ((nclIn H X).subgroupOf H₁)
  let θ₀ : (nclIn H X).subgroupOf H₁ →* H :=
    MonoidHom.codRestrict (H₁.subtype.comp ((nclIn H X).subgroupOf H₁).subtype) H
      (fun a => hJH a.2)
  let θ : (nclIn H X).subgroupOf H₁ →* H ⧸ primeComplementCore (G := H) p :=
    (QuotientGroup.mk' (primeComplementCore (G := H) p)).comp θ₀
  have hθK : ∀ a, θ a ∈ K := fun a =>
    hπJ ▸ Subgroup.mem_map_of_mem _ (show θ₀ a ∈ (nclIn H X).subgroupOf H from a.2)
  let ψ : (nclIn H X).subgroupOf H₁ →* K := θ.codRestrict K hθK
  have hψker : ∀ a, a ∈ ψ.ker ↔ ((a : H₁) : G) ∈ GLBPrimeCore p H := by
    intro a
    rw [MonoidHom.mem_ker, ← OneMemClass.coe_eq_one, MonoidHom.codRestrict_apply]
    exact mk'_primeComplementCore_eq_one_iff p (θ₀ a)
  have hψ : Function.Surjective ψ := by
    intro l
    obtain ⟨j, hj, hjl⟩ : (l : H ⧸ primeComplementCore (G := H) p) ∈
        ((nclIn H X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
      hπJ.symm ▸ l.2
    exact ⟨⟨⟨(j : G), hJH₁ hj⟩, hj⟩, Subtype.ext hjl⟩
  have hker : ρ.ker ≤ ψ.ker := by
    intro a ha
    have ha' : ((a : H₁) : G) ∈ GLBPrimeCore p H₁ := by
      rw [← mk'_primeComplementCore_eq_one_iff]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
    have hN := inf_glbPrimeCore_le_glbPrimeCore p hJH₁ ⟨a.2, ha'⟩
    rw [glbPrimeCore_nclIn] at hN
    exact (hψker a).mpr hN.2
  obtain ⟨φ, hφρ, hφs, hφker⟩ := exists_surjective_comp_eq ρ
    ((QuotientGroup.mk' _).subgroupMap_surjective _) ψ hψ hker
  refine ⟨φ, hφs, ?_, fun j hj => congrArg Subtype.val (hφρ ⟨⟨j, hJH₁ hj⟩, hj⟩)⟩
  have hι : Function.Injective (H₁.subtype.comp ((nclIn H X).subgroupOf H₁).subtype) :=
    H₁.subtype_injective.comp (Subgroup.subtype_injective _)
  refine Nat.Coprime.coprime_dvd_right ?_ ((glbPrimeCore_coprime p H).coprime_dvd_right
    (Subgroup.card_dvd_of_le (H := ψ.ker.map (H₁.subtype.comp
      ((nclIn H X).subgroupOf H₁).subtype)) ?_))
  · rw [hφker, Subgroup.card_map_of_injective hι]
    exact Subgroup.card_map_dvd _ _
  · rintro _ ⟨a, ha, rfl⟩
    exact (hψker a).mp ha

end Hom

section MemK

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.exists_sylow_of_memK (hT : KFactOneLieTorus)
    (hd : D1OneLieData p P M H R Rbar K) (hJ : D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)))
    {R₁ : Subgroup G} (hR₁R : R₁ ≤ R) (hXR₁ : d1LiftX p H R K ≤ R₁)
    (hcard : Nat.card R = p * Nat.card R₁) {H₁ : Subgroup G} (hH₁ : GLBIsMaxTwoLocal H₁)
    (hne : H₁ ≠ H) (hJH₁ : nclIn H (d1LiftX p H R K) ≤ H₁) (hR₁H₁ : R₁ ≤ H₁) :
    ∃ (P' : Sylow p G) (S : Subgroup G), D1LocalU p P' M ∧ D1Escape p P' M H₁ S ∧
      R₁ ≤ S ∧ Nat.card S ≤ p * Nat.card R₁ ∧ Open.pRank p S ≤ Open.pRank p R₁ := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hext := hd.cfg.ext
  have hXR : d1LiftX p H R K ≤ R := d1LiftX_le p H R K
  have hXH₁ : d1LiftX p H R K ≤ H₁ := (le_nclIn (d1LiftX_le_H p H R K)).trans hJH₁
  have hR₁M : R₁ ≤ M := hR₁R.trans hext.le_M
  have hX3 := hd.three_le_pRank_d1LiftX hT
  have hH₁M : ¬ H₁ ≤ M := hd.not_le_of_nclIn_le hJH₁
  have hrank : 3 ≤ Open.pRank p (H₁ ⊓ M) :=
    hX3.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp
      (le_inf hXH₁ (hXR.trans hext.le_M)))
  obtain ⟨T, hTM, -, -⟩ := intersecting_local_has_contained_sylow p hp P hext.sylow_le
    hext.weakCore_le hrank
  have hR₁p : IsPGroup p R₁ := hext.isPGroup.to_le hR₁R
  obtain ⟨S, hS⟩ := (hR₁p.comap_subtype (K := H₁ ⊓ M)).exists_le_sylow
  set R' : Subgroup G := (S : Subgroup ↥(H₁ ⊓ M)).map (H₁ ⊓ M).subtype with hR'def
  have hR₁R' : R₁ ≤ R' := by
    rw [hR'def, ← Subgroup.map_subgroupOf_eq_of_le (le_inf hR₁H₁ hR₁M)]
    exact Subgroup.map_mono hS
  have hR'HM : R' ≤ H₁ ⊓ M := Subgroup.map_subtype_le _
  have hR'p : IsPGroup p R' := S.isPGroup'.map _
  obtain ⟨S', hS'⟩ := (hR'p.comap_subtype (K := H₁)).exists_le_sylow
  have hR'S' : R' ≤ (S' : Subgroup H₁).map H₁.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (hR'HM.trans inf_le_left)]
    exact Subgroup.map_mono hS'
  have hS'eq : (S' : Subgroup H₁).map H₁.subtype = R' := by
    refine (Subgroup.eq_of_le_of_card_ge hR'S' ?_).symm
    rw [Subgroup.card_map_of_injective H₁.subtype_injective, S'.card_eq_multiplicity,
      ← T.card_eq_multiplicity, ← Subgroup.card_map_of_injective H₁.subtype_injective]
    exact card_le_card_map_sylow S (T.isPGroup'.map _) (le_inf (Subgroup.map_subtype_le _) hTM)
  have hle : Nat.card R' ≤ Nat.card R := hext.extremal H₁ hH₁.1 hH₁M hrank R' hR'HM hR'p
  have hrk : Open.pRank p R' ≤ Open.pRank p R₁ := by
    rcases hle.lt_or_eq with hlt | heq
    ·
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hR₁R'
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR'p
      obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp (hn ▸ Dvd.intro_left _ hk.symm)
      have hpos : 0 < Nat.card R₁ := Nat.card_pos
      have hj : j = 0 := by
        by_contra hj0
        have : p ≤ p ^ j := Nat.le_self_pow hj0 p
        have : p * Nat.card R₁ ≤ Nat.card R₁ * p ^ j := by nlinarith
        omega
      subst hj
      have : R' = R₁ := (Subgroup.eq_of_le_of_card_ge hR₁R' (by rw [hk, pow_zero, mul_one])).symm
      rw [this]
    · have hlt : Open.pRank p R' < Open.pRank p R := by
        by_contra hge
        exact hne (hJ H₁ hH₁ hJH₁ R' (hR'HM.trans inf_le_left) hR'p heq.ge (not_lt.mp hge))
      have := pRank_le_pRank_add_one_of_card_eq hp hR₁R hcard
      omega
  obtain ⟨c, hc⟩ := exists_conjugate_le_sylow_of_le p P hext.sylow_le
    (hR'HM.trans inf_le_right) hR'p
  have hm : (c : G)⁻¹ ∈ M := M.inv_mem c.2
  have hloc' : D1LocalU p ((c : G)⁻¹ • P) M := hd.cfg.loc.conj hm
  have hR'P' : R' ≤ (((c : G)⁻¹ • P : Sylow p G) : Subgroup G) := by
    rw [coe_smul_sylow_eq_map_conj]
    intro x hx
    refine ⟨(MulAut.conj (c : G)).toMonoidHom x, hc ⟨x, hx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hP'M : (((c : G)⁻¹ • P : Sylow p G) : Subgroup G) ≤ M := by
    rw [coe_smul_sylow_eq_map_conj]
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hext.sylow_le hx)) (M.inv_mem hm)
  refine ⟨(c : G)⁻¹ • P, R', hloc', ?_, hR₁R', hle.trans hcard.le, hrk⟩
  exact
    { prime := hp
      ne_two := hext.ne_two
      sylow_le := hP'M
      weakCore_le := hloc'.core
      maxTwoLocal_M := hext.maxTwoLocal_M
      maxTwoLocal_H := hH₁
      le_H := hR'HM.trans inf_le_left
      le_P := hR'P'
      isSylow := ⟨S', hS'eq⟩
      three_le_pRank := hX3.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp
        (hXR₁.trans hR₁R'))
      not_le := hH₁M }

theorem D1OneLieData.eq_one_of_commutator_le (hd : D1OneLieData p P M H R Rbar K)
    {R₁ H₁ : Subgroup G} (hR₁R : R₁ ≤ R) (hR₁N : R₁ ⊓ d1PlusCore p H K = ⊥)
    (hJH₁ : nclIn H (d1LiftX p H R K) ≤ H₁) {a : G} (ha : a ∈ R₁)
    (hc : ∀ j ∈ nclIn H (d1LiftX p H R K), a * j * a⁻¹ * j⁻¹ ∈ GLBPrimeCore p H₁) :
    a = 1 := by
  set X := d1LiftX p H R K with hXdef
  set J := nclIn H X with hJdef
  have haH : a ∈ H := hd.cfg.ext.le_H (hR₁R ha)
  have hJH : J ≤ H := nclIn_le_self H X
  have hHJ : H ≤ Subgroup.normalizer (J : Set G) := le_normalizer_nclIn H X
  have hcH : ∀ j ∈ J, a * j * a⁻¹ * j⁻¹ ∈ GLBPrimeCore p H := by
    intro j hj
    have hcJ : a * j * a⁻¹ * j⁻¹ ∈ J :=
      J.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHJ haH) j).mp hj) (J.inv_mem hj)
    have h1 := inf_glbPrimeCore_le_glbPrimeCore p hJH₁ ⟨hcJ, hc j hj⟩
    rw [glbPrimeCore_nclIn p H X] at h1
    exact h1.2
  set mk := QuotientGroup.mk' (primeComplementCore (G := H) p) with hmk
  have hJK : ((J.subgroupOf H).map mk) = K := hd.map_nclIn_eq le_rfl hd.d1LiftX_ne_bot
  have hcent : mk ⟨a, haH⟩ ∈
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [← hJK] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    have hjJ : (j : G) ∈ J := hj
    have hmem : (⟨a, haH⟩ * j * (⟨a, haH⟩ : H)⁻¹ * j⁻¹ : H) ∈
        primeComplementCore (G := H) p := by
      rw [← glbPrimeCore_subgroupOf p H]
      exact hcH j hjJ
    have h1 : mk (⟨a, haH⟩ * j * (⟨a, haH⟩ : H)⁻¹ * j⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc mk j * mk ⟨a, haH⟩
        = mk ⟨a, haH⟩ * mk j * (mk ⟨a, haH⟩)⁻¹ * (mk j)⁻¹ * (mk j * mk ⟨a, haH⟩) := by
          rw [h1, one_mul]
      _ = mk ⟨a, haH⟩ * mk j := by group
  have haN : a ∈ d1PlusCore p H K := ⟨⟨a, haH⟩, hcent, rfl⟩
  have : a ∈ R₁ ⊓ d1PlusCore p H K := ⟨ha, haN⟩
  rwa [hR₁N, Subgroup.mem_bot] at this

end MemK

end CFSG.AGLEmbedding
