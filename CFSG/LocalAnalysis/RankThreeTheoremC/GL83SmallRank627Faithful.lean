module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeRankTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem le_of_forall_inf_centralizer_le_plane {p : ℕ} (hp : p.Prime) {B R O : Subgroup G}
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) (hBR : B ≤ normalizer (R : Set G))
    (hcop : p.Coprime (Nat.card R))
    (h : ∀ y ∈ B, y ≠ 1 → R ⊓ centralizer ({y} : Set G) ≤ O) : R ≤ O := by
  obtain ⟨φ, hinj, hrange⟩ :=
    elementary_rank_two_has_coordinate_embedding p hp B hB 2 hBc le_rfl
  refine embedded_rank_two_signalizer_le_of_line_centralizers p hp φ R O (hrange.trans hBR)
    hcop fun v hv => ?_
  have hmem : φ (Multiplicative.ofAdd v) ∈ (φ.comp (coordinatePairLineHom v)).range :=
    ⟨Multiplicative.ofAdd 1, by simp [coordinatePairLineHom]⟩
  have hne : φ (Multiplicative.ofAdd v) ≠ 1 := fun h1 =>
    hv (by simpa using hinj (h1.trans (map_one φ).symm))
  exact (inf_le_inf_left R (centralizer_le (Set.singleton_subset_iff.mpr hmem))).trans
    (h _ (hrange ⟨_, rfl⟩) hne)

private theorem coprime_card_of_isPGroup_two' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup G} (hR : IsPGroup 2 R) : p.Coprime (Nat.card R) := by
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)

omit [Finite G] in
private theorem not_mem_of_isPGroup_two' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup G}
    (hR : IsPGroup 2 R) {z : G} (hz1 : z ≠ 1) (hzp : z ^ p = 1) : z ∉ R := by
  intro hzR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hR ⟨z, hzR⟩
  have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : p ∣ 2 ^ k := orderOf_eq_prime hzp hz1 ▸ orderOf_dvd_of_pow_eq_one hk'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

private theorem centralizer_singleton_le_of_mem_zpowers' {p : ℕ} (hp : p.Prime) {z y : G}
    (hz1 : z ≠ 1) (hzp : z ^ p = 1) (hy : y ∈ zpowers z) (hy1 : y ≠ 1) :
    centralizer ({y} : Set G) ≤ centralizer ({z} : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hyp : y ^ p = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzp, one_zpow]
  have heq : zpowers y = zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hy) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hzp hz1, orderOf_eq_prime hyp hy1]
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (heq ▸ mem_zpowers z : z ∈ zpowers y)
  intro v hv
  rw [mem_centralizer_singleton_iff] at hv ⊢
  exact hk ▸ (Commute.zpow_right hv k).eq

omit [Finite G] in
private theorem le_normalizer_pCoreOf (H : Subgroup G) :
    H ≤ normalizer (pCoreOf 2 H : Set G) := by
  have hn : ((pCoreOf 2 H).subgroupOf H).Normal :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 H H le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  exact le_normalizer_of_normal_subgroupOf (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 H)

theorem exists_mem_inf_centralizer_not_commute (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {T : Subgroup G} (hT : SmallRankSylowTwo P M T) :
    ∃ v ∈ T ⊓ centralizer ({x} : Set G), z * v ≠ v * z := by
  have hp : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  have hp2 : p ≠ 2 := sigmaA_odd p hsit.mem_sigmaA
  have hB := SmallRankPlane.of_situation hS hsit hx hz
  by_contra hcon
  push Not at hcon
  have hTz : T ≤ centralizer ({z} : Set G) := by
    refine le_of_forall_inf_centralizer_le_plane hp hB.isElemAbelian hB.card_eq
      (hB.isIsolatedPlane.1.trans hT.normalized) (coprime_card_of_isPGroup_two' hp hp2 hT.isPGroup)
      fun y hy hy1 => ?_
    by_cases hyz : y ∈ zpowers z
    · exact inf_le_right.trans
        (centralizer_singleton_le_of_mem_zpowers' hp hz.ne_one hz.pow_eq_one hyz hy1)
    · obtain ⟨g, hg, hgx⟩ := exists_mem_normalizer_conj_zpowers hS hsit hx hz hy hyz
      have hgP : g ∈ normalizer (T : Set G) := hT.normalized hg.1
      have hgz : g ∈ normalizer ((zpowers z : Subgroup G) : Set G) :=
        normalizer_plane_le_normalizer_zpowers hS hsit hx hz hg.2
      have hgxy : g * x * g⁻¹ ∈ zpowers y := hgx ▸ ⟨x, mem_zpowers x, rfl⟩
      rintro v ⟨hvT, hvy⟩
      have hvy' : v * y = y * v := mem_centralizer_singleton_iff.mp hvy
      have huT : g⁻¹ * v * g ∈ T := by
        simpa using (mem_normalizer_iff.mp (inv_mem hgP) v).mp hvT
      have hvgx : v * (g * x * g⁻¹) = g * x * g⁻¹ * v := by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hgxy
        rw [← hk]
        exact (Commute.zpow_right hvy' k).eq
      have hux : x * (g⁻¹ * v * g) = g⁻¹ * v * g * x := by
        calc x * (g⁻¹ * v * g) = g⁻¹ * (g * x * g⁻¹ * v) * g := by group
          _ = g⁻¹ * (v * (g * x * g⁻¹)) * g := by rw [hvgx]
          _ = g⁻¹ * v * g * x := by group
      have hcomm : z * (g⁻¹ * v * g) = g⁻¹ * v * g * z :=
        hcon _ ⟨huT, mem_centralizer_singleton_iff.mpr hux.symm⟩
      have hzg : g⁻¹ * z * g ∈ zpowers z := by
        simpa using (mem_normalizer_iff.mp (inv_mem hgz) z).mp (mem_zpowers z)
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hzg
      have hcomm' : g⁻¹ * z * g * (g⁻¹ * v * g) = g⁻¹ * v * g * (g⁻¹ * z * g) := by
        rw [← hk]
        exact (Commute.zpow_left (show Commute z (g⁻¹ * v * g) from hcomm) k).eq
      rw [mem_centralizer_singleton_iff]
      symm
      calc z * v = g * (g⁻¹ * z * g * (g⁻¹ * v * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * v * g * (g⁻¹ * z * g)) * g⁻¹ := by rw [hcomm']
        _ = v * z := by group
  have hN2 : IsPGroup 2 (pCoreOf 2 M) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 M
  have hNM : pCoreOf 2 M ≤ M := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 M
  have hMN : M ≤ normalizer (pCoreOf 2 M : Set G) := le_normalizer_pCoreOf M
  have hKM : rankThreePrimeCore p M ≤ M := sSup_le fun _ hK => hK.1
  have hNK : pCoreOf 2 M ≤ rankThreePrimeCore p M :=
    le_sSup ⟨hNM, normal_subgroupOf_of_le_normalizer hMN,
      coprime_card_of_isPGroup_two' hp hp2 hN2⟩
  have hNT : pCoreOf 2 M ≤ T := by
    have hTK : IsPGroup 2 (T.subgroupOf (rankThreePrimeCore p M)) :=
      hT.isPGroup.of_equiv (subgroupOfEquivOfLe hT.le_core).symm
    have : (pCoreOf 2 M |>.subgroupOf (rankThreePrimeCore p M)).Normal :=
      normal_subgroupOf_of_le_normalizer (hKM.trans hMN)
    have hle := (hN2.of_equiv (subgroupOfEquivOfLe hNK).symm).le_sylow_of_normal
      (hTK.toSylow hT.index_odd)
    intro n hn
    have hmem : (⟨n, hNK hn⟩ : rankThreePrimeCore p M) ∈
        (pCoreOf 2 M).subgroupOf (rankThreePrimeCore p M) := mem_subgroupOf.mpr hn
    exact mem_subgroupOf.mp (hle hmem)
  have hzM : z ∈ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1 hz.mem
  have hzC : z ∈ centralizer (pCoreOf 2 M : Set G) := by
    rw [mem_centralizer_iff]
    intro r hr
    exact mem_centralizer_singleton_iff.mp (hTz (hNT hr))
  exact not_mem_of_isPGroup_two' hp hp2 hN2 hz.ne_one hz.pow_eq_one
    (hS.charTwo M hsit.isCoreMaxLocal.1.1 ⟨hzM, hzC⟩)

theorem exists_pCoreOf_inf_centralizer_ne_bot (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {H : Subgroup G} (hH : IsTwoLocal H)
    (hBH : zpowers x ⊔ zpowers z ≤ H) :
    ∃ y ∈ zpowers x ⊔ zpowers z, y ∉ zpowers z ∧ pCoreOf 2 H ⊓ centralizer ({y} : Set G) ≠ ⊥ := by
  have hp : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  have hp2 : p ≠ 2 := sigmaA_odd p hsit.mem_sigmaA
  have hB := SmallRankPlane.of_situation hS hsit hx hz
  by_contra hcon
  push Not at hcon
  have hR2 : IsPGroup 2 (pCoreOf 2 H) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 H
  have hRz : pCoreOf 2 H ≤ centralizer ({z} : Set G) := by
    refine le_of_forall_inf_centralizer_le_plane hp hB.isElemAbelian hB.card_eq
      (hBH.trans (le_normalizer_pCoreOf H)) (coprime_card_of_isPGroup_two' hp hp2 hR2)
      fun y hy hy1 => ?_
    by_cases hyz : y ∈ zpowers z
    · exact inf_le_right.trans
        (centralizer_singleton_le_of_mem_zpowers' hp hz.ne_one hz.pow_eq_one hyz hy1)
    · rw [hcon y hy hyz]
      exact bot_le
  have hzC : z ∈ centralizer (pCoreOf 2 H : Set G) := by
    rw [mem_centralizer_iff]
    intro r hr
    exact mem_centralizer_singleton_iff.mp (hRz hr)
  exact not_mem_of_isPGroup_two' hp hp2 hR2 hz.ne_one hz.pow_eq_one
    (hS.charTwo H hH ⟨hBH (mem_sup_right (mem_zpowers z)), hzC⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC
