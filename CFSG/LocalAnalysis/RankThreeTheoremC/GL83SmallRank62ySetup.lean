module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeRankTwo
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sr629_le_of_forall_inf_centralizer_le_plane {p : ℕ} (hp : p.Prime) {B R O : Subgroup G}
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

theorem sr629_coprime_card_of_isPGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup G} (hR : IsPGroup 2 R) : p.Coprime (Nat.card R) := by
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)

omit [Finite G] in
theorem sr629_not_mem_of_isPGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup G}
    (hR : IsPGroup 2 R) {z : G} (hz1 : z ≠ 1) (hzp : z ^ p = 1) : z ∉ R := by
  intro hzR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hR ⟨z, hzR⟩
  have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : p ∣ 2 ^ k := orderOf_eq_prime hzp hz1 ▸ orderOf_dvd_of_pow_eq_one hk'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

theorem sr629_centralizer_singleton_le_of_mem_zpowers {p : ℕ} (hp : p.Prime) {z y : G}
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

theorem sr629_commutator_pCoreOf_inf_centralizer_ne_bot (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) :
    ⁅zpowers z, pCoreOf 2 M ⊓ centralizer ({x} : Set G)⁆ ≠ ⊥ := by
  have hp : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  have hp2 : p ≠ 2 := sigmaA_odd p hsit.mem_sigmaA
  have hB := SmallRankPlane.of_situation hS hsit hx hz
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  intro hbot
  have hxz : zpowers z ≤ centralizer ((pCoreOf 2 M ⊓ centralizer ({x} : Set G) : Subgroup G) :
      Set G) := commutator_eq_bot_iff_le_centralizer.mp hbot
  have hO2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMO : M ≤ normalizer (pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hBM : zpowers x ⊔ zpowers z ≤ M := hB.isIsolatedPlane.1.trans hPM
  have hOz : pCoreOf 2 M ≤ centralizer ({z} : Set G) := by
    refine sr629_le_of_forall_inf_centralizer_le_plane hp hB.isElemAbelian hB.card_eq
      (hBM.trans hMO) (sr629_coprime_card_of_isPGroup_two hp hp2 hO2) fun y hy hy1 => ?_
    by_cases hyz : y ∈ zpowers z
    · exact inf_le_right.trans
        (sr629_centralizer_singleton_le_of_mem_zpowers hp hz.ne_one hz.pow_eq_one hyz hy1)
    · obtain ⟨g, hg, hgx⟩ := exists_mem_normalizer_conj_zpowers hS hsit hx hz hy hyz
      have hgM : g ∈ M := hPM hg.1
      have hgO : g ∈ normalizer (pCoreOf 2 M : Set G) := hMO hgM
      have hgxy : g * x * g⁻¹ ∈ zpowers y := hgx ▸ ⟨x, mem_zpowers x, rfl⟩
      rintro w ⟨hwO, hwy⟩
      have hwy' : w * y = y * w := mem_centralizer_singleton_iff.mp hwy
      have hw'O : g⁻¹ * w * g ∈ pCoreOf 2 M := by
        simpa using (mem_normalizer_iff.mp (inv_mem hgO) w).mp hwO
      have hwgx : w * (g * x * g⁻¹) = g * x * g⁻¹ * w := by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hgxy
        rw [← hk]
        exact (Commute.zpow_right hwy' k).eq
      have hw'x : x * (g⁻¹ * w * g) = g⁻¹ * w * g * x := by
        calc x * (g⁻¹ * w * g) = g⁻¹ * (g * x * g⁻¹ * w) * g := by group
          _ = g⁻¹ * (w * (g * x * g⁻¹)) * g := by rw [hwgx]
          _ = g⁻¹ * w * g * x := by group
      have hzw' : g⁻¹ * w * g * z = z * (g⁻¹ * w * g) :=
        mem_centralizer_iff.mp (hxz (mem_zpowers z)) _
          ⟨hw'O, mem_centralizer_singleton_iff.mpr hw'x.symm⟩
      have hgz : g * z = z * g := mem_centralizer_iff.mp hz.centralizes g hg.1
      rw [mem_centralizer_singleton_iff]
      have hgz' : g⁻¹ * z = z * g⁻¹ := by
        have h1 : g⁻¹ * (g * z) * g⁻¹ = g⁻¹ * (z * g) * g⁻¹ := by rw [hgz]
        exact (by simpa [mul_assoc] using h1 : z * g⁻¹ = g⁻¹ * z).symm
      calc w * z = g * (g⁻¹ * w * g) * (g⁻¹ * z) := by group
        _ = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by rw [hgz']; group
        _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [hzw']
        _ = (g * z) * (g⁻¹ * w * g) * g⁻¹ := by group
        _ = z * g * (g⁻¹ * w * g) * g⁻¹ := by rw [hgz]
        _ = z * w := by group
  have hzM : z ∈ M := hPM hz.mem
  have hzC : z ∈ centralizer (pCoreOf 2 M : Set G) := by
    rw [mem_centralizer_iff]
    intro r hr
    exact mem_centralizer_singleton_iff.mp (hOz hr)
  exact sr629_not_mem_of_isPGroup_two hp hp2 hO2 hz.ne_one hz.pow_eq_one
    (hS.charTwo M hsit.isCoreMaxLocal.1.1 ⟨hzM, hzC⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC
