module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenThreeAt
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81JZeroTwoHolds
import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem AGL81CfgData.inspection (hN1 : TenThreeThree.AGL81ElevenThreeInspectionCfg G)
    (hS : Setting G) {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal)
    {R : Subgroup G} (hR : IsMaxInvariantTwoIn Q R (d1PlusCore p H K))
    (hsylJ : ¬ 2 ∣ (jZero H L ⊓ R).relIndex (jZero H L))
    (hpar : 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L)
    (hQJ : ¬ (∀ b ∈ Q, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L))) :
    p = 3 ∧ (∃ N : ℕ, 10 ≤ N ∧ Even N ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin N))) ∧
    ∃ I₀ ∈ cZero (H ⊓ L), Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* alternatingGroup (Fin 5)) := by
  have hQH : Q ≤ H := hd.le_H
  have hQM : Q ≤ M := hd.base.1
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hNHL : Q ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := fun b hb => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hQH hb)) y
    have h2 := Subgroup.mem_normalizer_iff.mp (hMn (hQM hb)) y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
  have hQT : Q ≤ Subgroup.normalizer ((jZero H L ⊓ R : Subgroup G) : Set G) :=
    (le_inf (hNHL.trans (le_normalizer_jZero H L)) hR.2.2.1).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact hN1 hS p P M H Q K hd L hL hLn Q (le_inf hQH hQM) hd.base.2.1 (jZero H L ⊓ R)
    inf_le_left (hR.2.1.to_le inf_le_right) hsylJ hQT hpar hQJ

theorem AGL81CfgData.two_dvd_relIndex_jZero_of_step (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    (h1033 : AGL81TenThreeThreeCfg G) (hXM : d1PlusCore p H K ≤ M) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal) {R : Subgroup G}
    (hR : IsMaxInvariantTwoIn Q R (d1PlusCore p H K)) (hR1 : R ≠ ⊥)
    (hstep : ¬ 2 ∣ (jZero H L ⊓ R).relIndex (jZero H L) →
      2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L →
      ¬ (∀ b ∈ Q, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) → False) :
    2 ∣ (jZero H L ⊓ R).relIndex (jZero H L) := by
  by_contra hsylJ
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hglob : AGLGlobal G := aglGlobal_of_setting hS
  have hM : GLBIsMaxTwoLocal M := hesc.maxTwoLocal_M
  obtain ⟨hCGS, hRmax⟩ := hd.star R hR hR1
  have hRX : R ≤ d1PlusCore p H K := hR.1
  have hRM : R ≤ M := hRX.trans hXM
  have hRH : R ≤ H := hRX.trans (Subgroup.map_subtype_le _)
  have hR2 : IsPGroup 2 R := hR.2.1
  have hQM : Q ≤ M := hd.base.1
  have hQH : Q ≤ H := hd.le_H
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := hRM.trans hMn
  have hOR : pCoreOf 2 M ≤ R :=
    TwoRest3A6.le_of_isMaxInvariantTwo hRmax
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
      (hRM.trans (localGroup_le_normalizer_pCoreOf 2 M))
      (hQM.trans (localGroup_le_normalizer_pCoreOf 2 M))
  have hloc := normalizer_le_of_cgs_le hCGS
  have hblock : ¬ 2 ∣ (L ⊓ R).relIndex L → False := fun hsylL =>
    hL.not_le_normalizer ((le_of_normal_block_of_local hglob hCGT hD2 hM hd.not_le hL.le hLn
      hRM hR2 hOR hRL hsylL hloc).trans (localGroup_le_normalizer_pCoreOf 2 H))
  have hNHL : ∀ B : Subgroup G, B ≤ H → B ≤ M →
      B ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := fun B hBH hBM b hb => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hBH hb)) y
    have h2 := Subgroup.mem_normalizer_iff.mp (hMn (hBM hb)) y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
  have hNO : ∀ B : Subgroup G, B ≤ H → B ≤ M →
      B ≤ Subgroup.normalizer (pCoreOf 2 (H ⊓ L) : Set G) := fun B hBH hBM =>
    (hNHL B hBH hBM).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  by_cases hpar : ¬ 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L
  ·
    refine hblock (not_two_dvd_relIndex_inf_of_parabolic_of_sylow hRmax
      ((jZero_le H L).trans inf_le_right)
      ((Subgroup.map_subtype_le _).trans inf_le_right)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
      (hNO R hRH hRM) (hNO Q hQH hQM)
      ((jZero_le H L).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) _)) hsylJ
      hpar)
  · rw [not_not] at hpar
    by_cases hQJ : ∀ b ∈ Q, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)
    · rcases h1033 hS p P M H Q K hd L hL hLn Q (le_inf hQH hQM) hd.base.2.1 hQJ with
        hc | hodd
      · exact hblock (TwoRest3A6.not_two_dvd_index_inf_of_isMaxInvariantTwo hRmax hOR hRL hc)
      · exact hodd hpar
    · exact hstep hsylJ hpar hQJ

theorem AGL81CfgData.two_dvd_relIndex_jZero_of_ne_three (hS : Setting G) {p : ℕ}
    {P : Sylow p G} {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    (h1033 : AGL81TenThreeThreeCfg G) (hN1 : TenThreeThree.AGL81ElevenThreeInspectionCfg G)
    (hp3 : p ≠ 3) (hXM : d1PlusCore p H K ≤ M) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal) {R : Subgroup G}
    (hR : IsMaxInvariantTwoIn Q R (d1PlusCore p H K)) (hR1 : R ≠ ⊥) :
    2 ∣ (jZero H L ⊓ R).relIndex (jZero H L) :=
  hd.two_dvd_relIndex_jZero_of_step hS hCGT hD2 h1033 hXM hL hLn hR hR1 fun hsylJ hpar hQJ =>
    hp3 (hd.inspection hN1 hS hL hLn hR hsylJ hpar hQJ).1

theorem AGL81CfgData.prime_dvd_card_jOne_of_two_dvd {p : ℕ} {P : Sylow p G}
    {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) (hXM : d1PlusCore p H K ≤ M) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal) {R : Subgroup G}
    (hR : IsMaxInvariantTwoIn Q R (d1PlusCore p H K)) (hR1 : R ≠ ⊥)
    (hev : 2 ∣ (jZero H L ⊓ R).relIndex (jZero H L)) :
    p ∣ Nat.card (jOne H L) := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hp : p.Prime := hesc.prime
  have hp2 : p ≠ 2 := hesc.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hpJ
  obtain ⟨-, hRmax⟩ := hd.star R hR hR1
  have hR2 : IsPGroup 2 R := hR.2.1
  have hQp : IsPGroup p Q := hd.base.2.1
  set J₀ := jZero H L with hJ₀
  have hpJ₀ : ¬ p ∣ Nat.card J₀ := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := J₀) p hdvd
    obtain ⟨k, hk⟩ := exists_two_pow_mem_jOne H L x.2
    have hxk : orderOf ((x : G) ^ (2 ^ k)) = p := by
      rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), Subgroup.orderOf_coe, hx,
        (Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)).gcd_eq_one,
        Nat.div_one]
    exact hpJ (hxk ▸ Subgroup.orderOf_dvd_natCard _ hk)
  have hQH : Q ≤ H := hd.le_H
  have hQM : Q ≤ M := hd.base.1
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hNHL : Q ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := fun b hb => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hQH hb)) y
    have h2 := Subgroup.mem_normalizer_iff.mp (hMn (hQM hb)) y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
  have hQJ₀ : Q ≤ Subgroup.normalizer (J₀ : Set G) := hNHL.trans (le_normalizer_jZero H L)
  have hRH : R ≤ H := hR.1.trans (Subgroup.map_subtype_le _)
  have hRM : R ≤ M := hR.1.trans hXM
  have hRHL : R ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := fun b hb => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hRH hb)) y
    have h2 := Subgroup.mem_normalizer_iff.mp (hMn (hRM hb)) y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
  have hRJ₀ : R ≤ Subgroup.normalizer (J₀ : Set G) := hRHL.trans (le_normalizer_jZero H L)
  set D := J₀ ⊔ R with hD
  have hQD : Q ≤ Subgroup.normalizer (D : Set G) :=
    CFSG.Goldschmidt.G310.le_normalizer_sup hQJ₀ hRmax.2.1
  have hpD : ¬ p ∣ Nat.card D := by
    intro hdvd
    have hprod := card_sup_mul_card_inf_of_le_normalizer hRJ₀
    rw [sup_comm] at hprod
    have h1 : p ∣ Nat.card R * Nat.card J₀ :=
      hprod ▸ Dvd.dvd.mul_right hdvd _
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
    · obtain ⟨n, hn⟩ := hR2.exists_card_eq
      rw [hn] at h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact hpJ₀ h
  obtain ⟨S, hSD, hRS, hQS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hp
    Nat.prime_two hQp hpD hQD le_sup_right hR2 hRmax.2.1
  have hSR : S = R := hRmax.2.2 S hSD.2.1 hQS hRS
  refine absurd hev ?_
  rw [Subgroup.relIndex, ← index_sup_eq_index_inf hRJ₀]
  obtain ⟨T, hT⟩ := (hR2.comap_subtype (K := D)).exists_le_sylow
  have hTR : (T : Subgroup D).map D.subtype = R := by
    have hRT : R ≤ (T : Subgroup D).map D.subtype := fun r hr =>
      ⟨⟨r, (le_sup_right : R ≤ D) hr⟩, hT hr, rfl⟩
    exact (hSD.2.2 _ (Subgroup.map_subtype_le _) (T.isPGroup'.map _) (hSR ▸ hRT)).trans hSR
  have hTeq : (T : Subgroup D) = R.subgroupOf D := by
    rw [← hTR]
    exact (Subgroup.comap_map_eq_self_of_injective D.subtype_injective _).symm
  rw [← hTeq]
  exact T.not_dvd_index

theorem AGL81CfgData.prime_dvd_card_jOne_of_ne_three (hS : Setting G) {p : ℕ}
    {P : Sylow p G} {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    (h1033 : AGL81TenThreeThreeCfg G) (hN1 : TenThreeThree.AGL81ElevenThreeInspectionCfg G)
    (hp3 : p ≠ 3) (hXM : d1PlusCore p H K ≤ M) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal) {R : Subgroup G}
    (hR : IsMaxInvariantTwoIn Q R (d1PlusCore p H K)) (hR1 : R ≠ ⊥) :
    p ∣ Nat.card (jOne H L) :=
  hd.prime_dvd_card_jOne_of_two_dvd hXM hL hLn hR hR1
    (hd.two_dvd_relIndex_jZero_of_ne_three hS hCGT hD2 h1033 hN1 hp3 hXM hL hLn hR hR1)

end CFSG.LocalAnalysis.RankThreeTheoremC
