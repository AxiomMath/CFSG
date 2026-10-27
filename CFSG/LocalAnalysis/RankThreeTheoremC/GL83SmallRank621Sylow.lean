module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

local notation "W₃" => Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

omit [Finite G] in
private theorem sylow621_card_eq_eighty_one {P : Subgroup G} (e : P ≃* W₃) : Nat.card P = 81 := by
  have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by simp
  rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, h3]
  norm_num

private theorem sylow621_le_maximal (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) : (P : Subgroup G) ≤ M :=
  (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1

private theorem sylow621_plane (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) : SmallRankPlane 3 (P : Subgroup G) x z :=
  smallRankPlane_of_largeObstruction_empty hS hsit.mem_sigmaA hsit.isCoreMaxLocal
    hsit.largeObstruction_empty hx.mem hx.ne_one hx.pow_eq_one hx.not_centralizer_le hz.mem
    hz.centralizes hz.ne_one hz.pow_eq_one

private theorem sylow621_le_core (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) (hsolv : Group.IsSolvable M) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {S : Subgroup G}
    (hSB : IsTwoInvariantIn (zpowers x ⊔ zpowers z) M S) : S ≤ GLBPrimeCore 3 M := by
  have hpl := sylow621_plane hS hsit hx hz
  have hB3 : IsPGroup 3 (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hBM : zpowers x ⊔ zpowers z ≤ M :=
    (sup_le (zpowers_le.mpr hx.mem) (zpowers_le.mpr hz.mem)).trans (sylow621_le_maximal hS hsit)
  obtain ⟨hSM, hS2, hBS⟩ := hSB
  have hS3 : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have : Group.IsSolvable M := hsolv
  exact CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains Nat.prime_three (by norm_num)
    (solvable_hasPrimeConstraint (G := M) 3 Nat.prime_three) hB3 hBM
    (fun y _ hyB hord => hpl.mem_of_mem_centralizer y hyB (by
      rw [← hord]
      exact pow_orderOf_eq_one y)) hSM hS3 hBS

private theorem sylow621_exists_conj (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) (hsolv : Group.IsSolvable M) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {S : Subgroup G}
    (hSB : IsTwoInvariantIn (zpowers x ⊔ zpowers z) M S) :
    ∃ (T : Subgroup G) (c : G), S ≤ T ∧ IsPGroup 2 T ∧ c ∈ GLBPrimeCore 3 M ∧
      c ∈ centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ∧
      (P : Subgroup G).map (MulAut.conj c).toMonoidHom ≤ normalizer (T : Set G) := by
  set B : Subgroup G := zpowers x ⊔ zpowers z
  set D : Subgroup G := GLBPrimeCore 3 M
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (sylow621_plane hS hsit hx hz).card_eq
  have hPM := sylow621_le_maximal hS hsit
  have hBP : B ≤ (P : Subgroup G) := sup_le (zpowers_le.mpr hx.mem) (zpowers_le.mpr hz.mem)
  have hSD : S ≤ D := sylow621_le_core hS hsit hsolv hx hz hSB
  obtain ⟨-, hS2, hBS⟩ := hSB
  have hD3 : ¬ 3 ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (CFSG.AGLEmbedding.glbPrimeCore_coprime 3 M)
  have hBD : B ≤ normalizer (D : Set G) :=
    (hBP.trans hPM).trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 M)
  have hPD : (P : Subgroup G) ≤ normalizer (D : Set G) :=
    hPM.trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 M)
  have hbot2 : IsPGroup 2 (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hPbot : (P : Subgroup G) ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨T, hTsyl, hST, hBT⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hB3 hD3 hBD hSD hS2 hBS
  obtain ⟨T', hT'syl, -, hPT'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two P.isPGroup' hD3 hPD bot_le hbot2 hPbot
  obtain ⟨c, hc, hTc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    Nat.prime_three Nat.prime_two hB3 hD3 hBD hT'syl hTsyl (hBP.trans hPT') hBT
  refine ⟨T, c, hST, hTsyl.2.1, (mem_inf.mp hc).1, (mem_inf.mp hc).2, ?_⟩
  rw [hTc, ← Subgroup.map_equiv_normalizer_eq]
  exact map_mono hPT'

omit [Finite G] in
private theorem sylow621_conj_fixed {c z : G} (h : z * c = c * z) :
    (MulAut.conj c).toMonoidHom z = z := by
  change c * z * c⁻¹ = z
  rw [← h, mul_inv_cancel_right]

omit [Finite G] in
private theorem sylow621_center_map {P : Subgroup G} {z : G} {φ : G →* G}
    (hφ : Function.Injective φ) (hzφ : φ z = z)
    (hcen : ∀ w ∈ P, w ∈ centralizer (P : Set G) → w ^ 3 = 1 → w ∈ zpowers z) :
    ∀ w ∈ P.map φ, w ∈ centralizer ((P.map φ : Subgroup G) : Set G) → w ^ 3 = 1 →
      w ∈ zpowers z := by
  rintro _ ⟨p, hp, rfl⟩ hwc hw3
  have hpc : p ∈ centralizer (P : Set G) := by
    rw [mem_centralizer_iff]
    intro q hq
    apply hφ
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hwc (φ q) ⟨q, hq, rfl⟩
  have hp3 : p ^ 3 = 1 := by
    apply hφ
    rw [map_pow, map_one]
    exact hw3
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hcen p hp hpc hp3)
  exact mem_zpowers_iff.mpr ⟨k, by rw [← hk, map_zpow, hzφ]⟩

omit [Finite G] in
private theorem sylow621_centralizes_map {P : Subgroup G} {z : G} {φ : G →* G}
    (hzφ : φ z = z) (hzc : z ∈ centralizer (P : Set G)) :
    z ∈ centralizer ((P.map φ : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨a, ha, rfl⟩
  have h := mem_centralizer_iff.mp hzc a ha
  calc φ a * z = φ a * φ z := by rw [hzφ]
    _ = φ (a * z) := (map_mul φ a z).symm
    _ = φ (z * a) := by rw [h]
    _ = z * φ a := by rw [map_mul, hzφ]

theorem exists_two_group_sylow_three_normalizing (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) (hsolv : Group.IsSolvable M)
    (e : (P : Subgroup G) ≃* W₃) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {S : Subgroup G}
    (hSB : IsTwoInvariantIn (zpowers x ⊔ zpowers z) M S) :
    ∃ T Y : Subgroup G, S ≤ T ∧ IsPGroup 2 T ∧ IsPGroup 3 Y ∧ Y ≤ M ∧ Nat.card Y = 81 ∧
      z ∈ Y ∧ z ∈ centralizer (Y : Set G) ∧ Y ≤ normalizer (T : Set G) ∧
      ∀ w ∈ Y, w ∈ centralizer (Y : Set G) → w ^ 3 = 1 → w ∈ zpowers z := by
  obtain ⟨T, c, hST, hT2, hcD, hcB, hYT⟩ := sylow621_exists_conj hS hsit hsolv hx hz hSB
  have hPM := sylow621_le_maximal hS hsit
  have hcM : c ∈ M := CFSG.AGLEmbedding.glbPrimeCore_le 3 M hcD
  have hzc : z * c = c * z := mem_centralizer_iff.mp hcB z (mem_sup_right (mem_zpowers z))
  have hzφ : (MulAut.conj c).toMonoidHom z = z := sylow621_conj_fixed hzc
  refine ⟨T, (P : Subgroup G).map (MulAut.conj c).toMonoidHom, hST, hT2, P.isPGroup'.map _, ?_,
    ?_, ⟨z, hz.mem, hzφ⟩, sylow621_centralizes_map hzφ hz.centralizes, hYT,
    sylow621_center_map (MulAut.conj c).injective hzφ (sylow621_plane hS hsit hx hz).center⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact M.mul_mem (M.mul_mem hcM (hPM ha)) (M.inv_mem hcM)
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact sylow621_card_eq_eighty_one e

end CFSG.LocalAnalysis.RankThreeTheoremC
