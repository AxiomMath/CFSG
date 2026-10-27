module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIMemberCZero
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNineStmt
import CFSG.LocalAnalysis.AGLEmbedding.CZeroLift
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Quasithin.EmptyFaithful.SBc6Sl2
import CFSG.Quasithin.EmptyFaithful.S1422Basic
import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem nonempty_perfectCore_quot_mulEquiv {Y : Type} [Group Y] [Finite Y] (J : Subgroup Y) :
    Nonempty (↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J))) ≃*
      CFSG.Quasithin.ModO2 (CFSG.Quasithin.perfectCore J)) := by
  let D := ↥J ⧸ CFSG.pCore 2 ↥J
  let C : Subgroup D := CFSG.Quasithin.perfectCore (⊤ : Subgroup D)
  let φ : ↥(CFSG.Quasithin.perfectCore J) →* D :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥J)).comp
      (Subgroup.inclusion (CFSG.Quasithin.perfectCore_le J))
  have hRange : φ.range = C := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact CZeroUnique.map_subgroupOf_perfectCore (QuotientGroup.mk' (CFSG.pCore 2 ↥J))
      (QuotientGroup.mk'_surjective _)
  have hker : IsPGroup 2 φ.ker := by
    have h : φ.ker = (CFSG.pCore 2 ↥J).comap
        (Subgroup.inclusion (CFSG.Quasithin.perfectCore_le J)) := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [h]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥J)).comap_of_injective _
      (Subgroup.inclusion_injective _)
  have hD : CFSG.pCore 2 D = ⊥ := CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' 2
  have hCsub : CFSG.Open.IsSubnormal C ⊤ :=
    CFSG.Quasithin.A3.subnormal_perfectCore (CFSG.Open.IsSubnormal.refl ⊤)
  have hCO : CFSG.pCore 2 ↥C = ⊥ :=
    CFSG.AGLEmbedding.CZeroLift.pCore_eq_bot_of_isSubnormal hCsub hD
  have hO : CFSG.pCore 2 ↥φ.range = ⊥ := by
    rw [hRange]
    exact hCO
  have hp : CFSG.pCore 2 ↥(CFSG.Quasithin.perfectCore J) = φ.ker :=
    CFSG.AGLEmbedding.CZeroLift.pCore_eq_ker_of_range φ hker hO
  exact ⟨(((QuotientGroup.quotientMulEquivOfEq hp).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hRange)).symm⟩

theorem not_two_dvd_index_perfectCore_quot {Y : Type} [Group Y] [Finite Y] {T J : Subgroup Y}
    (hT : IsSylowTwoOf T J) (hTJ : T ≤ CFSG.Quasithin.perfectCore J) :
    ¬ 2 ∣ (CFSG.Quasithin.perfectCore
      (⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J))).index := by
  let C : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J) :=
    CFSG.Quasithin.perfectCore (⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J))
  have hmap : ((T.subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))).index ∣
      (T.subgroupOf J).index :=
    Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
  have hC : C = ((CFSG.Quasithin.perfectCore J).subgroupOf J).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) := by
    rw [CZeroUnique.map_subgroupOf_perfectCore _ (QuotientGroup.mk'_surjective _)]
  have hidx : C.index ∣
      ((T.subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))).index := by
    rw [hC]
    exact Subgroup.index_dvd_of_le (Subgroup.map_mono (Subgroup.subgroupOf_mono J hTJ))
  intro h2
  exact hT.2.2 (h2.trans (hidx.trans hmap))

theorem exists_prime_dvd_card_of_isPSL_two {Z : Type} [Group Z] {n : ℕ} (hn : Odd n)
    (hn3 : 3 ≤ n) (hZ : CFSG.Quasithin.IsPSL 2 2 n Z) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ∣ Nat.card Z := by
  have hcard : Nat.card Z = 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hZ
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨k, hk⟩ : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have h2n : 2 ≤ 2 ^ n :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ n))
    exact ⟨k - 1, by omega⟩
  have hne : 2 ^ n - 1 ≠ 1 := by
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · intro hr2
    subst hr2
    exact hodd.not_two_dvd_nat hrd
  · intro hr3
    subst hr3
    obtain ⟨k, hk⟩ := hrd
    have h2n : 2 ^ n = 3 * k + 1 := (Nat.sub_eq_iff_eq_add (Nat.one_le_two_pow)).mp hk
    have hmod : 2 ^ n % 3 = 2 := CFSG.two_pow_mod_three_of_odd hn
    rw [h2n, Nat.mul_add_mod_self_left] at hmod
    norm_num at hmod
  · rw [hcard]
    exact hrd.trans ((Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2).mul_left (2 ^ n))

private def rangeQuotMap {X : Subgroup G} {Y : Type} [Group Y] (ψ₁ : ↥X →* Y) :
    ↥X →* (↥ψ₁.range ⧸ CFSG.pCore 2 ↥ψ₁.range) :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥ψ₁.range)).comp ψ₁.rangeRestrict

omit [Finite G] in
private theorem rangeQuotMap_surjective {X : Subgroup G} {Y : Type} [Group Y]
    (ψ₁ : ↥X →* Y) : Function.Surjective (rangeQuotMap ψ₁) :=
  (QuotientGroup.mk'_surjective _).comp ψ₁.rangeRestrict_surjective

omit [Finite G] in
private theorem isPGroup_ker_rangeQuotMap {X : Subgroup G} {Y : Type} [Group Y]
    (ψ₁ : ↥X →* Y) (hker : IsPGroup 2 ψ₁.ker) :
    IsPGroup 2 (rangeQuotMap ψ₁).ker := by
  have h : (rangeQuotMap ψ₁).ker =
      (CFSG.pCore 2 ↥ψ₁.range).comap ψ₁.rangeRestrict := by
    calc
      (rangeQuotMap ψ₁).ker = ((QuotientGroup.mk' (CFSG.pCore 2 ↥ψ₁.range)).comp
          ψ₁.rangeRestrict).ker := rfl
      _ = (QuotientGroup.mk' (CFSG.pCore 2 ↥ψ₁.range)).ker.comap ψ₁.rangeRestrict :=
        (MonoidHom.comap_ker _ _).symm
      _ = (CFSG.pCore 2 ↥ψ₁.range).comap ψ₁.rangeRestrict := by
        rw [QuotientGroup.ker_mk']
  rw [h]
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥ψ₁.range)).comap_of_ker_isPGroup
    ψ₁.rangeRestrict (by rwa [MonoidHom.ker_rangeRestrict])

theorem cZero_eq_singleton_of_parabolic {X : Subgroup G} {Y : Type} [Group Y] [Finite Y]
    (ψ₁ : ↥X →* Y) (hker : IsPGroup 2 ψ₁.ker) {T : Subgroup Y} (hT : IsSylowTwoOf T ⊤)
    (hTJ : T ≤ CFSG.Quasithin.perfectCore ψ₁.range) {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (hJ : CFSG.Quasithin.IsPSL 2 2 n
      (CFSG.Quasithin.ModO2 (CFSG.Quasithin.perfectCore ψ₁.range))) :
    ∃ I : Subgroup G, cZero X = {I} ∧ IsPSLType 2 (GaloisField 2 n) (modTwoCore I) := by
  let D := ↥ψ₁.range ⧸ CFSG.pCore 2 ↥ψ₁.range
  let ψ : ↥X →* D := rangeQuotMap ψ₁
  have hψ : Function.Surjective ψ := rangeQuotMap_surjective ψ₁
  have hkerψ : IsPGroup 2 ψ.ker := isPGroup_ker_rangeQuotMap ψ₁ hker
  have hD : CFSG.pCore 2 D = ⊥ := CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' 2
  have hTJ' : IsSylowTwoOf T ψ₁.range := by
    have hTle : T ≤ ψ₁.range := hTJ.trans (CFSG.Quasithin.perfectCore_le ψ₁.range)
    refine ⟨hTle, hT.2.1, ?_⟩
    intro h2
    refine hT.2.2 ?_
    rw [show (T.subgroupOf (⊤ : Subgroup Y)).index = T.index from
      Subgroup.relIndex_top_right T, ← Subgroup.relIndex_mul_index hTle]
    exact dvd_mul_of_dvd_left h2 _
  have hodd : ¬ 2 ∣ (CFSG.Quasithin.perfectCore (⊤ : Subgroup D)).index :=
    not_two_dvd_index_perfectCore_quot hTJ' hTJ
  obtain ⟨eC⟩ := nonempty_perfectCore_quot_mulEquiv ψ₁.range
  have hsimple : IsSimpleGroup
      (CFSG.Quasithin.ModO2 (CFSG.Quasithin.perfectCore ψ₁.range)) :=
    CFSG.Quasithin.SBc6.isSimpleGroup_of_psl (by omega) hJ
  have hC : IsSimpleGroup ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D)) :=
    eC.isSimpleGroup_congr.mpr hsimple
  obtain ⟨r, hr, hr2, hr3, hrC⟩ := exists_prime_dvd_card_of_isPSL_two hn hn3 hJ
  have hrC' : r ∣ Nat.card ↥(CFSG.Quasithin.perfectCore (⊤ : Subgroup D)) := by
    rw [Nat.card_congr eC.toEquiv]
    exact hrC
  obtain ⟨I, hset, ⟨eI⟩⟩ :=
    CZeroUnique.cZero_eq_singleton_of_perfectCore hψ hkerψ hD hC hodd hr hr2 hr3 hrC'
  refine ⟨I, hset, ?_⟩
  obtain ⟨eP⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField
    (CFSG.Quasithin.ModO2 (CFSG.Quasithin.perfectCore ψ₁.range)) 2 2 n hJ
  exact ⟨eI.trans (eC.trans eP)⟩

theorem cZero_eq_singleton_of_parabolic_one {X : Subgroup G} {Y : Type} [Group Y] [Finite Y]
    (ψ₁ : ↥X →* Y) (hker : IsPGroup 2 ψ₁.ker)
    (e : ↥ψ₁.range ⧸ CFSG.pCore 2 ↥ψ₁.range ≃* Equiv.Perm (Fin 3)) :
    ∃ I : Subgroup G, cZero X = {I} ∧ IsPSLType 2 (GaloisField 2 1) (modTwoCore I) := by
  let D := ↥ψ₁.range ⧸ CFSG.pCore 2 ↥ψ₁.range
  let ψ : ↥X →* D := rangeQuotMap ψ₁
  have hψ : Function.Surjective ψ := rangeQuotMap_surjective ψ₁
  have hkerψ : IsPGroup 2 ψ.ker := isPGroup_ker_rangeQuotMap ψ₁ hker
  have hD : CFSG.pCore 2 D = ⊥ := CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' 2
  obtain ⟨hset, ⟨eI⟩⟩ := CZeroUnique.cZero_eq_singleton_of_perm_three hψ hkerψ hD e
  exact ⟨X, hset, ⟨eI.trans CFSG.Quasithin.permThreeEquivPSL⟩⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
