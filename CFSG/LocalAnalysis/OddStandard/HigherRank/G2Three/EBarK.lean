module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Core
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step6
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAschbacherCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAschbacherOne
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Setup
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Tools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CL4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeModel
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1FourGroup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAlt
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Count
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalStatements
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCoreBasics
public import CFSG.LocalAnalysis.ComponentClassification.TBLitStepFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxDef
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSkel
public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Simple
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.AllFixed
public import Certificates.Certificate7233Base

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.ComponentClassification.HarrisLit
open scoped commutatorElement

private def mapMkCenter {E : Type*} [Group E] (K : Subgroup E) :
    ↥K →* ↥(K.map (QuotientGroup.mk' (center E))) :=
  MonoidHom.mk' (fun k => ⟨QuotientGroup.mk' (center E) (k : E),
      Subgroup.mem_map_of_mem _ k.2⟩) (by
    intro a b
    apply Subtype.ext
    show QuotientGroup.mk' (center E) ((a : E) * (b : E)) =
      QuotientGroup.mk' (center E) (a : E) * QuotientGroup.mk' (center E) (b : E)
    rw [map_mul])

private lemma mapMkCenter_surjective {E : Type*} [Group E] (K : Subgroup E) :
    Function.Surjective (mapMkCenter K) := by
  intro y
  obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp y.2
  exact ⟨⟨k, hk⟩, Subtype.ext hky⟩

theorem mem_center_of_map_mem_center {E : Type*} [Group E] {K : Subgroup E}
    (hK : Group.IsPerfect ↥K) (k : ↥K)
    (h : (⟨QuotientGroup.mk' (center E) (k : E), Subgroup.mem_map_of_mem _ k.2⟩ :
      ↥(K.map (QuotientGroup.mk' (center E)))) ∈
        center ↥(K.map (QuotientGroup.mk' (center E)))) :
    k ∈ center ↥K := by
  let π : E →* E ⧸ center E := QuotientGroup.mk' (center E)
  have hmem : ∀ k' : ↥K, ⁅(k : E), (k' : E)⁆ ∈ center E := by
    intro k'
    have hc := (Subgroup.mem_center_iff.mp h)
      (⟨π (k' : E), Subgroup.mem_map_of_mem π k'.2⟩ : ↥(K.map π))
    have hc' : π (k' : E) * π (k : E) = π (k : E) * π (k' : E) :=
      congrArg Subtype.val hc
    have h1 : π ⁅(k : E), (k' : E)⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hc'.symm
    exact (QuotientGroup.eq_one_iff (N := center E) _).mp h1
  let f : ↥K →* ↥(center E) :=
    MonoidHom.mk' (fun k' => ⟨⁅(k : E), (k' : E)⁆, hmem k'⟩) (by
      intro a b
      apply Subtype.ext
      show ⁅(k : E), ((a : E) * (b : E))⁆ = ⁅(k : E), (a : E)⁆ * ⁅(k : E), (b : E)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hca : Commute (a : E) ⁅(k : E), (b : E)⁆ :=
        (Subgroup.mem_center_iff.mp (hmem b)) (a : E)
      rw [mul_assoc (⁅(k : E), (a : E)⁆) (a : E) (⁅(k : E), (b : E)⁆), hca.eq]
      simp only [mul_assoc, mul_inv_cancel, mul_one])
  have hcomm_le : commutator ↥K ≤ f.ker := Abelianization.commutator_subset_ker f
  have htop : commutator ↥K = ⊤ := hK.commutator_eq_top
  have hker : f.ker = ⊤ := top_le_iff.mp (htop ▸ hcomm_le)
  rw [Subgroup.mem_center_iff]
  intro k'
  have h1 : f k' = 1 := by
    have : k' ∈ f.ker := by rw [hker]; trivial
    simpa using this
  have h2 : ⁅(k : E), (k' : E)⁆ = 1 := by
    have := congrArg Subtype.val h1
    simpa [f] using this
  exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp h2).symm

theorem nonempty_quotient_center_equiv_map {E : Type*} [Group E] {K : Subgroup E}
    (hK : CFSG.IsQuasisimple ↥K) :
    Nonempty (↥K ⧸ center ↥K ≃* ↥(K.map (QuotientGroup.mk' (center E))) ⧸
      center ↥(K.map (QuotientGroup.mk' (center E)))) := by
  let K' : Subgroup (E ⧸ center E) := K.map (QuotientGroup.mk' (center E))
  have hcenter : center ↥K ≤ (center ↥K').comap (mapMkCenter K) := by
    intro x hx
    exact (Subgroup.map_center_le_center (mapMkCenter_surjective K)) ⟨x, hx, rfl⟩
  let Φ : ↥K ⧸ center ↥K →* ↥K' ⧸ center ↥K' :=
    QuotientGroup.map (center ↥K) (center ↥K') (mapMkCenter K) hcenter
  have hΦinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    change (QuotientGroup.map (center ↥K) (center ↥K') (mapMkCenter K) hcenter).ker = ⊥
    rw [QuotientGroup.ker_map]
    apply le_bot_iff.mp
    intro q hq
    rw [Subgroup.mem_bot]
    rcases hq with ⟨x, hx, rfl⟩
    have hx' : x ∈ center ↥K :=
      mem_center_of_map_mem_center hK.1 x hx
    exact (QuotientGroup.eq_one_iff (N := center ↥K) x).mpr hx'
  have hΦsurj : Function.Surjective Φ := by
    change Function.Surjective
      (QuotientGroup.map (center ↥K) (center ↥K') (mapMkCenter K) hcenter)
    refine QuotientGroup.map_surjective_of_surjective (N := center ↥K)
      (center ↥K') (mapMkCenter K) ?_ hcenter
    intro z
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center ↥K') z
    obtain ⟨k, hk⟩ := mapMkCenter_surjective K y
    exact ⟨k, by rw [Function.comp_apply, hk]; simpa using hy⟩
  exact ⟨MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩⟩

theorem isQuasisimple_map_mk_center {E : Type*} [Group E] {K : Subgroup E}
    (hK : CFSG.IsQuasisimple ↥K) :
    CFSG.IsQuasisimple ↥(K.map (QuotientGroup.mk' (center E))) := by
  refine ⟨?_, ?_, ?_⟩
  · haveI : Group.IsPerfect ↥K := hK.1
    exact Group.IsPerfect.ofSurjective (mapMkCenter_surjective K)
  · haveI : IsSimpleGroup (↥K ⧸ center ↥K) := hK.2.1
    obtain ⟨e⟩ := nonempty_quotient_center_equiv_map hK
    exact e.symm.isSimpleGroup
  · obtain ⟨e⟩ := nonempty_quotient_center_equiv_map hK
    obtain ⟨a, b, hab⟩ := hK.2.2
    exact ⟨e a, e b, fun h => hab (e.injective (by simpa only [map_mul] using h))⟩

theorem not_orderOf_four_of_mem_center_map {E : Type*} [Group E] [Finite E] {K : Subgroup E}
    {u : E} (hK : CFSG.IsQuasisimple ↥K) (hu2 : u * u ∈ center E)
    (htwo : ∀ c ∈ K, (∀ k ∈ K, k * c = c * k) → IsPGroup 2 (zpowers c) → c ∈ zpowers u)
    (x : ↥(K.map (QuotientGroup.mk' (center E))))
    (hx : x ∈ center ↥(K.map (QuotientGroup.mk' (center E)))) : orderOf x ≠ 4 := by
  intro hx4
  let π : E →* E ⧸ center E := QuotientGroup.mk' (center E)
  obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp x.2
  let kk : ↥K := ⟨k, hk⟩
  have hxK : (⟨π k, Subgroup.mem_map_of_mem π hk⟩ : ↥(K.map π)) ∈ center ↥(K.map π) := by
    have hxeq : (⟨π k, Subgroup.mem_map_of_mem π hk⟩ : ↥(K.map π)) = x := Subtype.ext hkx
    rwa [hxeq]
  have hkcenter : kk ∈ center ↥K :=
    mem_center_of_map_mem_center hK.1 kk (by simpa [kk, π] using hxK)
  have hx4π : orderOf (π k) = 4 := by
    have hxeq : (⟨π k, Subgroup.mem_map_of_mem π hk⟩ : ↥(K.map π)) = x := Subtype.ext hkx
    rw [← hxeq] at hx4
    simpa only [Subgroup.orderOf_mk] using hx4
  have hcomm0 : ∀ k' : ↥K, (k' : E) * k = k * (k' : E) := by
    intro k'
    have h := Subgroup.mem_center_iff.mp hkcenter k'
    simpa [kk] using congrArg Subtype.val h
  set n : ℕ := orderOf k with hn
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact (isOfFinOrder_of_finite (k : E)).orderOf_pos.ne'
  obtain ⟨e, m, hm_odd, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  let c : E := k ^ m
  have hcK : c ∈ K := by
    show k ^ m ∈ K
    exact K.pow_mem hk m
  have hcommc : ∀ k' ∈ K, k' * c = c * k' := by
    intro k' hk'
    have h0 : Commute k' k := hcomm0 ⟨k', hk'⟩
    exact (h0.pow_right m).eq
  have hc_pow : c ^ (2 ^ e) = 1 := by
    show (k ^ m) ^ (2 ^ e) = 1
    rw [← pow_mul, mul_comm m (2 ^ e), ← hnm, hn]
    exact pow_orderOf_eq_one k
  have hcP : IsPGroup 2 (zpowers c) := by
    apply IsPGroup.of_card_dvd_pow (n := e)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr hc_pow
  have hcu : c ∈ zpowers u := htwo c hcK hcommc hcP
  have hc2center : c ^ 2 ∈ center E := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hcu
    rw [← hj, pow_two]
    have hsq : (u ^ j) * (u ^ j) = (u * u) ^ j :=
      ((Commute.refl u).mul_zpow j).symm
    rw [hsq]
    exact Subgroup.zpow_mem (center E) hu2 j
  have hpi_c2 : π (c ^ 2) = 1 :=
    (QuotientGroup.eq_one_iff (N := center E) (c ^ 2)).mpr hc2center
  have hpi_eq : π (c ^ 2) = (π k) ^ (2 * m) := by
    show π ((k ^ m) ^ 2) = (π k) ^ (2 * m)
    rw [← pow_mul, map_pow, mul_comm m 2]
  have hpow1 : (π k) ^ (2 * m) = 1 := by rw [← hpi_eq]; exact hpi_c2
  have hdvd : orderOf (π k) ∣ 2 * m := orderOf_dvd_iff_pow_eq_one.mpr hpow1
  rw [hx4π] at hdvd
  have h4 : (2 : ℕ) * 2 ∣ 2 * m := by
    rw [show (2 : ℕ) * 2 = 4 by norm_num]; exact hdvd
  have h2m : 2 ∣ m :=
    (mul_dvd_mul_iff_left (show (2 : ℕ) ≠ 0 by norm_num)).mp h4
  exact (Nat.not_even_iff_odd.mpr hm_odd) (even_iff_two_dvd.mpr h2m)

theorem nonempty_fusionZStar_equiv_map_mk_center {E : Type*} [Group E] [Finite E]
    {K : Subgroup E} (hK : CFSG.IsQuasisimple ↥K) (hev : 2 ∣ Nat.card ↥K)
    (hev' : 2 ∣ Nat.card ↥(K.map (QuotientGroup.mk' (center E)))) :
    Nonempty (↥K ⧸ CFSG.Open.fusionZStar ↥K ≃*
      ↥(K.map (QuotientGroup.mk' (center E))) ⧸
        CFSG.Open.fusionZStar ↥(K.map (QuotientGroup.mk' (center E)))) := by
  have hOK : pPrimeCore 2 ↥K ≠ ⊤ := by
    intro h
    have hc := CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥K)
    rw [h, Subgroup.card_top] at hc
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl hev hc
  have hOK' : pPrimeCore 2 ↥(K.map (QuotientGroup.mk' (center E))) ≠ ⊤ := by
    intro h
    have hc := CFSG.pPrimeCore_coprime_card (p := 2)
      (G := ↥(K.map (QuotientGroup.mk' (center E))))
    rw [h, Subgroup.card_top] at hc
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl hev' hc
  have hZK := CFSG.ComponentClassification.CatLeaf.fusionZStar_eq_center_of_quasisimple hK hOK
  have hZK' := CFSG.ComponentClassification.CatLeaf.fusionZStar_eq_center_of_quasisimple
    (isQuasisimple_map_mk_center hK) hOK'
  obtain ⟨e⟩ := nonempty_quotient_center_equiv_map hK
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZK).trans
    (e.trans (QuotientGroup.quotientMulEquivOfEq hZK'.symm))⟩

end CFSG.OddStandard.HigherRank.G2Three
