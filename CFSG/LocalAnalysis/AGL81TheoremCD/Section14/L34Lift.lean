module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Transitive
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerSubgroupCyclic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.PGLModelDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]
variable {K : Subgroup G}
variable {A : Subgroup G}

theorem pPrimeCore_quotient_injOn_of_isSylowOf {A : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K) :
    Set.InjOn (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) (A.subgroupOf K : Set ↥K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  have hbot : A.subgroupOf K ⊓ CFSG.pPrimeCore 3 ↥K = ⊥ := by
    have hA3 : IsPGroup 3 ↥(A.subgroupOf K) := hA.isPGroup.comap_subtype
    obtain ⟨n, hn⟩ := hA3.exists_card_eq
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hn]
    exact Nat.Coprime.pow_left n (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K))
  intro x hx y hy hxy
  have hmem : x⁻¹ * y ∈ A.subgroupOf K ⊓ CFSG.pPrimeCore 3 ↥K := by
    refine ⟨(A.subgroupOf K).mul_mem ((A.subgroupOf K).inv_mem hx) hy, ?_⟩
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) (x⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥K) (x⁻¹ * y)).mp h1
  rw [hbot] at hmem
  have h1 : x⁻¹ * y = 1 := by simpa using hmem
  exact inv_mul_eq_one.mp h1

theorem card_eq_card_map_pPrimeCore_quotient_of_isSylowOf {A : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K) :
    Nat.card A = Nat.card ((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))) := by
  have hcardA : Nat.card A = Nat.card (A.subgroupOf K) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.le).toEquiv).symm
  rw [hcardA]
  symm
  rw [← SetLike.coe_sort_coe, Subgroup.coe_map,
    Nat.card_image_of_injOn (pPrimeCore_quotient_injOn_of_isSylowOf hA)]
  rfl

theorem card_map_pPrimeCore_quotient_of_isSylowOf {A : Subgroup G}
    (hK : Nonempty ((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃* projSL 3 (GaloisField 2 2)))
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K) :
    Nat.card ((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))) = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  obtain ⟨Q3, hQ3⟩ := hA.exists_sylow_eq_subgroupOf
  let Q3bar : Sylow 3 (↥K ⧸ CFSG.pPrimeCore 3 ↥K) :=
    Q3.mapSurjective (f := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))
      (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥K))
  have hcoe : (Q3bar : Subgroup (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) =
      (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) := by
    rw [Sylow.coe_mapSurjective (f := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))
      (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥K)), hQ3]
  rw [← hcoe, Sylow.card_eq_multiplicity]
  obtain ⟨e⟩ := hK
  have hcard : Nat.card (↥K ⧸ CFSG.pPrimeCore 3 ↥K) = 20160 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.L34.card_projSL
  have hf3 : (20160 : ℕ).factorization 3 = 2 := by
    rw [show (20160 : ℕ) = 3 ^ 2 * 2240 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [hcard, hf3]
  norm_num

theorem card_eq_nine_of_isSylowOf (hK : Nonempty
    ((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃* projSL 3 (GaloisField 2 2)))
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K) : Nat.card A = 9 := by
  rw [card_eq_card_map_pPrimeCore_quotient_of_isSylowOf hA,
    card_map_pPrimeCore_quotient_of_isSylowOf hK hA]

theorem isElemAbelian_of_isSylowOf (hK : Nonempty
    ((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃* projSL 3 (GaloisField 2 2)))
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K) : CFSG.Open.IsElemAbelian 3 A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  have h9 : Nat.card A = 9 := card_eq_nine_of_isSylowOf hK hA
  have hbar9 : Nat.card ((A.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))) = 9 :=
    card_map_pPrimeCore_quotient_of_isSylowOf hK hA
  obtain ⟨e⟩ := hK
  let eP : (↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2) :=
    e.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))
  have himg9 : Nat.card (((A.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map eP.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective eP.injective, hbar9]
  have hk4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hEimg : CFSG.IsElementaryAbelian 3 (((A.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map eP.toMonoidHom) :=
    CFSG.RankThree.PartTwo.KFacts.L34.isElementaryAbelian_of_card_eq_nine hk4 himg9
  have hEimg' : CFSG.Open.IsElemAbelian 3 (((A.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map eP.toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mp hEimg
  refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) ?_, ?_⟩
  · rw [h9]; norm_num
  · intro a ha
    have hxbar : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨a, hA.le ha⟩ ∈
        (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
    have hxbar' : eP (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨a, hA.le ha⟩) ∈
        ((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map
          eP.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hxbar
    have h3 : (eP (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨a, hA.le ha⟩)) ^ 3 = 1 :=
      hEimg'.2 _ hxbar'
    have hbar : (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨a, hA.le ha⟩) ^ 3 = 1 := by
      apply eP.injective
      rw [map_pow, map_one]
      exact h3
    have hx3 : a ^ 3 ∈ A := A.pow_mem ha 3
    have hmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)
        (⟨a ^ 3, hA.le hx3⟩ : ↥K) = 1 := by
      have hpow : (⟨a ^ 3, hA.le hx3⟩ : ↥K) = ⟨a, hA.le ha⟩ ^ 3 := Subtype.ext rfl
      rw [hpow, map_pow, hbar]
    have hone : (⟨a ^ 3, hA.le hx3⟩ : ↥K) = 1 :=
      pPrimeCore_quotient_injOn_of_isSylowOf hA (Subgroup.mem_subgroupOf.mpr hx3)
        (Subgroup.mem_subgroupOf.mpr A.one_mem) (by rw [hmem, map_one])
    simpa using congrArg Subtype.val hone

theorem pPrimeCore_quotient_eq_one_of_mem_map {y : G} {hyK : y ∈ K}
    (hy : y ∈ (CFSG.pPrimeCore 3 ↥K).map K.subtype) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨y, hyK⟩ = 1 := by
  obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.mp hy
  rw [show (⟨y, hyK⟩ : ↥K) = n from Subtype.ext hny.symm]
  exact (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥K) n).mpr hn

theorem mem_sup_of_quotient_eq {K A : Subgroup G} (hAK : A ≤ K) {c : ↥K} {a : G}
    (ha : a ∈ A)
    (hπ : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) c =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨a, hAK ha⟩) :
    (c : G) ∈ A ⊔ (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  have hker : c * ⟨a, hAK ha⟩⁻¹ ∈ CFSG.pPrimeCore 3 ↥K := by
    rw [← QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥K)]
    change QuotientGroup.mk (c * ⟨a, hAK ha⟩⁻¹) = 1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) c *
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨a, hAK ha⟩)⁻¹ = 1
    rw [hπ, mul_inv_cancel]
  have hOK : ((c * ⟨a, hAK ha⟩⁻¹ : ↥K) : G) ∈
      (CFSG.pPrimeCore 3 ↥K).map K.subtype := Subgroup.mem_map_of_mem K.subtype hker
  have heq : (c : G) = ((c * ⟨a, hAK ha⟩⁻¹ : ↥K) : G) * a := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [heq]
  exact (A ⊔ (CFSG.pPrimeCore 3 ↥K).map K.subtype).mul_mem
    (Subgroup.mem_sup_right hOK) (Subgroup.mem_sup_left ha)

theorem pPrimeCore_quotient_eq_of_mem_pPrimeCore_map {K : Subgroup G} {a k : G}
    (haK : a ∈ K) (hk : k ∈ K)
    (h : a⁻¹ * k ∈ (CFSG.pPrimeCore 3 ↥K).map K.subtype) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨k, hk⟩ =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨a, haK⟩ := by
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  change QuotientGroup.mk (⟨k, hk⟩ : ↥K) = QuotientGroup.mk ⟨a, haK⟩
  rw [QuotientGroup.eq]
  have hmemK : a⁻¹ * k ∈ K := Subgroup.map_subtype_le _ h
  have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) (⟨a⁻¹ * k, hmemK⟩ : ↥K) = 1 :=
    pPrimeCore_quotient_eq_one_of_mem_map (K := K) (hyK := hmemK) h
  have h2 : (⟨a⁻¹ * k, hmemK⟩ : ↥K) ∈ CFSG.pPrimeCore 3 ↥K :=
    (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥K) _).mp h1
  have h3 : (⟨a⁻¹ * k, hmemK⟩ : ↥K) = (⟨a, haK⟩ : ↥K)⁻¹ * ⟨k, hk⟩ := by
    apply Subtype.ext
    simp
  rw [h3] at h2
  simpa using (CFSG.pPrimeCore 3 ↥K).inv_mem h2


theorem exists_mem_normalizer_inf_conj_eq (hK : Nonempty
    ((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃* projSL 3 (GaloisField 2 2)))
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (A : Set G) ⊓ K, n * a * n⁻¹ = b := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  haveI : Fact (IsPGroup 3 ↥(A.subgroupOf K)) := ⟨hA.isPGroup.comap_subtype⟩
  set N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K with hN
  set π : ↥K →* (↥K ⧸ N) := QuotientGroup.mk' N with hπ
  set AK : Subgroup ↥K := A.subgroupOf K with hAK
  set Abar : Subgroup (↥K ⧸ N) := AK.map π with hAbar
  have hAbar9 : Nat.card Abar = 9 := by
    simpa [Abar, AK, π] using card_map_pPrimeCore_quotient_of_isSylowOf hK hA
  obtain ⟨e⟩ := hK
  have haK : a ∈ K := hA.le ha
  have hbK : b ∈ K := hA.le hb
  have hpa : π ⟨a, haK⟩ ∈ Abar := by
    rw [hAbar]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha)
  have hpb : π ⟨b, hbK⟩ ∈ Abar := by
    rw [hAbar]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hb)
  have hpa1 : π ⟨a, haK⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨a, haK⟩ : ↥K) = 1 :=
      pPrimeCore_quotient_injOn_of_isSylowOf hA (Subgroup.mem_subgroupOf.mpr ha)
        (Subgroup.mem_subgroupOf.mpr A.one_mem) (by rw [h1, map_one])
    exact ha1 (by simpa using congrArg Subtype.val h2)
  have hpb1 : π ⟨b, hbK⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨b, hbK⟩ : ↥K) = 1 :=
      pPrimeCore_quotient_injOn_of_isSylowOf hA (Subgroup.mem_subgroupOf.mpr hb)
        (Subgroup.mem_subgroupOf.mpr A.one_mem) (by rw [h1, map_one])
    exact hb1 (by simpa using congrArg Subtype.val h2)
  obtain ⟨nstar, hnstar, hnstarconj⟩ :=
    exists_mem_normalizer_conj_eq e hAbar9 hpa hpa1 hpb hpb1
  have hbar : Subgroup.normalizer Abar = (Subgroup.normalizer AK).map π := by
    simpa [Abar, AK, π] using normalizer_map_quotient_eq_map_normalizer 3
      (A.subgroupOf K) (CFSG.pPrimeCore 3 ↥K)
      (CFSG.pPrimeCore_normal (p := 3) (G := ↥K))
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K))
  rw [hbar] at hnstar
  obtain ⟨n, hnN, hπn⟩ := Subgroup.mem_map.mp hnstar
  have hxmem : n * (⟨a, haK⟩ : ↥K) * n⁻¹ ∈ AK := by
    rw [hAK]
    exact (Subgroup.mem_normalizer_iff.mp hnN (⟨a, haK⟩ : ↥K)).mp
      (Subgroup.mem_subgroupOf.mpr ha)
  have hconj : π (n * (⟨a, haK⟩ : ↥K) * n⁻¹) = π ⟨b, hbK⟩ := by
    rw [map_mul, map_mul, map_inv, hπn, hnstarconj]
  have heq : n * (⟨a, haK⟩ : ↥K) * n⁻¹ = ⟨b, hbK⟩ :=
    pPrimeCore_quotient_injOn_of_isSylowOf hA hxmem
      (Subgroup.mem_subgroupOf.mpr hb) hconj
  refine ⟨(n : G), ?_, ?_⟩
  · have hmem : n ∈ (K ⊓ Subgroup.normalizer (A : Set G)).subgroupOf K := by
      rw [← CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer K A hA.le]
      exact hnN
    exact ⟨(Subgroup.mem_subgroupOf.mp hmem).2, n.2⟩
  · simpa using congrArg Subtype.val heq

theorem mem_conj_of_inner {A : Subgroup G} (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K)
    {e k : G} (hk : k ∈ K)
    (hek : ∀ x ∈ A, (k * x * k⁻¹)⁻¹ * (e * x * e⁻¹) ∈
      (CFSG.pPrimeCore 3 ↥K).map K.subtype)
    {x : G} (hx : x ∈ A) : e * x * e⁻¹ ∈ K := by
  have hxk : k * x * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk (hA.le hx)) (K.inv_mem hk)
  have hOle : ((CFSG.pPrimeCore 3 ↥K).map K.subtype) ≤ K := Subgroup.map_subtype_le _
  have hsplit : e * x * e⁻¹ = (k * x * k⁻¹) * ((k * x * k⁻¹)⁻¹ * (e * x * e⁻¹)) := by
    group
  rw [hsplit]
  exact K.mul_mem hxk (hOle (hek x hx))

theorem pPrimeCore_quotient_conj_eq {A : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K) {e k : G} (hk : k ∈ K)
    (hek : ∀ x ∈ A, (k * x * k⁻¹)⁻¹ * (e * x * e⁻¹) ∈
      (CFSG.pPrimeCore 3 ↥K).map K.subtype)
    {x : G} (hx : x ∈ A) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨e * x * e⁻¹, mem_conj_of_inner hA hk hek hx⟩ =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨k, hk⟩ *
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨x, hA.le hx⟩ *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨k, hk⟩)⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  have hxk : k * x * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk (hA.le hx)) (K.inv_mem hk)
  have hmem : (k * x * k⁻¹)⁻¹ * (e * x * e⁻¹) ∈ K :=
    K.mul_mem (K.inv_mem hxk) (mem_conj_of_inner hA hk hek hx)
  have hq : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)
      (⟨(k * x * k⁻¹)⁻¹ * (e * x * e⁻¹), hmem⟩ : ↥K) = 1 := by
    simpa using pPrimeCore_quotient_eq_one_of_mem_map (K := K) (hyK := hmem) (hek x hx)
  have hprod : (⟨e * x * e⁻¹, mem_conj_of_inner hA hk hek hx⟩ : ↥K) =
      ⟨k * x * k⁻¹, hxk⟩ * ⟨(k * x * k⁻¹)⁻¹ * (e * x * e⁻¹), hmem⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  calc QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨e * x * e⁻¹, mem_conj_of_inner hA hk hek hx⟩
      = QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨k * x * k⁻¹, hxk⟩ := by
        rw [hprod, map_mul, hq, mul_one]
    _ = QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨k, hk⟩ *
          QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨x, hA.le hx⟩ *
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨k, hk⟩)⁻¹ := by
        have hsplit : (⟨k * x * k⁻¹, hxk⟩ : ↥K) =
            (⟨k, hk⟩ : ↥K) * ⟨x, hA.le hx⟩ * (⟨k, hk⟩ : ↥K)⁻¹ := Subtype.ext rfl
        rw [hsplit, map_mul, map_mul, map_inv]

theorem pPrimeCore_quotient_cube_mem_centralizer {A : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K) {e k : G} (hk : k ∈ K)
    (he3 : e ^ 3 = 1) (heA : ∀ a ∈ A, e * a * e⁻¹ ∈ A)
    (hek : ∀ x ∈ A, (k * x * k⁻¹)⁻¹ * (e * x * e⁻¹) ∈
      (CFSG.pPrimeCore 3 ↥K).map K.subtype) :
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨k, hk⟩) ^ 3 ∈
      Subgroup.centralizer ((A.subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) :
          Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  set N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K with hN
  set π : ↥K →* (↥K ⧸ N) := QuotientGroup.mk' N with hπ
  set AK : Subgroup ↥K := A.subgroupOf K with hAK
  set Abar : Subgroup (↥K ⧸ N) := AK.map π with hAbar
  let kk : ↥K := ⟨k, hk⟩
  let y : ↥K ⧸ N := π kk
  have hτ : ∀ x (hx : x ∈ A), π (⟨e * x * e⁻¹, mem_conj_of_inner hA hk hek hx⟩ : ↥K) =
      y * π ⟨x, hA.le hx⟩ * y⁻¹ := by
    intro x hx
    have h := pPrimeCore_quotient_conj_eq hA hk hek hx
    simpa [π, N, kk, y] using h
  rw [show Subgroup.centralizer ((A.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) : Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) =
      Subgroup.centralizer (Abar : Set (↥K ⧸ N)) from by rw [hAbar, hAK]]
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [hAbar] at hz
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
  have huA : u.1 ∈ A := Subgroup.mem_subgroupOf.mp hu
  have hτ1 : π (⟨e * u.1 * e⁻¹, mem_conj_of_inner hA hk hek huA⟩ : ↥K) =
      y * π u * y⁻¹ := by
    have h := hτ u.1 huA
    simpa using h
  have hτ2 : π (⟨e * (e * u.1 * e⁻¹) * e⁻¹,
      mem_conj_of_inner hA hk hek (heA u.1 huA)⟩ : ↥K) =
      y * π (⟨e * u.1 * e⁻¹, mem_conj_of_inner hA hk hek huA⟩ : ↥K) * y⁻¹ :=
    hτ (e * u.1 * e⁻¹) (heA u.1 huA)
  have hτ3 : π (⟨e * (e * (e * u.1 * e⁻¹) * e⁻¹) * e⁻¹,
      mem_conj_of_inner hA hk hek (heA (e * u.1 * e⁻¹) (heA u.1 huA))⟩ : ↥K) =
      y * π (⟨e * (e * u.1 * e⁻¹) * e⁻¹,
        mem_conj_of_inner hA hk hek (heA u.1 huA)⟩ : ↥K) * y⁻¹ :=
    hτ (e * (e * u.1 * e⁻¹) * e⁻¹) (heA (e * u.1 * e⁻¹) (heA u.1 huA))
  have h3 : e * e * e = 1 := by
    rw [show e * e * e = e ^ 3 by rw [pow_succ, pow_two]]
    exact he3
  have hτx : e * (e * (e * u.1 * e⁻¹) * e⁻¹) * e⁻¹ = u.1 := by
    calc e * (e * (e * u.1 * e⁻¹) * e⁻¹) * e⁻¹
        = (e * e * e) * u.1 * (e * e * e)⁻¹ := by group
      _ = u.1 := by rw [h3, one_mul, inv_one, mul_one]
  have heq : π (⟨e * (e * (e * u.1 * e⁻¹) * e⁻¹) * e⁻¹,
      mem_conj_of_inner hA hk hek (heA (e * u.1 * e⁻¹) (heA u.1 huA))⟩ : ↥K) = π u := by
    rw [show (⟨e * (e * (e * u.1 * e⁻¹) * e⁻¹) * e⁻¹,
        mem_conj_of_inner hA hk hek (heA (e * u.1 * e⁻¹) (heA u.1 huA))⟩ : ↥K) = u
      from Subtype.ext hτx]
  have hfinal : π u = y ^ 3 * π u * (y ^ 3)⁻¹ := by
    conv_lhs => rw [← heq, hτ3, hτ2, hτ1]
    rw [show y * (y * (y * π u * y⁻¹) * y⁻¹) * y⁻¹ =
      y * y * y * π u * (y⁻¹ * y⁻¹ * y⁻¹) by group]
    rw [show y * y * y = y ^ 3 by rw [pow_succ, pow_two],
      show y⁻¹ * y⁻¹ * y⁻¹ = (y⁻¹) ^ 3 by rw [pow_succ, pow_two], ← inv_pow]
  have hcomm : y ^ 3 * π u = π u * y ^ 3 := by
    have h := congrArg (fun z => z * y ^ 3) hfinal
    calc y ^ 3 * π u = (y ^ 3 * π u * (y ^ 3)⁻¹) * y ^ 3 := by group
      _ = π u * y ^ 3 := h.symm
  exact hcomm.symm

theorem pPrimeCore_quotient_mem_normalizer_of_inner (hK : Nonempty
    ((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃* projSL 3 (GaloisField 2 2)))
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K) {e k : G} (hk : k ∈ K)
    (heA : ∀ a ∈ A, e * a * e⁻¹ ∈ A)
    (hek : ∀ x ∈ A, (k * x * k⁻¹)⁻¹ * (e * x * e⁻¹) ∈
      (CFSG.pPrimeCore 3 ↥K).map K.subtype) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨k, hk⟩ ∈
      Subgroup.normalizer ((A.subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) :
          Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  set N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K with hN
  set π : ↥K →* (↥K ⧸ N) := QuotientGroup.mk' N with hπ
  set AK : Subgroup ↥K := A.subgroupOf K with hAK
  set Abar : Subgroup (↥K ⧸ N) := AK.map π with hAbar
  let kk : ↥K := ⟨k, hk⟩
  let y : ↥K ⧸ N := π kk
  rw [show Subgroup.normalizer ((A.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) : Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) =
      Subgroup.normalizer (Abar : Set (↥K ⧸ N)) from by rw [hAbar, hAK]]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap_le : Abar.map (MulAut.conj y).toMonoidHom ≤ Abar := by
    rintro z ⟨w, hw, rfl⟩
    rw [hAbar] at hw
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
    have huA : u.1 ∈ A := Subgroup.mem_subgroupOf.mp hu
    rw [show π u = π ⟨u.1, hA.le huA⟩ from rfl]
    change MulAut.conj y (π ⟨u.1, hA.le huA⟩) ∈ Abar
    rw [MulAut.conj_apply, ← pPrimeCore_quotient_conj_eq hA hk hek huA]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr (heA u.1 huA))
  have hcard : Nat.card (Abar.map (MulAut.conj y).toMonoidHom) = Nat.card Abar :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  exact Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcard.symm)

theorem pPrimeCore_quotient_mem_of_centralizer (hK : Nonempty
    ((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃* projSL 3 (GaloisField 2 2)))
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K)
    {y : ↥K ⧸ CFSG.pPrimeCore 3 ↥K}
    (hycent : y ^ 3 ∈ Subgroup.centralizer ((A.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) :
        Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K)))
    (hyN : y ∈ Subgroup.normalizer ((A.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) :
        Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K))) :
    y ∈ (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  have hE9 : Nat.card ((A.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))) = 9 :=
    card_map_pPrimeCore_quotient_of_isSylowOf hK hA
  have hEAK : CFSG.Open.IsElemAbelian 3 (A.subgroupOf K) :=
    (isElemAbelian_of_isSylowOf hK hA).subgroupOf K
  have hE : CFSG.Open.IsElemAbelian 3 ((A.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))) := hEAK.map _
  obtain ⟨eiso⟩ := hK
  have hy3 : y ^ 3 ∈ (A.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) := by
    rw [centralizer_eq_of_card_eq_nine eiso hE9] at hycent
    exact hycent
  have hy9 : y ^ 9 = 1 := by
    have h3 : (y ^ 3) ^ 3 = 1 := hE.2 (y ^ 3) hy3
    rw [← pow_mul] at h3
    simpa using h3
  have hyP : IsPGroup 3 (Subgroup.zpowers y) := by
    have hdvd : orderOf y ∣ 3 ^ 2 := by
      simpa using orderOf_dvd_of_pow_eq_one hy9
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  obtain ⟨Q3, hQ3⟩ := hA.exists_sylow_eq_subgroupOf
  let Qbar3 : Sylow 3 (↥K ⧸ CFSG.pPrimeCore 3 ↥K) :=
    Q3.mapSurjective (f := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))
      (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥K))
  have hQbar3 : (Qbar3 : Subgroup (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) =
      (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) := by
    rw [Sylow.coe_mapSurjective, hQ3]
  have hset : ((Qbar3 : Sylow 3 (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) :
      Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) =
      ((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) :
        Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) := by
    simpa using congrArg (fun T : Subgroup (↥K ⧸ CFSG.pPrimeCore 3 ↥K) =>
      (T : Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K))) hQbar3
  have hinf : Subgroup.zpowers y ⊓ Subgroup.normalizer ((A.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) :
        Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) =
      Subgroup.zpowers y ⊓ ((A.subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))) := by
    have h := IsPGroup.inf_normalizer_sylow (p := 3) hyP Qbar3
    rw [hset, hQbar3] at h
    exact h
  have hyAbar : y ∈ (A.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) := by
    have h1 : y ∈ Subgroup.zpowers y ⊓ Subgroup.normalizer ((A.subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) :
          Set (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) :=
      ⟨Subgroup.mem_zpowers y, hyN⟩
    rw [hinf] at h1
    exact (Subgroup.mem_inf.mp h1).2
  exact hyAbar

theorem pPrimeCore_quotient_mem_of_inner (hK : Nonempty
    ((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃* projSL 3 (GaloisField 2 2)))
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K) {e k : G} (hk : k ∈ K)
    (he3 : e ^ 3 = 1) (heA : ∀ a ∈ A, e * a * e⁻¹ ∈ A)
    (hek : ∀ x ∈ A, (k * x * k⁻¹)⁻¹ * (e * x * e⁻¹) ∈
      (CFSG.pPrimeCore 3 ↥K).map K.subtype) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨k, hk⟩ ∈
      (A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) :=
  pPrimeCore_quotient_mem_of_centralizer hK hA
    (pPrimeCore_quotient_cube_mem_centralizer hA hk he3 heA hek)
    (pPrimeCore_quotient_mem_normalizer_of_inner hK hA hk heA hek)

theorem exists_mem_and_commute_of_inner (hK : Nonempty
    ((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃* projSL 3 (GaloisField 2 2)))
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K) {e k : G} (hk : k ∈ K)
    (he3 : e ^ 3 = 1) (heA : ∀ a ∈ A, e * a * e⁻¹ ∈ A)
    (hek : ∀ x ∈ A, (k * x * k⁻¹)⁻¹ * (e * x * e⁻¹) ∈
      (CFSG.pPrimeCore 3 ↥K).map K.subtype) :
    (∃ a₀ ∈ A, a₀⁻¹ * k ∈ (CFSG.pPrimeCore 3 ↥K).map K.subtype) ∧
      ∀ a ∈ A, e * a * e⁻¹ = a := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  set N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K with hN
  set π : ↥K →* (↥K ⧸ N) := QuotientGroup.mk' N with hπ
  set AK : Subgroup ↥K := A.subgroupOf K with hAK
  set Abar : Subgroup (↥K ⧸ N) := AK.map π with hAbar
  have hEA : CFSG.Open.IsElemAbelian 3 A := isElemAbelian_of_isSylowOf hK hA
  obtain ⟨aK, haKA, hπa⟩ :=
    Subgroup.mem_map.mp (pPrimeCore_quotient_mem_of_inner hK hA hk he3 heA hek)
  let kk : ↥K := ⟨k, hk⟩
  refine ⟨⟨aK, Subgroup.mem_subgroupOf.mp haKA, ?_⟩, ?_⟩
  · have hq : π (aK⁻¹ * kk) = 1 := by
      rw [map_mul, map_inv, hπa]
      change (π ⟨k, hk⟩)⁻¹ * π ⟨k, hk⟩ = 1
      exact inv_mul_cancel _
    have hmemN : aK⁻¹ * kk ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) (aK⁻¹ * kk)).mp hq
    simpa using Subgroup.mem_map_of_mem K.subtype hmemN
  · intro a ha
    have haK : a ∈ K := hA.le ha
    have hconjA : aK * (⟨a, haK⟩ : ↥K) * aK⁻¹ = ⟨a, haK⟩ := by
      apply Subtype.ext
      show (aK : G) * a * (aK : G)⁻¹ = a
      rw [CFSG.Open.IsElemAbelian.comm hEA (Subgroup.mem_subgroupOf.mp haKA) ha]
      group
    have h : π (⟨e * a * e⁻¹, mem_conj_of_inner hA hk hek ha⟩ : ↥K) = π ⟨a, haK⟩ := by
      calc π (⟨e * a * e⁻¹, mem_conj_of_inner hA hk hek ha⟩ : ↥K) =
          π kk * π ⟨a, haK⟩ * (π kk)⁻¹ := by
            simpa [π, N, kk] using pPrimeCore_quotient_conj_eq hA hk hek ha
        _ = π aK * π ⟨a, haK⟩ * (π aK)⁻¹ := by rw [hπa]
        _ = π (aK * (⟨a, haK⟩ : ↥K) * aK⁻¹) := by rw [map_mul, map_mul, map_inv]
        _ = π ⟨a, haK⟩ := by rw [hconjA]
    have heq : (⟨e * a * e⁻¹, mem_conj_of_inner hA hk hek ha⟩ : ↥K) = ⟨a, haK⟩ :=
      pPrimeCore_quotient_injOn_of_isSylowOf hA (Subgroup.mem_subgroupOf.mpr (heA a ha))
        (Subgroup.mem_subgroupOf.mpr ha) h
    simpa using congrArg Subtype.val heq

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
