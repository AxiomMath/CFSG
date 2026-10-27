module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.SteinbergBNPair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Omega8Step3
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviFam
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.Lie

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.GroupTheory.TitsSystem CFSG.GH74.BNPair
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section General

variable {K Y : Type*} [Group K] [Group Y] [Finite K] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem _root_.CFSG.AGLEmbedding.ParabHub.BorelQuotient.normalizer_le_of_normalizer_sylow_le (h : BorelQuotient D n H π M)
    (T : Sylow 2 Y) {J : Subgroup Y}
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) :
    Subgroup.normalizer (J : Set Y) ≤ J := by
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel D H).map π' ≤ J := hNπ ▸ hNJ
  have hBA : borel D H ≤ J.comap π' := Subgroup.map_le_iff_le_comap.mp hBJ
  have := cartan_borel_weylN_normal h.ct h.extras
  have hBN := isBNPair_borel_weylN h.ct h.extras
  obtain ⟨I, hIS, hAI⟩ := hBN.exists_parabolic hBA
  have hNA : Subgroup.normalizer ((J.comap π' : Subgroup K) : Set K) = J.comap π' := by
    rw [hAI]
    exact hBN.normalizer_parabolic hIS
  intro y hy
  obtain ⟨k, rfl⟩ := hπ' y
  have hk : k ∈ Subgroup.normalizer ((J.comap π' : Subgroup K) : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hy (π' a)
  rw [hNA] at hk
  exact hk

end General

theorem statedClassicalModel_of_isOmegaEightPlus {L : Type} [Group L] (h : IsOmegaEightPlus L) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel L .POmegaPlus 4 2 1 := by
  obtain ⟨⟨x, hv⟩, ⟨q, hq, hd⟩, ⟨eL⟩⟩ := h
  obtain rfl : x = TauCeti.LieTypeIndex.D 4 q := hd
  have hp : q.p = 2 := by
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [← TauCeti.PrimePower.card_def, hq] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
  have he : q.exponent = 1 := by
    have h2 : 2 ^ q.exponent = 2 ^ 1 := by
      have h3 := hq
      rw [TauCeti.PrimePower.card_def, hp] at h3
      rw [h3]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv
  have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = 2 ^ 1 := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent, hp,
      he]
  exact ⟨⟨Nat.prime_two, le_rfl, le_refl 4⟩, _, inferInstance, inferInstance, hcard,
    ⟨eL.trans e⟩⟩

open CFSG.LieType.Universal.Spin in
theorem normalizer_le_of_isOmegaEightPlus {Y : Type} [Group Y] [Finite Y]
    (hY : IsOmegaEightPlus Y) (T : Sylow 2 Y) {J : Subgroup Y}
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) :
    Subgroup.normalizer (J : Set Y) ≤ J := by
  obtain ⟨⟨-, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := statedClassicalModel_of_isOmegaEightPlus hY
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have : NeZero 4 := ⟨by norm_num⟩
  have : Finite (spinGroup (quadPlus 4 F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := 4) (K := F))
  exact (borelQuotient_spinPlus (by norm_num : 3 ≤ 4) e).normalizer_le_of_normalizer_sylow_le T hNJ

theorem exists_sylow_of_isSylowTwoOf {X : Type} [Group X] [Finite X] {Lb T₀ : Subgroup X}
    (hT : IsSylowTwoOf T₀ Lb) : ∃ T : Sylow 2 ↥Lb, (T : Subgroup ↥Lb) = T₀.subgroupOf Lb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (T₀.subgroupOf Lb) := hT.2.1.comap_subtype
  exact ⟨hp.toSylow hT.2.2, rfl⟩

theorem omega8_parabolic_le {X : Type} [Group X] [Finite X] {Lb P : Subgroup X}
    (hΩ : IsOmegaEightPlus ↥Lb) (hP : IsParabolicTwo Lb P) :
    Lb ⊓ Subgroup.normalizer (P : Set X) ≤ P := by
  obtain ⟨hPL, T₀, hT₀, hN⟩ := hP
  obtain ⟨T, hT⟩ := exists_sylow_of_isSylowTwoOf hT₀
  have hT₀L : T₀ ≤ Lb := hT₀.1
  have hNJ : Subgroup.normalizer ((T : Subgroup ↥Lb) : Set ↥Lb) ≤ P.subgroupOf Lb := by
    intro y hy
    rw [hT, mem_normalizer_iff_map, Subgroup.map_subgroupOf_eq_of_le hT₀L] at hy
    exact Subgroup.mem_subgroupOf.mpr (hN ⟨y.2, hy⟩)
  have h := normalizer_le_of_isOmegaEightPlus hΩ T hNJ
  rintro x ⟨hxL, hxN⟩
  have hx : (⟨x, hxL⟩ : ↥Lb) ∈ Subgroup.normalizer ((P.subgroupOf Lb : Subgroup ↥Lb) : Set ↥Lb) := by
    rw [mem_normalizer_iff_map, Subgroup.map_subgroupOf_eq_of_le hPL]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp (h hx)

theorem omega8_parabolic_elemAbelian {X : Type} [Group X] [Finite X] {Lb P : Subgroup X}
    (hΩ : IsOmegaEightPlus ↥Lb) (hP : IsParabolicTwo Lb P)
    (hB : ¬ IsSylowTwoOf (pCoreOf 2 P) Lb)
    (hperf : ∀ J : Subgroup X, J ≤ P → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J)
    (hr : Open.pRank 3 P ≤ 2) :
    ∀ E : Subgroup X, E ≤ P → IsPGroup 3 E → IsElemAbelian 3 E ∧ Nat.card E ≤ 9 := by
  obtain ⟨hPL, T₀, hT₀, hN⟩ := hP
  obtain ⟨T, hT⟩ := exists_sylow_of_isSylowTwoOf hT₀
  have hT₀L : T₀ ≤ Lb := hT₀.1
  have hmodel := statedClassicalModel_of_isOmegaEightPlus hΩ
  have hNJ : Subgroup.normalizer ((T : Subgroup ↥Lb) : Set ↥Lb) ≤ P.subgroupOf Lb := by
    intro y hy
    rw [hT, mem_normalizer_iff_map, Subgroup.map_subgroupOf_eq_of_le hT₀L] at hy
    exact Subgroup.mem_subgroupOf.mpr (hN ⟨y.2, hy⟩)
  have hJ : P.subgroupOf Lb ≠ Subgroup.normalizer ((T : Subgroup ↥Lb) : Set ↥Lb) := by
    intro hJeq
    apply hB
    have hPeq : P = Subgroup.normalizer (T₀ : Set X) ⊓ Lb := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hPL, hJeq, map_normalizer_eq_inf, hT,
        Subgroup.map_subgroupOf_eq_of_le hT₀L]
    have hT₀P : T₀ ≤ P := by
      rw [hPeq]
      exact le_inf Subgroup.le_normalizer hT₀L
    have hT₀O : T₀ ≤ pCoreOf 2 P :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hT₀P (hPeq ▸ inf_le_left) hT₀.2.1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨(pCoreOf_le 2 P).trans hPL, pCoreOf_isPGroup 2 P, fun hd => hT₀.2.2 ?_⟩
    exact hd.trans (Subgroup.relIndex_dvd_of_le_left Lb hT₀O)
  have hperf' : ∀ U : Subgroup ↥Lb, U ≤ P.subgroupOf Lb → ⁅U, U⁆ = U →
      Nat.Coprime 3 (Nat.card U) := by
    intro U hU hUp
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    have hle : U.map Lb.subtype ≤ P := by
      rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hU hu)
    have hp : ⁅U.map Lb.subtype, U.map Lb.subtype⁆ = U.map Lb.subtype := by
      rw [← Subgroup.map_commutator, hUp]
    have h3 := hperf _ hle hp
    rwa [Subgroup.card_map_of_injective Lb.subtype_injective] at h3
  have hel := isElemAbelian_of_model_pomegaPlus_two hmodel T (P.subgroupOf Lb) hNJ hJ hperf'
  intro E hEP hE3
  have hEL : E ≤ Lb := hEP.trans hPL
  have hU : E.subgroupOf Lb ≤ P.subgroupOf Lb := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hEP (Subgroup.mem_subgroupOf.mp hx))
  have hEel : IsElemAbelian 3 E := by
    have h1 := elementary_map_injective 3 (E.subgroupOf Lb) Lb.subtype Lb.subtype_injective
      (hel _ hU hE3.comap_subtype)
    rwa [Subgroup.map_subgroupOf_eq_of_le hEL] at h1
  refine ⟨hEel, ?_⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE3
  have hkr : k ≤ Open.pRank 3 P := CFSG.SectionRank.le_pRank (by norm_num) hEP hEel hk
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hkr.trans hr)
    _ = 9 := by norm_num

end CFSG.AGLEmbeddingD2.McLaughlin.Lie
