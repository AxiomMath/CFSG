module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
public import Certificates.Certificate31064
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2HeisSound
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSporMax
import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Aux
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.RankThree.PartOne.KS.HeSevenCentralizers
import CFSG.Sporadic.Bridge.HeSurj
public import CFSG.RankThree.PartOne.KS.HeSevenData
public import CFSG.Sporadic.He
public import CFSG.Sporadic.HeldB.CertPChain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem card_inf_centralizer_eq_card_center {G : Type*} [Group G] (H : Subgroup G) :
    Nat.card (H ⊓ centralizer (H : Set G) : Subgroup G) = Nat.card (center H) := by
  have h : (center H).map H.subtype = H ⊓ centralizer (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, mem_centralizer_iff.mpr fun t ht =>
        congrArg Subtype.val (mem_center_iff.mp hy ⟨t, ht⟩)⟩
    · rintro ⟨hxH, hxC⟩
      exact ⟨⟨x, hxH⟩, mem_center_iff.mpr fun t =>
        Subtype.ext (mem_centralizer_iff.mp hxC t t.2), rfl⟩
  rw [← h, card_map_of_injective H.subtype_injective]

theorem pRank_and_card_inf_centralizer_of_card_cube {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {T : Subgroup G} (hT : Nat.card T = p ^ 3) (hexp : ∀ x ∈ T, x ^ p = 1)
    (hnab : ∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x) :
    2 ≤ CFSG.Open.pRank p T ∧
      Nat.card (T ⊓ centralizer (T : Set G) : Subgroup G) = p := by
  have hp : p.Prime := Fact.out
  obtain ⟨B, hBT, hB, hBc⟩ := exists_isElemAbelian_card_sq_of_card_cube hT hexp
  refine ⟨CFSG.SectionRank.le_pRank hp.one_lt hBT hB hBc, ?_⟩
  rw [card_inf_centralizer_eq_card_center]
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  exact Generic49U3.card_center_of_nonabelian_card_p_cube hT fun h =>
    hxy (congrArg Subtype.val (h.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))

section HeSylow

open CFSG.RankThree.PartOne CFSG.Sporadic.HeldB

theorem heSeven_sylow_shape
    {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .He).Group)) (T : Sylow 7 K) :
    Nat.card (T : Subgroup K) = 7 ^ 3 ∧ (∀ x ∈ (T : Subgroup K), x ^ 7 = 1) ∧
      ∃ x ∈ (T : Subgroup K), ∃ y ∈ (T : Subgroup K), x * y ≠ y * x := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨⟨-, -, -, -⟩, -, -, -, -, -, -, -, ⟨hA0C, -, hA0P, hA0c, hA0e, hAcard, -⟩, -, -⟩ :=
    R3E_He_full_seven_centralizer_structures
  obtain ⟨e⟩ := nonempty_mulEquiv_carrier_of_sporadicIndex (s := .He)
    CFSG.Sporadic.Bridge.He.nonempty_mulEquiv hK
  set A : Subgroup heP := heSevenA0.subgroupOf heP with hAdef
  have hAc : Nat.card A = 7 ^ 3 := by
    rw [hAdef, Nat.card_congr (subgroupOfEquivOfLe hA0P).toEquiv, hA0c]
    norm_num
  have hAp : IsPGroup 7 A := IsPGroup.of_card hAc
  have hAidx : ¬ 7 ∣ A.index := by
    have h1 := A.card_mul_index
    rw [hAc, card_heP] at h1
    have h2 : A.index = 11750400 := by omega
    rw [h2]
    norm_num
  obtain ⟨Φ, hΦ⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_mulEquiv_map_eq_sylow
    (e.trans heEquivP) hAp hAidx T
  have hAexp : ∀ x ∈ heSevenA0, x ^ 7 = 1 := fun x hx => by
    have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : heSevenA0)
    rw [hA0e] at h
    exact congrArg Subtype.val h
  have hAnab : ∃ x ∈ heSevenA0, ∃ y ∈ heSevenA0, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hle : heSevenA0 ≤ centralizer (heSevenA0 : Set (Equiv.Perm (Fin 8330))) ⊓ heSevenC0 :=
      fun x hx => ⟨mem_centralizer_iff.mpr fun y hy => hcon y hy x hx, hA0C hx⟩
    have := Subgroup.card_le_of_le hle
    rw [hA0c, hAcard] at this
    norm_num at this
  refine ⟨by rw [hΦ, card_map_of_injective Φ.injective, hAc], ?_, ?_⟩
  · rw [hΦ]
    rintro _ ⟨y, hy, rfl⟩
    have h1 : (y : Equiv.Perm (Fin 8330)) ^ 7 = 1 := hAexp _ (mem_subgroupOf.mp hy)
    have h2 : y ^ 7 = 1 := Subtype.ext (by simpa using h1)
    simp [← map_pow, h2]
  · obtain ⟨x, hx, y, hy, hxy⟩ := hAnab
    rw [hΦ]
    refine ⟨Φ ⟨x, hA0P hx⟩, ⟨⟨x, hA0P hx⟩, mem_subgroupOf.mpr hx, rfl⟩, Φ ⟨y, hA0P hy⟩,
      ⟨⟨y, hA0P hy⟩, mem_subgroupOf.mpr hy, rfl⟩, fun h => hxy ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (Φ.injective h)

end HeSylow

private theorem sylow_seven_normalizer_of_maximal {K : Type*} [Group K] [Finite K]
    [IsSimpleGroup K] (hKc : Nat.card K = 4030387200) {R : Subgroup K} (hRc : Nat.card R = 6174)
    (hRmax : ∀ Y : Subgroup K, R ≤ Y → Y = R ∨ Y = ⊤) (T : Sylow 7 K) :
    Group.IsSolvable (normalizer ((T : Subgroup K) : Set K)) ∧
      ∀ H : Subgroup K, normalizer ((T : Subgroup K) : Set K) ≤ H →
        H = normalizer ((T : Subgroup K) : Set K) ∨ H = ⊤ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 R) := inferInstance
  have h0 : (6174 : ℕ) ≠ 0 := by norm_num
  have hfac : (6174 : ℕ).factorization 7 = 3 := by
    have h1 := (Nat.prime_seven.pow_dvd_iff_le_factorization h0).1 (by norm_num : 7 ^ 3 ∣ 6174)
    have h2 : ¬ 4 ≤ (6174 : ℕ).factorization 7 := fun h => by
      have := (Nat.prime_seven.pow_dvd_iff_le_factorization h0).2 h
      norm_num at this
    omega
  have hPc : Nat.card (P : Subgroup R) = 7 ^ 3 := by
    rw [Sylow.card_eq_multiplicity P, hRc, hfac]
  have hPidx : (P : Subgroup R).index = 18 := by
    have h1 := (P : Subgroup R).card_mul_index
    rw [hPc, hRc] at h1
    omega
  have hone : Nat.card (Sylow 7 R) = 1 := by
    have hdvd : Nat.card (Sylow 7 R) ∣ 18 := hPidx ▸ Sylow.card_dvd_index P
    have hmod : Nat.card (Sylow 7 R) % 7 = 1 := card_sylow_modEq_one (p := 7) (G := R)
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Sylow 7 R) = m at hdvd hmod hle ⊢
    interval_cases m <;> omega
  have hPn : (P : Subgroup R).Normal := by
    haveI : Subsingleton (Sylow 7 R) := (Nat.card_eq_one_iff_unique.mp hone).1
    exact Sylow.normal_of_subsingleton P
  set T₀ : Subgroup K := (P : Subgroup R).map R.subtype with hT₀
  have hT₀c : Nat.card T₀ = 7 ^ 3 := by
    rw [hT₀, card_map_of_injective R.subtype_injective, hPc]
  have hT₀R : T₀ ≤ R := map_subtype_le _
  have hRN : R ≤ normalizer (T₀ : Set K) := by
    intro r hr
    rw [mem_normalizer_iff]
    intro t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨r, hr⟩ * u * ⟨r, hr⟩⁻¹, hPn.conj_mem u hu ⟨r, hr⟩, rfl⟩
    · rintro ⟨u, hu, hut⟩
      have hut' : (u : K) = r * t * r⁻¹ := hut
      have ht : t ∈ R := by
        have h2 := R.mul_mem (R.mul_mem (R.inv_mem hr) (hut' ▸ u.2 : r * t * r⁻¹ ∈ R)) hr
        rwa [show r⁻¹ * (r * t * r⁻¹) * r = t by group] at h2
      refine ⟨⟨t, ht⟩, ?_, rfl⟩
      have h1 := hPn.conj_mem u hu ⟨r, hr⟩⁻¹
      have h2 : (⟨r, hr⟩⁻¹ * u * (⟨r, hr⟩⁻¹)⁻¹ : R) = ⟨t, ht⟩ := by
        refine Subtype.ext ?_
        change r⁻¹ * (u : K) * r⁻¹⁻¹ = t
        rw [hut']
        group
      rwa [h2] at h1
  have hNtop : normalizer (T₀ : Set K) ≠ ⊤ := by
    intro htop
    haveI : T₀.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T₀ with h | h
    · rw [h, card_bot] at hT₀c
      norm_num at hT₀c
    · rw [h, card_top, hKc] at hT₀c
      norm_num at hT₀c
  have hNR : normalizer (T₀ : Set K) = R :=
    (hRmax _ hRN).resolve_right hNtop
  have hRsol : Group.IsSolvable R :=
    CFSG.AGLEmbedding.MaxD2.isSolvable_of_normal_pow (k := 3) (a := 1) (b := 2)
      Nat.prime_seven hT₀R hRN hT₀c (by rw [hRc]; norm_num)
  have hT₀idx : ¬ 7 ∣ (T₀.subgroupOf ⊤).index := by
    change ¬ 7 ∣ T₀.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have h1 := T₀.card_mul_index
    rw [hT₀c, hKc] at h1
    have h2 : T₀.index = 11750400 := by omega
    rw [h2]
    norm_num
  have hKfac : (4030387200 : ℕ).factorization 7 = 3 := by
    have h0' : (4030387200 : ℕ) ≠ 0 := by norm_num
    have h1 := (Nat.prime_seven.pow_dvd_iff_le_factorization h0').1
      (by norm_num : 7 ^ 3 ∣ 4030387200)
    have h2 : ¬ 4 ≤ (4030387200 : ℕ).factorization 7 := fun h => by
      have := (Nat.prime_seven.pow_dvd_iff_le_factorization h0').2 h
      norm_num at this
    omega
  obtain ⟨l, -, hl⟩ := CFSG.AGLEmbedding.exists_mem_map_conj_eq_of_card_eq (L := ⊤) le_top le_top
    (IsPGroup.of_card hT₀c) T.isPGroup' hT₀idx
    (by rw [Sylow.card_eq_multiplicity T, hKc, hT₀c, hKfac])
  have hNT : normalizer ((T : Subgroup K) : Set K) = R.map (MulAut.conj l).toMonoidHom := by
    rw [← hl, ← map_equiv_normalizer_eq, hNR]
  rw [hNT]
  refine ⟨?_, fun H hH => ?_⟩
  · haveI := hRsol
    exact Group.isSolvable_of_surjective
      (f := (R.equivMapOfInjective (MulAut.conj l).toMonoidHom
        (MulAut.conj l).injective).toMonoidHom) (MulEquiv.surjective _)
  · have hle : R ≤ H.map (MulAut.conj l).symm.toMonoidHom := by
      intro r hr
      exact ⟨MulAut.conj l r, hH ⟨r, hr, rfl⟩, by simp only [MulEquiv.coe_toMonoidHom,
        MulAut.conj_symm_apply, MulAut.conj_apply]; group⟩
    rcases hRmax _ hle with h | h
    · left
      rw [← h, map_map]
      convert (map_id H).symm
      ext x
      simp
    · right
      rw [eq_top_iff]
      intro x _
      have : (MulAut.conj l).symm x ∈ H.map (MulAut.conj l).symm.toMonoidHom := h ▸ mem_top _
      obtain ⟨y, hy, hyx⟩ := this
      rwa [show y = x from (MulAut.conj l).symm.injective hyx] at hy

section HeNormalizer

open CFSG.Sporadic.He (J card_J heEquivJ)

private theorem exists_maximal_of_mulEquiv {A A' : Type*} [Group A] [Group A'] {n : ℕ}
    (e : A ≃* A') (h : ∃ R : Subgroup A, Nat.card R = n ∧ ∀ Y : Subgroup A, R ≤ Y → Y = R ∨ Y = ⊤) :
    ∃ R : Subgroup A', Nat.card R = n ∧ ∀ Y : Subgroup A', R ≤ Y → Y = R ∨ Y = ⊤ := by
  obtain ⟨R, hRc, hRmax⟩ := h
  refine ⟨R.map e.toMonoidHom, by rw [card_map_of_injective e.injective, hRc], fun Y hY => ?_⟩
  have hle : R ≤ Y.map e.symm.toMonoidHom := by
    intro r hr
    exact ⟨e r, hY ⟨r, hr, rfl⟩, by simp⟩
  rcases hRmax _ hle with h | h
  · left
    rw [← h, map_map]
    convert (map_id Y).symm
    ext x
    simp
  · right
    rw [eq_top_iff]
    intro x _
    have : e.symm x ∈ Y.map e.symm.toMonoidHom := h ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := this
    rwa [show y = x from e.symm.injective hyx] at hy

theorem heSeven_normalizer_facts_of
    (hmax : ∃ R : Subgroup J, Nat.card R = 6174 ∧ ∀ Y : Subgroup J, R ≤ Y → Y = R ∨ Y = ⊤)
    {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .He).Group)) (T : Sylow 7 K) :
    Group.IsSolvable (normalizer ((T : Subgroup K) : Set K)) ∧
      ∀ H : Subgroup K, normalizer ((T : Subgroup K) : Set K) ≤ H →
        H = normalizer ((T : Subgroup K) : Set K) ∨ H = ⊤ := by
  have hN := exists_maximal_of_mulEquiv (A := ↥J) (A' := CFSG.Blueprint.NativeSporadic.He)
    heEquivJ.symm hmax
  obtain ⟨eK⟩ := nonempty_mulEquiv_carrier_of_sporadicIndex (s := .He)
    CFSG.Sporadic.Bridge.He.nonempty_mulEquiv hK
  obtain ⟨R, hRc, hRmax⟩ := exists_maximal_of_mulEquiv
    (A := CFSG.Blueprint.NativeSporadic.Carrier .He) (A' := K) eK.symm hN
  haveI : IsSimpleGroup K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He eK
  have hKc : Nat.card K = 4030387200 := by
    rw [Nat.card_congr eK.toEquiv]
    exact CFSG.Sporadic.He.card_He
  exact sylow_seven_normalizer_of_maximal hKc hRc hRmax T

theorem heSeven_maximal_J :
    ∃ R : Subgroup J, Nat.card R = 6174 ∧ ∀ Y : Subgroup J, R ≤ Y → Y = R ∨ Y = ⊤ :=
  Certificates.certificate31064

end HeNormalizer

theorem threeFourTwoNoneAt_he :
    ThreeFourTwoNoneAt 7 (TauCeti.CFSGIndex.sporadic .He).Group := by
  have hO : Nat.card (Outer (CFSG.Blueprint.NativeSporadic.Carrier .He)) ≤ 2 :=
    CFSG.Sporadic.Schreier.AT_He_Schreier.1
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
    CFSG.Sporadic.He.fam_he_simplicity.1
  have hsq : 7 ^ 2 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) := by
    show 7 ^ 2 ∣ Nat.card CFSG.Blueprint.NativeSporadic.He
    rw [CFSG.Sporadic.He.card_He]
    norm_num
  obtain ⟨hX, hnab, hout⟩ := sporadicIndex_facts_of_bridge (s := .He)
    CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
    CFSG.Sporadic.He.fam_he_simplicity.2.2 hO (by norm_num) hsq
  refine threeFourTwoNoneAt_of_normalizer_maximal hX hnab hout fun K _ _ hK => ?_
  obtain ⟨e⟩ := nonempty_mulEquiv_carrier_of_sporadicIndex (s := .He)
    CFSG.Sporadic.Bridge.He.nonempty_mulEquiv hK
  haveI : Finite (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .He)) := MulEquiv.finite_left
  refine ⟨?_, fun T => ?_⟩
  · rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact (isSolvable_and_not_dvd_of_card_le_two hO (by norm_num) (by norm_num)).2
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hc, hexp, hnc⟩ := heSeven_sylow_shape hK T
  obtain ⟨h2, hZ⟩ := pRank_and_card_inf_centralizer_of_card_cube hc hexp hnc
  obtain ⟨hsol, hmax⟩ := heSeven_normalizer_facts_of heSeven_maximal_J hK T
  exact ⟨h2, hZ, hsol, hmax⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
