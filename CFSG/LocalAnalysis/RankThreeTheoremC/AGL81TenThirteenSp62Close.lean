module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenSp62Shape
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseDefs
public import CFSG.RankThree.PartTwo.Sec21.Item234
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseCore
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseXfer
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseBlock
import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3
import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Comp
import CFSG.LocalAnalysis.LyonsUnitaryFour.Fusion
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux
import CFSG.LocalAnalysis.AGLEmbedding.Sp48DataDefs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockTargets
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRGN
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenResidueDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.RankThree.PartTwo.Sec21 (GL83StronglyEmbeddedThreeSolvable)

variable {G : Type} [Group G] [Finite G]

theorem sp62_mem_normalizer_of_component {X : Type} [Group X] [Finite X] {L A : Subgroup X}
    (hL : IsComponentOf L ⊤) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center L)) (hAL : A ≤ L)
    (hA3 : IsPGroup 3 A) (hA1 : A ≠ ⊥) {g : X} (hg : g ∈ normalizer (A : Set X)) :
    g ∈ normalizer (L : Set X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hgL
  set L' := L.map (MulAut.conj g).toMonoidHom with hL'
  have hL'c : IsComponentOf L' ⊤ := isComponentOf_map_conj hL g
  have hne : L' ≠ L := by
    intro h
    apply hgL
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hmem : g * x * g⁻¹ ∈ L' := ⟨x, hx, by simp [MulAut.conj_apply]⟩
      rwa [h] at hmem
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have hyx' : y = x := by simpa using hyx
      exact hyx' ▸ hy
  have hcomm := commute_of_isComponentOf_ne hL'c hL hne
  have hAL' : A ≤ L' := by
    intro a ha
    refine ⟨g⁻¹ * a * g, hAL ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) a).mp ha
    simpa using h1
  have h3A : 3 ∣ Nat.card A := by
    rcases hA3.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hA1
    · exact h
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 h3A
  have haZ : (⟨(a : X), hAL a.2⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcomm (a : X) (hAL' a.2) (y : X) y.2).symm
  apply hZ
  have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.center L) haZ
  rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe, ha] at h1

theorem sp62_weakCore_conj_le {M P : Subgroup G} (hM : GLBWeakCore 3 P ≤ M) {m : G}
    (hm : m ∈ M) : GLBWeakCore 3 (P.map (MulAut.conj m).toMonoidHom) ≤ M := by
  have h1 := map_glbWeakCore_le Nat.prime_three (MulAut.conj m⁻¹).toMonoidHom
    (MulAut.conj m⁻¹).injective (P.map (MulAut.conj m).toMonoidHom)
  have hPP : (P.map (MulAut.conj m).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom = P := by
    rw [Subgroup.map_map]
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hPP] at h1
  intro x hx
  have hx' : (MulAut.conj m⁻¹) x ∈ M := hM (h1 ⟨x, hx, rfl⟩)
  simp only [MulAut.conj_apply, inv_inv] at hx'
  have h2 := M.mul_mem (M.mul_mem hm hx') (M.inv_mem hm)
  simpa [mul_assoc] using h2

theorem sp62_sylow_eq (hKA : KFactOmegaEightMinusAut) (hS : Setting G) {M : Subgroup G}
    (hMloc : IsTwoLocal M) {L R₀ J₀ S : Subgroup G} (hLc : IsComponentOf (barM M L) ⊤)
    {d4 : TauCeti.ValidLieTypeIndex} (hd4 : IsOmegaMinusTwoIndex 4 d4)
    (eL : Nonempty (barM M L ≃* CatGroup d4))
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L))) (hR₀L : R₀ ≤ L) (hR₀M : R₀ ≤ M)
    (hR₀p : IsPGroup 3 R₀) (hR₀c : Nat.card R₀ = 3 ^ 4) (hJR : J₀ ≤ R₀)
    (hJe : IsElemAbelian 3 J₀) (hJc : Nat.card J₀ = 3 ^ 3) (hSp : IsPGroup 3 S) (hRS : R₀ ≤ S)
    (hSM : S ≤ M) : S = R₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hρ
  have hOcop2 := sp62Close_coprime_pCore_two M
  by_contra hne
  have hlt : R₀ < S := lt_of_le_of_ne hRS (Ne.symm hne)
  obtain ⟨x, hxS, hxR, hxN⟩ := exists_mem_normalizer_not_mem_of_lt_three hSp hlt
  have hxM : x ∈ M := hSM hxS
  set D := R₀ ⊔ Subgroup.zpowers x with hD
  have hDS : D ≤ S := sup_le hRS (Subgroup.zpowers_le.mpr hxS)
  have hDM : D ≤ M := hDS.trans hSM
  have hDp : IsPGroup 3 D := hSp.to_le hDS
  have hD5 : 3 ^ 5 ∣ Nat.card D := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hDp
    have h81 : 3 ^ 4 ∣ Nat.card D := hR₀c ▸ Subgroup.card_dvd_of_le le_sup_left
    have hne' : Nat.card D ≠ 3 ^ 4 := by
      intro h
      have hDR : R₀ = D := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hR₀c])
      exact hxR (hDR ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
    rw [hk] at h81 hne' ⊢
    have h4 : 4 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h81
    have h5 : 5 ≤ k := by
      rcases Nat.eq_or_lt_of_le h4 with h | h
      · exact absurd (by rw [← h]) hne'
      · omega
    exact Nat.pow_dvd_pow 3 h5
  set Lb := barM M L with hLb
  set Rb := barM M R₀ with hRbdef
  set Db := barM M D with hDb
  have hDbc : Nat.card Db = Nat.card D := by
    have h1 : Nat.card (barM M D) = Nat.card (D.subgroupOf M) :=
      card_map_mk_of_isPGroup Nat.prime_three _ hOcop2 hDp.comap_subtype
    rw [hDb, h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv]
  have hRbL : Rb ≤ Lb := Subgroup.map_mono (Subgroup.comap_mono hR₀L)
  have hRbp : IsPGroup 3 Rb := hR₀p.comap_subtype.map _
  have hRbc : Nat.card Rb = 3 ^ 4 := by
    have h1 : Nat.card (barM M R₀) = Nat.card (R₀.subgroupOf M) :=
      card_map_mk_of_isPGroup Nat.prime_three _ hOcop2 hR₀p.comap_subtype
    rw [hRbdef, h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀M).toEquiv, hR₀c]
  have hRb1 : Rb ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hRbc
    norm_num at hRbc
  have hxb : ρ ⟨x, hxM⟩ ∈ normalizer (Rb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM hxM hxN
  have hxL : ρ ⟨x, hxM⟩ ∈ normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    sp62_mem_normalizer_of_component hLc hZ hRbL hRbp hRb1 hxb
  have hDN : Db ≤ normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [hDb, CFSG.AGLEmbeddingD2.McLaughlin.barM_sup_eq hR₀M (Subgroup.zpowers_le.mpr hxM)]
    refine sup_le (hRbL.trans Subgroup.le_normalizer) ?_
    rw [barM, map_mk_subgroupOf_zpowers _ hxM]
    exact Subgroup.zpowers_le.mpr hxL
  set NL := normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hNL
  set D' := Db.subgroupOf NL with hD'
  set ψ : ↥D' →* MulAut ↥Lb := Lb.normalizerMonoidHom.comp D'.subtype with hψ
  have hD'c : Nat.card D' = Nat.card Db := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv
  have hDbp : IsPGroup 3 Db := hDp.comap_subtype.map _
  have hD'p : IsPGroup 3 D' := hDbp.comap_subtype
  have hQp : IsPGroup 3 ψ.range := by
    rw [MonoidHom.range_eq_map]
    exact (hD'p.to_subgroup ⊤).map ψ
  have hQ81 : Nat.card ψ.range ∣ 3 ^ 4 := hKA ↥Lb d4 hd4 eL ψ.range hQp
  have hker3 : 3 ∣ Nat.card ψ.ker := by
    have hmul := Subgroup.card_ker_mul_card_range ψ
    rw [hD'c, hDbc] at hmul
    by_contra h3
    have hcop : Nat.Coprime (3 ^ 5) (Nat.card ψ.ker) :=
      Nat.Coprime.pow_left 5 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    have h5 : 3 ^ 5 ∣ Nat.card ψ.range :=
      hcop.dvd_of_dvd_mul_left (hmul ▸ hD5)
    have := Nat.le_of_dvd (by norm_num) (h5.trans hQ81)
    norm_num at this
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 hker3
  set cb : ↥M ⧸ CFSG.pCore 2 ↥M := (((c : ↥D') : ↥NL) : ↥M ⧸ CFSG.pCore 2 ↥M) with hcb
  have hcbord : orderOf cb = 3 := by
    rw [hcb, Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hc
  have hcbC : ∀ l ∈ Lb, l * cb = cb * l := by
    intro l hl
    have hk : ((c : ↥D') : ↥NL) ∈ Lb.normalizerMonoidHom.ker := by
      have hk' : ψ (c : ↥D') = 1 := c.2
      exact hk'
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hk
    exact Subgroup.mem_centralizer_iff.mp hk l hl
  set Eb := barM M J₀ with hEb
  have hEbL : Eb ≤ Lb := Subgroup.map_mono (Subgroup.comap_mono (hJR.trans hR₀L))
  have hEbe : IsElemAbelian 3 Eb :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
      (CFSG.AGLEmbedding.isElemAbelian_subgroupOf hJe M) _
  have hJM : J₀ ≤ M := hJR.trans hR₀M
  have hEbc : Nat.card Eb = 3 ^ 3 := by
    have h1 : Nat.card (barM M J₀) = Nat.card (J₀.subgroupOf M) :=
      card_map_mk_of_isPGroup Nat.prime_three _ hOcop2 (IsPGroup.of_card hJc).comap_subtype
    rw [hEb, h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJM).toEquiv, hJc]
  have hcbE : cb ∉ Eb := by
    intro hcE
    have hcL : cb ∈ Lb := hEbL hcE
    apply hZ
    have hcZ : (⟨cb, hcL⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcbC (y : ↥M ⧸ CFSG.pCore 2 ↥M) y.2)
    have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥Lb) hcZ
    rwa [Subgroup.orderOf_mk, hcbord] at h1
  obtain ⟨hE', hcard⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hEbe hcbord
    (fun e he => hcbC e (hEbL he)) hcbE
  have h4 : 4 ≤ Open.pRank 3 (barM M M) :=
    CFSG.SectionRank.le_pRank (by norm_num) (by
      intro y _
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) y
      exact ⟨m, Subgroup.mem_subgroupOf.mpr m.2, rfl⟩) hE' (by rw [hcard, hEbc]; norm_num)
  have h3 := pRank_barM_le_three_of_setting hS hMloc (le_refl M)
  omega

theorem sp62_frame (hK1 : KFactSp62Frame) {M H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} [K.Normal]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsSpSixTwoIndex d) (eK : Nonempty (K ≃* CatGroup d))
    (hC : Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) = ⊥)
    {R₀ : Subgroup G} (hR : CFSG.Quasithin.IsSylowIn 3 R₀ H) (hRM : R₀ ≤ M)
    (hX0 : d1X0 3 M H ≠ ⊤) :
    ∃ (J : Subgroup G) (b : G), ElemFrame3 R₀ J (Subgroup.zpowers b) ∧ J ≤ H ∧
      48 ∣ (Subgroup.centralizer (J : Set G)).relIndex (Subgroup.normalizer (J : Set G) ⊓ H) ∧
      (Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G)).relIndex
        (Subgroup.normalizer (J : Set G) ⊓ H) = 3 ∧
      ¬ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := primeComplementCore (G := H) 3 with hO
  set π := QuotientGroup.mk' O with hπ
  set Rbar : Sylow 3 (H ⧸ O) := hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O)
    with hRbar
  have hrbar : (Rbar : Subgroup (H ⧸ O)) = (R₀.subgroupOf H).map π := by
    rw [hRbar, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow]
  obtain ⟨Jb, bb, hJbT, hJbel, hJbcard, hJbuniq, hJbcent, hJb48, hbbJ, hbb3, hbbidx, hbbY⟩ :=
    hK1 _ K d hd inferInstance eK hC Rbar
  have hRH : R₀ ≤ H := hR.1
  have hR3 : IsPGroup 3 R₀ := hR.2.1
  have hOcop : Nat.Coprime 3 (Nat.card O) := primeComplementCore_coprime 3
  obtain ⟨J, hJH, hJR, hJmap, hJlift, ψ, -⟩ :=
    exists_lift_of_le_map Nat.prime_three hRH hR3 O hOcop (hJbT.trans hrbar.le)
  have hJ3 : IsPGroup 3 J := hR3.to_le hJR
  have hJel : IsElemAbelian 3 J := isElemAbelian_of_mulEquiv ψ hJbel
  have hJcard : Nat.card J = 3 ^ 3 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact hJbcard
  have hbbR : bb ∈ (R₀.subgroupOf H).map π := hrbar ▸ hJbT hbbJ
  obtain ⟨x, hxR, hxπ⟩ := hbbR
  have hbR : (x : G) ∈ R₀ := Subgroup.mem_subgroupOf.mp hxR
  have hbJ : (x : G) ∈ J := hJlift x hbR (hxπ ▸ hbbJ)
  have hbH : (x : G) ∈ H := x.2
  have hbord : orderOf (x : G) = 3 := by
    rw [← orderOf_mk_eq_of_isPGroup hRH hR3 hbR]
    have : π ⟨(x : G), hRH hbR⟩ = bb := hxπ
    rw [this]
    exact hbb3
  have hBJ : Subgroup.zpowers (x : G) ≤ J := Subgroup.zpowers_le.mpr hbJ
  have hBmap : ((Subgroup.zpowers (x : G)).subgroupOf H).map π = Subgroup.zpowers bb :=
    (map_mk_subgroupOf_zpowers O hbH).trans (by rw [hπ] at hxπ; exact congrArg _ hxπ)
  refine ⟨J, x, ⟨hJR, hJel, hJcard, hBJ, ?_, ?_, ?_⟩, hJH, ?_, ?_, ?_⟩
  ·
    rw [Nat.card_zpowers, hbord]
  ·
    intro J' hJ'R hJ'el hJ'card
    have hJ'H : J' ≤ H := hJ'R.trans hRH
    have hJ'bT : (J'.subgroupOf H).map π ≤ (Rbar : Subgroup (H ⧸ O)) :=
      hrbar ▸ Subgroup.map_mono (Subgroup.comap_mono hJ'R)
    have hJ'bel : IsElemAbelian 3 ((J'.subgroupOf H).map π) :=
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
        (isElemAbelian_subgroupOf hJ'el H) π
    have hJ'bcard : Nat.card ((J'.subgroupOf H).map π) = 3 ^ 3 := by
      have h1 : Nat.card ((J'.subgroupOf H).map π) = Nat.card (J'.subgroupOf H) :=
        card_map_mk_of_isPGroup Nat.prime_three O hOcop (hR3.to_le hJ'R).comap_subtype
      rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ'H).toEquiv]
      exact hJ'card
    have heq : (J'.subgroupOf H).map π = Jb := hJbuniq _ hJ'bT hJ'bel hJ'bcard
    have hJ'J : J' ≤ J := fun y hy =>
      hJlift ⟨y, hJ'H hy⟩ (hJ'R hy)
        (heq ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy))
    exact Subgroup.eq_of_le_of_card_ge hJ'J (by rw [hJ'card, hJcard])
  ·
    rintro y ⟨hyR, hyC⟩
    have hyH : y ∈ H := hRH hyR
    have hmem : π ⟨y, hyH⟩ ∈ (Rbar : Subgroup (H ⧸ O)) ⊓ Subgroup.centralizer (Jb : Set _) :=
      ⟨hrbar ▸ ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hyR, rfl⟩,
        Subgroup.mem_centralizer_iff.mpr fun jb hjb => by
          rw [← hJmap] at hjb
          obtain ⟨j, hj, rfl⟩ := hjb
          have hcomm := Subgroup.mem_centralizer_iff.mp hyC j (Subgroup.mem_subgroupOf.mp hj)
          rw [← map_mul, ← map_mul]
          exact congrArg π (Subtype.ext hcomm)⟩
    exact hJlift ⟨y, hyH⟩ hyR (hJbcent hmem)
  ·
    have h3 := relIndex_centralizer_eq_of_quotient Nat.prime_three O hOcop hJH hJ3
    rw [hJmap] at h3
    rw [h3]
    exact hJb48
  ·
    have h4 := relIndex_normalizer_eq_of_quotient Nat.prime_three O hOcop hJH hBJ hJ3
    rw [hBmap, hJmap] at h4
    rw [h4]
    exact hbbidx
  ·
    intro hCM
    have hX0T : (Rbar : Subgroup (H ⧸ O)) ≤ ((H ⊓ M).subgroupOf H).map π :=
      hrbar ▸ Subgroup.map_mono (Subgroup.comap_mono (le_inf hRH hRM))
    refine hbbY _ hX0T hX0 fun y hy => ?_
    have he : IsPGroup 3 (Subgroup.zpowers x) :=
      hR3.comap_subtype.to_le (Subgroup.zpowers_le.mpr hxR)
    have hy' : y ∈ Subgroup.centralizer ({π x} : Set (H ⧸ O)) := by
      rw [hxπ]
      exact hy
    obtain ⟨g, hg, rfl⟩ := exists_mem_centralizer_mk_eq Nat.prime_three O hOcop he hy'
    have hgc : (g : G) * (x : G) = (x : G) * (g : G) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
    have hgC : (g : G) ∈
        Subgroup.centralizer ((Subgroup.zpowers (x : G) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact ((Commute.zpow_left (Commute.symm (show Commute (g : G) (x : G) from hgc)) k).eq)
    exact ⟨g, Subgroup.mem_subgroupOf.mpr ⟨g.2, hCM hgC⟩, rfl⟩

theorem sp62_normBound_section (hK2 : KFactOmega8Frame) {M L J : Subgroup G} {b : G}
    (hLc : IsComponentOf (barM M L) ⊤) {d4 : TauCeti.ValidLieTypeIndex}
    (hd4 : IsOmegaMinusTwoIndex 4 d4) (eL : Nonempty (barM M L ≃* CatGroup d4))
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L))) (hJL : J ≤ L) (hJM : J ≤ M)
    (hJe : IsElemAbelian 3 J) (hJc : Nat.card J = 3 ^ 3)
    (hN : Subgroup.normalizer (J : Set G) ≤ M) (hbJ : b ∈ J) (hb3 : orderOf b = 3) :
    (Subgroup.centralizer (J : Set G)).relIndex (Subgroup.normalizer (J : Set G)) ∣ 48 ∧
      ((Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G)).relIndex
          (Subgroup.normalizer (J : Set G)) = 3 →
        ∃ (W : Subgroup G) (Wb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (φ : ↥W →* ↥Wb),
          W ≤ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) ⊓ M ∧
          Function.Surjective φ ∧ IsSimpleGroup ↥Wb ∧ (∃ x y : Wb, x * y ≠ y * x) ∧
          3 ∣ Nat.card Wb) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hρ
  have hOcop2 := sp62Close_coprime_pCore_two M
  have hJ3 : IsPGroup 3 J := IsPGroup.of_card hJc
  set Lb := barM M L with hLb
  set Jb := barM M J with hJb
  have hJbL : Jb ≤ Lb := Subgroup.map_mono (Subgroup.comap_mono hJL)
  have hJbe : IsElemAbelian 3 Jb :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
      (isElemAbelian_subgroupOf hJe M) _
  have hJbc : Nat.card Jb = 3 ^ 3 := by
    have h1 : Nat.card (barM M J) = Nat.card (J.subgroupOf M) :=
      card_map_mk_of_isPGroup Nat.prime_three _ hOcop2 hJ3.comap_subtype
    rw [hJb, h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJM).toEquiv, hJc]
  have hJbp : IsPGroup 3 Jb := IsPGroup.of_card hJbc
  have hJb1 : Jb ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hJbc
    norm_num at hJbc
  set NL := Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hNL
  have hNJ : Subgroup.normalizer (Jb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ NL := fun g hg =>
    sp62_mem_normalizer_of_component hLc hZ hJbL hJbp hJb1 hg
  have hLNL : Lb ≤ NL := Subgroup.le_normalizer
  have hJNL : Jb ≤ NL := hJbL.trans hLNL
  set L' := Lb.subgroupOf NL with hL'
  haveI hL'n : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLNL).mpr le_rfl
  have eL' : Nonempty (↥L' ≃* CatGroup d4) := by
    obtain ⟨e⟩ := eL
    exact ⟨(Subgroup.subgroupOfEquivOfLe hLNL).trans e⟩
  set J' := Jb.subgroupOf NL with hJ'
  have hJ'L : J' ≤ L' := Subgroup.comap_mono hJbL
  have hJ'e : IsElemAbelian 3 J' := isElemAbelian_subgroupOf hJbe NL
  have hJ'c : Nat.card J' = 3 ^ 3 := by
    rw [hJ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJNL).toEquiv, hJbc]
  obtain ⟨h48', hsec'⟩ := hK2 ↥NL L' d4 hd4 hL'n eL' J' hJ'L hJ'e hJ'c
  have hNM : Subgroup.normalizer (J : Set G) ⊓ M = Subgroup.normalizer (J : Set G) :=
    inf_eq_left.mpr hN
  have hJbNL : Subgroup.normalizer (Jb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓ NL =
      Subgroup.normalizer (Jb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := inf_eq_left.mpr hNJ
  have hq1 : (Subgroup.centralizer (J : Set G)).relIndex (Subgroup.normalizer (J : Set G)) =
      (Subgroup.centralizer (Jb : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex
        (Subgroup.normalizer (Jb : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := by
    have h := relIndex_centralizer_eq_of_quotient Nat.prime_three (CFSG.pCore 2 ↥M) hOcop2 hJM hJ3
    rw [hNM] at h
    exact h
  have hq2 := relIndex_centralizer_eq_subgroupOf (A := NL) hJNL
  rw [hJbNL] at hq2
  refine ⟨?_, ?_⟩
  · rw [hq1, hq2]
    exact h48'
  · intro hidx
    have hBJ : Subgroup.zpowers b ≤ J := Subgroup.zpowers_le.mpr hbJ
    have hbM : b ∈ M := hJM hbJ
    have h4 := relIndex_normalizer_eq_of_quotient Nat.prime_three (CFSG.pCore 2 ↥M) hOcop2 hJM
      hBJ hJ3
    rw [hNM, hidx, map_mk_subgroupOf_zpowers _ hbM] at h4
    set bb := ρ ⟨b, hbM⟩ with hbb
    have hbbJ : bb ∈ Jb := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbJ)
    have hbbNL : bb ∈ NL := hJNL hbbJ
    have h5 := relIndex_normalizer_eq_subgroupOf (A := NL) hJNL (Subgroup.zpowers_le.mpr hbbJ)
    rw [hJbNL] at h5
    have hzp : (Subgroup.zpowers bb).subgroupOf NL = Subgroup.zpowers (⟨bb, hbbNL⟩ : ↥NL) := by
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by simpa using hk)⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    rw [hzp] at h5
    have hBcard : Nat.card (Subgroup.zpowers bb) = 3 := by
      have h1 : Nat.card (((Subgroup.zpowers b).subgroupOf M).map ρ) =
          Nat.card ((Subgroup.zpowers b).subgroupOf M) :=
        card_map_mk_of_isPGroup Nat.prime_three _ hOcop2 (hJ3.to_le hBJ).comap_subtype
      rw [← map_mk_subgroupOf_zpowers (CFSG.pCore 2 ↥M) hbM, h1,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBJ.trans hJM)).toEquiv,
        Nat.card_zpowers, hb3]
    have hbb3 : orderOf (⟨bb, hbbNL⟩ : ↥NL) = 3 := by
      rw [Subgroup.orderOf_mk, ← Nat.card_zpowers, hBcard]
    obtain ⟨W', hW'L, hW's, hW'na, hW'3⟩ :=
      hsec' ⟨bb, hbbNL⟩ (Subgroup.mem_subgroupOf.mpr hbbJ) hbb3 (h5.symm.trans h4.symm)
    set Wb := W'.map NL.subtype with hWb
    have eW : ↥W' ≃* ↥Wb := Subgroup.equivMapOfInjective W' NL.subtype NL.subtype_injective
    have hWbs : IsSimpleGroup ↥Wb := (MulEquiv.isSimpleGroup_congr eW).mp hW's
    have hWbna : ∃ x y : Wb, x * y ≠ y * x := by
      obtain ⟨x, y, hxy⟩ := hW'na
      exact ⟨eW x, eW y, fun h => hxy (eW.injective (by rw [map_mul, map_mul, h]))⟩
    have hWb3 : 3 ∣ Nat.card Wb := by
      rw [← Nat.card_congr eW.toEquiv]
      exact hW'3
    have hWbC : Wb ≤ Subgroup.centralizer ({bb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rintro _ ⟨w, hw, rfl⟩
      have hwC : w ∈ Subgroup.centralizer ({⟨bb, hbbNL⟩} : Set ↥NL) := (hW'L hw).2
      rw [Subgroup.mem_centralizer_singleton_iff] at hwC ⊢
      exact congrArg Subtype.val hwC
    have he : IsPGroup 3 (Subgroup.zpowers (⟨b, hbM⟩ : ↥M)) :=
      (hJ3.comap_subtype (K := M)).to_le
        (Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr hbJ))
    set W₁ : Subgroup ↥M :=
      Subgroup.centralizer ({(⟨b, hbM⟩ : ↥M)} : Set ↥M) ⊓ Wb.comap ρ with hW₁
    let φ' : ↥W₁ →* ↥Wb := (ρ.comp W₁.subtype).codRestrict Wb fun w => w.2.2
    have hφ' : Function.Surjective φ' := by
      rintro ⟨y, hy⟩
      obtain ⟨g, hg, hgy⟩ := exists_mem_centralizer_mk_eq Nat.prime_three (CFSG.pCore 2 ↥M)
        hOcop2 he (hWbC hy)
      have hρg : ρ g = y := hgy
      have hgW : g ∈ W₁ :=
        Subgroup.mem_inf.mpr ⟨hg, Subgroup.mem_comap.mpr (by rw [hρg]; exact hy)⟩
      exact ⟨⟨g, hgW⟩, Subtype.ext hρg⟩
    let ι := Subgroup.equivMapOfInjective W₁ M.subtype M.subtype_injective
    refine ⟨W₁.map M.subtype, Wb, φ'.comp ι.symm.toMonoidHom, ?_, hφ'.comp ι.symm.surjective,
      hWbs, hWbna, hWb3⟩
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun h hh => ?_, w.2⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc' : (w : G) * b = b * (w : G) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hw.1)
    exact (Commute.zpow_left (Commute.symm (show Commute (w : G) b from hc')) k).eq

variable (G) in
theorem agl81TenThirteenSp62_of (hGL : GL83StronglyEmbeddedThreeSolvable)
    (hLoc : KFactSp62CfgLocal) (hK1 : KFactSp62Frame) (hK2 : KFactOmega8Frame)
    (hLevi : KFactBlockLeviU42) (hKA : KFactOmegaEightMinusAut) (hU : KFactU62ThreeRank)
    (hΩ : KFactOmegaMinusThreeRank) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hNX3 : D1NoXBlock3 G)
    (h98 : AGL81NineEightFour G) : AGL81TenThirteenSp62 G := by
  intro hS P M H Q K hd L hL I₀ hI₀ hI₀c hN q dK dJ hqp hqe hdK hdJ eK f hf hker
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G := noXBlockFor_of_setting hNX3 hS
  have hdK' : IsSpSixTwoIndex dK := ⟨q, hqp, hqe, hdK⟩
  have hdJ' : IsUFourTwoIndex dJ := ⟨q, hqp, hqe, hdJ⟩
  haveI := sp62_normal hd
  obtain ⟨⟨d4, hd4, eL⟩, hZ⟩ := sp62_omegaEight hLoc hLevi hU hΩ h84 h85 h86 h93 hD2 h98 hS
    hd hL hI₀ hI₀c hN hdK' hdJ' eK f hf hker
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hMloc : IsTwoLocal M := he.maxTwoLocal_M.1
  have hLM : IsSubnormal L M := hL.subnormal
  have hI₀M : I₀ ≤ H ⊓ M := le_inf_of_cZero hLM hI₀
  have hI₀HL : I₀ ≤ H ⊓ L := hI₀.le
  have hI₀H : I₀ ≤ H := hI₀M.trans inf_le_left
  have hC := sp62_centralizer_eq_bot hLoc hS hd hdK' eK
  have hH5 := sp62_not_dvd_card hLoc hS hd hdK' eK
  have h25 : 25920 ∣ Nat.card ((I₀.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3))) := by
    have h := sp62_card_dvd_image hC hI₀H f hf hker
    rwa [(LeviBlock.catGroup_u42_facts hdJ').1] at h
  obtain ⟨R₀, J₀, hR₀I, hR₀p, hR₀c, hJR, hJe, hJc⟩ :=
    sp62_sylow_lift hLoc hS hd hdK' eK hI₀H ((show 3 ^ 4 ∣ 25920 by norm_num).trans h25)
  have hR₀H : R₀ ≤ H := hR₀I.trans hI₀H
  have hR₀M : R₀ ≤ M := hR₀I.trans (hI₀M.trans inf_le_right)
  have hR₀L : R₀ ≤ L := hR₀I.trans (hI₀HL.trans inf_le_right)
  obtain ⟨c, hcM, hc⟩ := CFSG.LyonsUnitaryFour.exists_conj_le_sylow_of_le P he.sylow_le hR₀M hR₀p
  set P' := (P : Subgroup G).map (MulAut.conj c⁻¹).toMonoidHom with hP'
  have hRP' : R₀ ≤ P' := fun r hr =>
    ⟨c * r * c⁻¹, hc r hr, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hP'M : P' ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    have hxM := he.sylow_le hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact M.mul_mem (M.mul_mem (M.inv_mem hcM) hxM) hcM
  have hP'p : IsPGroup 3 P' := P.isPGroup'.map _
  have hP'eq : P' = R₀ := sp62_sylow_eq hKA hS hMloc hL.component hd4 eL hZ hR₀L hR₀M hR₀p hR₀c
    hJR hJe hJc hP'p hRP' hP'M
  have hW : GLBWeakCore 3 R₀ ≤ M := hP'eq ▸ sp62_weakCore_conj_le he.weakCore_le (M.inv_mem hcM)
  set PR : Sylow 3 G := c⁻¹ • P with hPR
  have hPReq : (PR : Subgroup G) = R₀ := by
    rw [hPR, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, ← hP'eq, hP']
    rfl
  have hRsyl : CFSG.Quasithin.IsSylowIn 3 R₀ H := by
    refine ⟨hR₀H, hR₀p, fun h3 => hH5 ?_⟩
    have hmul := Subgroup.relIndex_mul_card (H := R₀) (K := H)
    rw [inf_eq_left.mpr hR₀H, hR₀c] at hmul
    rw [← hmul]
    obtain ⟨k, hk⟩ := h3
    rw [hk, show 3 ^ 5 = 3 * 3 ^ 4 by norm_num, mul_assoc]
    exact Nat.mul_dvd_mul_left 3 (Dvd.intro_left k rfl)
  have hX0 : d1X0 3 M H ≠ ⊤ := fun h => hd.not_le_X0 (by rw [h]; exact le_top)
  obtain ⟨J, b, hF, hJH, h48H, hidxH, hCB⟩ := sp62_frame hK1 hdK' eK hC hRsyl hR₀M hX0
  have hJM : J ≤ M := hF.le_P.trans hR₀M
  have hJL : J ≤ L := hF.le_P.trans hR₀L
  have hNJ : Subgroup.normalizer (J : Set G) ≤ M :=
    normalizer_le_of_isElemAbelian_three_cube hW hF.le_P hF.elem hF.card_J
  have hbJ : b ∈ J := hF.le_J (Subgroup.mem_zpowers b)
  have hbord : orderOf b = 3 := by rw [← Nat.card_zpowers, hF.card_B]
  obtain ⟨h48, hsec⟩ := sp62_normBound_section hK2 hL.component hd4 eL hZ hJL hJM hF.elem
    hF.card_J hNJ hbJ hbord
  have hCn : ((Subgroup.centralizer (J : Set G)).subgroupOf
      (Subgroup.normalizer (J : Set G))).Normal := by
    rw [← Subgroup.normalizerMonoidHom_ker]
    infer_instance
  have hCS : Subgroup.centralizer (J : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) :=
    (Subgroup.centralizer_le hF.le_J).trans (Subgroup.centralizer_le_normalizer _)
  have hidx : (Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer (J : Set G)) = 3 := by
    rw [relIndex_eq_of_cover3 (A := Subgroup.normalizer (J : Set G) ⊓ H) inf_le_left hCS
      (h48.trans h48H)]
    exact hidxH
  obtain ⟨W, Wb, φ, hWC, hφ, hWbs, hWbna, hWb3⟩ := hsec hidx
  have hF' : ElemFrame3 (PR : Subgroup G) J (Subgroup.zpowers b) := hPReq ▸ hF
  have := hWbs
  exact false_of_simple_quotient_inf_centralizer3 hGL hS (P := PR) (hPReq ▸ hR₀M) (hPReq ▸ hW)
    hF'.le_P hF.elem hF.card_J hF.le_J hF.card_B (sylow_of_elemFrame3 hF' h48 hidx) hCB hWC
    hWbna φ hφ hWb3

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
