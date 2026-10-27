module

public import CFSG.GroupTheory.PGroup.PrimePartTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOuterAut
public import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeMain
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barM_zpowers_le_centralizer_of_mem_inf {M H L : Subgroup G} {d : ℕ}
    (hL : IsTwoPrimeComponent M L)
    (hYL : ∀ y ∈ oPPrimeHull d (H ⊓ M), ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 M)
    {x : G} (hx : x ∈ H ⊓ L) (hxd : ∃ k : ℕ, orderOf x = d ^ k) :
    barM M (zpowers x) ≤
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨k, hk⟩ := hxd
  have hxM : x ∈ M := hL.le hx.2
  have hxhull : x ∈ oPPrimeHull d (H ⊓ M) :=
    Subgroup.subset_closure ⟨⟨hx.1, hxM⟩, k, hk⟩
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hw
  have hyG : (y : G) ∈ zpowers x := Subgroup.mem_subgroupOf.mp hy
  have hyHull : (y : G) ∈ oPPrimeHull d (H ⊓ M) :=
    Subgroup.zpowers_le.mpr hxhull hyG
  have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hc : (y : G) * (l : G) * (y : G)⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 M :=
    hYL (y : G) hyHull (l : G) hlL
  have hmem : (y : G) * (l : G) * (y : G)⁻¹ * (l : G)⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem y.2 l.2) (M.inv_mem y.2)) (M.inv_mem l.2)
  let dM : ↥M := ⟨(y : G) * (l : G) * (y : G)⁻¹ * (l : G)⁻¹, hmem⟩
  have hdM : dM ∈ CFSG.pCore 2 ↥M := by
    have hc' := hc
    rw [show CFSG.Open.pCoreOf 2 M = (CFSG.pCore 2 ↥M).map M.subtype from rfl] at hc'
    obtain ⟨z, hz, hzv⟩ := Subgroup.mem_map.mp hc'
    have hzd : z = dM := Subtype.ext hzv
    simpa [hzd] using hz
  have hquot : (y * l) / (l * y) = dM := by
    apply Subtype.ext
    simp only [Subgroup.coe_div, Subgroup.coe_mul, dM]
    rw [div_eq_mul_inv, mul_inv_rev]
    group
  rw [← map_mul, ← map_mul, eq_comm]
  exact QuotientGroup.eq_iff_div_mem.mpr (hquot ▸ hdM)

omit [Finite G] in
private lemma exists_hom_range_map_center_ker {M H L : Subgroup G} {d : ℕ} (hd : d.Prime)
    (hL : IsTwoPrimeComponent M L)
    (hYL : ∀ y ∈ oPPrimeHull d (H ⊓ M), ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 M) :
    ∃ Φ : ↥(H ⊓ L) →* (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)),
      Φ.range = ((barM M (H ⊓ L)).subgroupOf (barM M L)).map
        (QuotientGroup.mk' (Subgroup.center ↥(barM M L))) ∧
      ∀ x : ↥(H ⊓ L), IsPGroup d (Subgroup.zpowers x) → x ∈ Φ.ker := by
  classical
  let Z : Subgroup ↥(barM M L) := Subgroup.center ↥(barM M L)
  let S : Subgroup (↥(barM M L) ⧸ Z) :=
    ((barM M (H ⊓ L)).subgroupOf (barM M L)).map (QuotientGroup.mk' Z)
  have hKM : H ⊓ L ≤ M := inf_le_right.trans hL.le
  let φ : ↥(H ⊓ L) →* ↥(barM M L) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hKM)).codRestrict
      (barM M L) (fun x => by
        rw [barM]
        exact Subgroup.mem_map.mpr
          ⟨Subgroup.inclusion hKM x, Subgroup.mem_subgroupOf.mpr x.2.2, rfl⟩)
  let Φ : ↥(H ⊓ L) →* (↥(barM M L) ⧸ Z) := (QuotientGroup.mk' Z).comp φ
  have hφrange : φ.range = (barM M (H ⊓ L)).subgroupOf (barM M L) := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr
        ⟨Subgroup.inclusion hKM x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
    · intro hp
      rcases Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hp) with ⟨w, hw, hwp⟩
      refine ⟨⟨(w : G), Subgroup.mem_subgroupOf.mp hw⟩, ?_⟩
      apply Subtype.ext
      exact hwp
  have hΦrange : Φ.range = S := by
    rw [MonoidHom.range_comp, hφrange]
  refine ⟨Φ, hΦrange, ?_⟩
  intro x hx
  rw [MonoidHom.mem_ker]
  obtain ⟨k, hk⟩ := hx.exists_orderOf_dvd_pow ⟨x, Subgroup.mem_zpowers x⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hd).mp hk
  have hkx : orderOf x = d ^ j := by
    rw [← Subgroup.orderOf_mk (H := Subgroup.zpowers x) x (Subgroup.mem_zpowers x)]
    exact hj
  have hxd : ∃ n : ℕ, orderOf (x : G) = d ^ n :=
    ⟨j, by rw [Subgroup.orderOf_coe, hkx]⟩
  have hcent := barM_zpowers_le_centralizer_of_mem_inf hL hYL x.2 hxd
  have hxbar : (φ x : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M (Subgroup.zpowers (x : G)) := by
    rw [barM]
    exact Subgroup.mem_map.mpr
      ⟨⟨(x : G), hKM x.2⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers (x : G)), rfl⟩
  have hcentx : (φ x : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := hcent hxbar
  have hcenter : φ x ∈ Z := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hcentx (g : ↥M ⧸ CFSG.pCore 2 ↥M) g.2
  exact (QuotientGroup.eq_one_iff (φ x)).mpr hcenter

theorem not_dvd_card_map_center_barM_inf {M H L : Subgroup G} {d : ℕ} (hd : d.Prime)
    (hL : IsTwoPrimeComponent M L)
    (hYL : ∀ y ∈ oPPrimeHull d (H ⊓ M), ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 M) :
    ¬ d ∣ Nat.card (((barM M (H ⊓ L)).subgroupOf (barM M L)).map
      (QuotientGroup.mk' (Subgroup.center ↥(barM M L)))) := by
  classical
  let S : Subgroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    ((barM M (H ⊓ L)).subgroupOf (barM M L)).map
      (QuotientGroup.mk' (Subgroup.center ↥(barM M L)))
  change ¬ d ∣ Nat.card S
  obtain ⟨Φ, hΦrange, hker⟩ := exists_hom_range_map_center_ker hd hL hYL
  have hΦrange' : Φ.range = S := hΦrange
  have hfac : (Nat.card ↥(H ⊓ L)).factorization d = (Nat.card Φ.ker).factorization d := by
    simpa using CFSG.GroupTheory.factorization_eq_of_forall_isPGroup_zpowers_mem hd
      (H := Φ.ker) (K := ⊤) le_top (fun x _ hx => hker x hx)
  have hcard : Nat.card Φ.ker * Nat.card S = Nat.card ↥(H ⊓ L) := by
    rw [← hΦrange']
    exact Subgroup.card_ker_mul_card_range Φ
  have hfacS : (Nat.card S).factorization d = 0 := by
    have h1 : (Nat.card ↥(H ⊓ L)).factorization d =
        (Nat.card Φ.ker).factorization d + (Nat.card S).factorization d := by
      rw [← hcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
        Finsupp.add_apply]
    omega
  rw [Nat.Prime.dvd_iff_one_le_factorization hd (Nat.card_pos.ne')]
  omega

theorem pRank_barM_le_one_of_nineThreeTwo {M S L : Subgroup G} (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hS : ¬ CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ L) L)
    (h2 : NineThreeTwo M S L) (hN1 : CFSG.LocalAnalysis.AGL81I.Section4.AGL81FourNineteen)
    (hm3L : CFSG.Open.pRank 3 (barM M L) ≤ 2) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hJ : ¬ d ∣ Nat.card (((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf
      (barM M L)).map (QuotientGroup.mk' (Subgroup.center ↥(barM M L))))) :
    CFSG.Open.pRank d (barM M L) ≤ 1 := by
  obtain ⟨hcl, T, J, hT, hle, hne, htop, hJdef⟩ :=
    CFSG.AGLEmbedding.BlockCyc.nineThreeTwo_parabolic hA hL hS h2
  have h3top : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) ≤ 2 := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barM M L)]
  have hmain :=
    hN1 ↥(barM M L) hL.component.2.2 hcl T J hT hle hne htop d hd hd5
      (by rw [hJdef]; exact hJ) (h3top.trans (by norm_num))
  have hle1 : CFSG.Open.pRank d (⊤ : Subgroup ↥(barM M L)) + 1 ≤ 2 := by
    calc CFSG.Open.pRank d (⊤ : Subgroup ↥(barM M L)) + 1
        ≤ max 2 (CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barM M L))) := hmain
      _ ≤ 2 := max_le (by norm_num) h3top
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := d) (barM M L)]
  omega

theorem pRank_barM_le_one_of_quot_center_alternating {M L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) {n : ℕ}
    (hA : Nonempty ((↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ≃* alternatingGroup (Fin n)))
    (hm3L : CFSG.Open.pRank 3 (barM M L) ≤ 2) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) :
    CFSG.Open.pRank d (barM M L) ≤ 1 := by
  obtain ⟨e⟩ := hA
  have : Group.IsPerfect ↥(barM M L) := ⟨hL.component.2.2.1⟩
  have : Group.IsPerfect (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center ↥(barM M L)))
      (QuotientGroup.mk'_surjective _)
  have : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    hL.component.2.2.2.toNontrivial
  have hn : 5 ≤ n :=
    CFSG.AGLEmbedding.BlockCyc.five_le_of_perfect_mulEquiv_alternatingGroup e
  have h := pRank_add_one_le_of_quot_center_alternating hL.component.2.2 hn ⟨e⟩ hd hd5
  have h3top : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) ≤ 2 := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barM M L)]
  have hdle : CFSG.Open.pRank d (⊤ : Subgroup ↥(barM M L)) ≤ 1 := by
    have hle1 : CFSG.Open.pRank d (⊤ : Subgroup ↥(barM M L)) + 1 ≤
        max 2 (CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barM M L))) := h.1
    have hmax : max 2 (CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barM M L))) ≤ 2 :=
      max_le (by norm_num) h3top
    omega
  rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := d) (barM M L)]

theorem pRank_barM_le_one_of_nineThreeConclusion
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev) {M S L : Subgroup G}
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hS : ¬ CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ L) L)
    (h93 : NineThreeConclusion M S L) (hn1 : ¬ NineThreeOne L)
    (hN1 : CFSG.LocalAnalysis.AGL81I.Section4.AGL81FourNineteen)
    (hm3L : CFSG.Open.pRank 3 (barM M L) ≤ 2) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (hJ : ¬ d ∣ Nat.card (((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf
      (barM M L)).map (QuotientGroup.mk' (Subgroup.center ↥(barM M L))))) :
    CFSG.Open.pRank d (barM M L) ≤ 1 := by
  have hq := hL.component.2.2
  have h3top : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) ≤ 2 := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barM M L)]
  have halt {n : ℕ} (hA : Nonempty ((↥(barM M L) ⧸ Subgroup.center ↥(barM M L))
      ≃* alternatingGroup (Fin n))) :
      CFSG.Open.pRank d (barM M L) ≤ 1 :=
    pRank_barM_le_one_of_quot_center_alternating hL.toIsTwoPrimeComponent hA hm3L hd hd5
  have hquot {n : ℕ} (e : ↥(barM M L) ≃* alternatingGroup (Fin n)) :
      CFSG.Open.pRank d (barM M L) ≤ 1 :=
    halt (quot_center_alternating_of_mulEquiv hq e).2.2
  rcases h93 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hn1
  · exact pRank_barM_le_one_of_nineThreeTwo hA hL hS h2 hN1 hm3L hd hd5 hJ
  · obtain ⟨n, -, ⟨e⟩⟩ :=
      exists_mulEquiv_alternating_of_isOrthogonalTwo hT h3.2.1 h3top
    exact hquot e
  · exact halt h4.2.2.1
  · obtain ⟨e⟩ := h5.2.1
    exact hquot e
  · obtain ⟨-, n, ⟨e⟩, -⟩ := h6
    exact halt ⟨e⟩
  · obtain ⟨-, n, ⟨e⟩, -⟩ := h7
    exact hquot e
  · obtain ⟨-, N, r, -, -, -, -, -, ⟨e⟩, -⟩ := h8
    exact hquot e

theorem not_dvd_card_center_barM_of_pRank_le_one {M L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (h : CFSG.Open.pRank d (barM M L) ≤ 1) :
    ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L)) :=
  letI : Fact d.Prime := ⟨hd⟩
  letI : Group.IsPerfect ↥(barM M L) := ⟨hL.component.2.2.1⟩
  by
    by_cases h1 : CFSG.Open.pRank d (barM M L) = 1
    · have hrank : CFSG.Open.pRank d (⊤ : Subgroup ↥(barM M L)) = 1 := by
        rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barM M L)]
        exact h1
      exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.not_dvd_card_center_of_pRank_eq_one
        hd2 hrank
    · have h0 : CFSG.Open.pRank d (barM M L) = 0 := by omega
      have hnot : ¬ d ∣ Nat.card (barM M L) :=
        CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero hd h0
      exact fun hdvd => hnot (hdvd.trans (Subgroup.card_subgroup_dvd_card _))

omit [Finite G] in
private lemma exists_mem_subgroupOf_orderOf_eq_prime {M H L : Subgroup G} (hLM : L ≤ M) {d : ℕ}
    (hd : d.Prime) (hd2 : d ≠ 2) {x : G} (hx : x ∈ H ⊓ L) (hxord : orderOf x = d) :
    ∃ pL : ↥(barM M L), pL ∈ (barM M (H ⊓ L)).subgroupOf (barM M L) ∧ orderOf pL = d := by
  classical
  let xM : ↥M := ⟨x, hLM hx.2⟩
  have hxMord : orderOf xM = d := by
    rw [← Subgroup.orderOf_coe (H := M) xM]
    exact hxord
  let p : ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) xM
  have hpK : p ∈ barM M (H ⊓ L) := by
    rw [barM]
    exact Subgroup.mem_map.mpr ⟨xM, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hpL : p ∈ barM M L := by
    rw [barM]
    exact Subgroup.mem_map.mpr ⟨xM, Subgroup.mem_subgroupOf.mpr hx.2, rfl⟩
  let pL : ↥(barM M L) := ⟨p, hpL⟩
  have hp_ne : p ≠ 1 := by
    intro hp1
    have hxM2 : xM ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff xM).mp hp1
    let xC : ↥(CFSG.pCore 2 ↥M) := ⟨xM, hxM2⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_orderOf_dvd_pow xC
    rw [Subgroup.orderOf_mk, hxMord] at hk
    have hdvd2 : d ∣ 2 := hd.dvd_of_dvd_pow hk
    exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp hdvd2)
  have hp_pow : p ^ d = 1 := by
    change ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)) xM) ^ d = 1
    rw [← map_pow, show xM ^ d = 1 by rw [← hxMord]; exact pow_orderOf_eq_one xM, map_one]
  have hpord : orderOf p = d := by
    have hpdvd : orderOf p ∣ d := orderOf_dvd_iff_pow_eq_one.mpr hp_pow
    rcases (Nat.dvd_prime hd).mp hpdvd with h1 | h
    · exact absurd (orderOf_eq_one_iff.mp h1) hp_ne
    · exact h
  have hpLord : orderOf pL = d := by
    change orderOf (⟨p, hpL⟩ : ↥(barM M L)) = d
    rw [Subgroup.orderOf_mk, hpord]
  exact ⟨pL, Subgroup.mem_subgroupOf.mpr hpK, hpLord⟩

omit [Finite G] in
private lemma dvd_card_center_or_map_center_of_orderOf {M H L : Subgroup G} {d : ℕ} (hd : d.Prime)
    {pL : ↥(barM M L)} (hpL : pL ∈ (barM M (H ⊓ L)).subgroupOf (barM M L))
    (hpLord : orderOf pL = d) :
    d ∣ Nat.card (Subgroup.center ↥(barM M L)) ∨
      d ∣ Nat.card (((barM M (H ⊓ L)).subgroupOf (barM M L)).map
        (QuotientGroup.mk' (Subgroup.center ↥(barM M L)))) := by
  classical
  let Z : Subgroup ↥(barM M L) := Subgroup.center ↥(barM M L)
  let S : Subgroup (↥(barM M L) ⧸ Z) :=
    ((barM M (H ⊓ L)).subgroupOf (barM M L)).map (QuotientGroup.mk' Z)
  change d ∣ Nat.card Z ∨ d ∣ Nat.card S
  let q : ↥(barM M L) ⧸ Z := QuotientGroup.mk' Z pL
  have hqS : q ∈ S := by
    change QuotientGroup.mk' Z pL ∈
      ((barM M (H ⊓ L)).subgroupOf (barM M L)).map (QuotientGroup.mk' Z)
    exact Subgroup.mem_map.mpr ⟨pL, hpL, rfl⟩
  have hq_dvd : orderOf q ∣ d := by
    rw [orderOf_dvd_iff_pow_eq_one]
    change ((QuotientGroup.mk' Z) pL) ^ d = 1
    rw [← map_pow, show pL ^ d = 1 by rw [← hpLord]; exact pow_orderOf_eq_one pL, map_one]
  by_cases hq1 : q = 1
  · left
    have hcenter : pL ∈ Z := (QuotientGroup.eq_one_iff pL).mp hq1
    have hzp : Subgroup.zpowers pL ≤ Z := Subgroup.zpowers_le.mpr hcenter
    have hcard : Nat.card (Subgroup.zpowers pL) = d := by rw [Nat.card_zpowers, hpLord]
    exact hcard ▸ Subgroup.card_dvd_of_le hzp
  · right
    have hqord : orderOf q = d := by
      rcases (Nat.dvd_prime hd).mp hq_dvd with h1 | h
      · exact absurd (orderOf_eq_one_iff.mp h1) hq1
      · exact h
    have hzp : Subgroup.zpowers q ≤ S := Subgroup.zpowers_le.mpr hqS
    have hcard : Nat.card (Subgroup.zpowers q) = d := by rw [Nat.card_zpowers, hqord]
    exact hcard ▸ Subgroup.card_dvd_of_le hzp

theorem not_dvd_card_inf_of_barM {M H L : Subgroup G} (hLM : L ≤ M) {d : ℕ} (hd : d.Prime)
    (hd2 : d ≠ 2)
    (hJ : ¬ d ∣ Nat.card (((barM M (H ⊓ L)).subgroupOf (barM M L)).map
      (QuotientGroup.mk' (Subgroup.center ↥(barM M L)))))
    (hZ : ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L))) :
    ¬ d ∣ Nat.card (H ⊓ L : Subgroup G) :=
  letI : Fact d.Prime := ⟨hd⟩
  by
  classical
  let Z : Subgroup ↥(barM M L) := Subgroup.center ↥(barM M L)
  let S : Subgroup (↥(barM M L) ⧸ Z) :=
    ((barM M (H ⊓ L)).subgroupOf (barM M L)).map (QuotientGroup.mk' Z)
  change ¬ d ∣ Nat.card S at hJ
  change ¬ d ∣ Nat.card Z at hZ
  intro hdvd
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ L)) d hdvd
  obtain ⟨pL, hpL, hpLord⟩ :=
    exists_mem_subgroupOf_orderOf_eq_prime hLM hd hd2 x.2
      (by rw [Subgroup.orderOf_coe]; exact hxord)
  rcases dvd_card_center_or_map_center_of_orderOf hd hpL hpLord with h | h
  · exact hZ h
  · exact hJ h

theorem not_dvd_card_inf_of_isWeakSBlock
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev) {M H L : Subgroup G} {d : ℕ}
    (hd : d.Prime) (hd5 : 5 ≤ d) (hphase : TwoLocalPhaseThree M H)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hS : ¬ CFSG.QuasithinUnique.IsSylowTwoOf (pCoreOf 2 H ⊓ L) L)
    (h93 : NineThreeConclusion M (pCoreOf 2 H) L) (hn1 : ¬ NineThreeOne L)
    (hN1 : CFSG.LocalAnalysis.AGL81I.Section4.AGL81FourNineteen)
    (hm3L : CFSG.Open.pRank 3 (barM M L) ≤ 2)
    (hYL : ∀ y ∈ oPPrimeHull d (H ⊓ M), ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 M) :
    ¬ d ∣ Nat.card (H ⊓ L : Subgroup G) ∧ CFSG.Open.pRank d (barM M L) ≤ 1 ∧
      ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
  have hA : Asc81bHyp M (pCoreOf 2 H) := hphase.asc81bHyp
  have hIH : ¬ d ∣ Nat.card (((barM M (H ⊓ L)).subgroupOf (barM M L)).map
      (QuotientGroup.mk' (Subgroup.center ↥(barM M L)))) :=
    not_dvd_card_map_center_barM_inf hd hL.toIsTwoPrimeComponent hYL
  have hJH : ¬ d ∣ Nat.card
      (((barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)).subgroupOf
        (barM M L)).map (QuotientGroup.mk' (Subgroup.center ↥(barM M L)))) := by
    rwa [hphase.normalizer_twoCore_H]
  have hLd : CFSG.Open.pRank d (barM M L) ≤ 1 :=
    pRank_barM_le_one_of_nineThreeConclusion hT hA hL hS h93 hn1 hN1 hm3L hd hd5 hJH
  have hZ : ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L)) :=
    not_dvd_card_center_barM_of_pRank_le_one hL.toIsTwoPrimeComponent hd (by omega) hLd
  exact ⟨not_dvd_card_inf_of_barM hL.le hd (by omega) hIH hZ, hLd, hZ⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
