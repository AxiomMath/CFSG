module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.Quasithin.SteinbergCGPlanePairTransport
import CFSG.Quasithin.Vol2.Ch3Sec1Aux
import CFSG.Quasithin.Vol2.Ch4Sec2T425C27A
import CFSG.RankThree.PartOne.S9.Sylow.GlobalLemmas

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (gnV gnC gnImg)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {M H E Q J R T L : Subgroup G}

private theorem fourteenNine_X_le_M {M H E Q J R T L : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h8 : FourteenEightData M L) : L ⊔ T ≤ M :=
  sup_le h8.L_le (c.T_sylow.le.trans inf_le_right)

private theorem fourteenNine_M_le_normalizer_L {M L : Subgroup G} (h8 : FourteenEightData M L) :
    M ≤ Subgroup.normalizer (L : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h8.L_le).mp h8.L_normal

private theorem fourteenNine_M_le_normalizer_D (M : Subgroup G) :
    M ≤ Subgroup.normalizer (CFSG.inSubgroup (CFSG.pPrimeCore 3) M : Set G) :=
  Subgroup.le_normalizer.trans
    (CFSG.RankThree.PartOne.Sec9B.normalizer_le_normalizer_inSubgroup_pPrimeCore 3 M)

private theorem fourteenNine_T_ne_bot {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) : T ≠ ⊥ := by
  intro hT
  have hO : CFSG.Open.pCoreOf 2 H = ⊥ :=
    le_bot_iff.mp (hT ▸ (c.core_le_R.trans c.R_le_T))
  exact CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal c.choice.hypCGen.isTwoLocal hO

private theorem fourteenNine_sylow_D1 {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h7 : FourteenSevenData M H Q R T)
    {L : Subgroup G} (h8 : FourteenEightData M L) :
    CFSG.ABGLocalTools.IsSylowOf 2
      (T ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M)
      (CFSG.inSubgroup (CFSG.pPrimeCore 3) M ⊓ (L ⊔ T)) :=
  h7.sylow_D.of_le
    (le_inf inf_le_right (inf_le_left.trans le_sup_right)) inf_le_left

private theorem subgroupOf_normal_of_le_normalizer {L M X : Subgroup G}
    (hLX : L ≤ X) (hXM : X ≤ M) (hML : M ≤ Subgroup.normalizer (L : Set G)) :
    (L.subgroupOf X).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr (hXM.trans hML)

private theorem subgroupOf_map_subtype_eq {X : Subgroup G} (U : Subgroup ↥X) :
    (U.map X.subtype).subgroupOf X = U :=
  Subgroup.comap_map_eq_self_of_injective X.subtype_injective U

private theorem le_core_or_le_of_normal {M L X U : Subgroup G}
    (h8 : FourteenEightData M L) (hLX : L ≤ X) (hXM : X ≤ M)
    (hUX : U ≤ X) (hUnorm : (U.subgroupOf X).Normal) (hUM : U ≤ M)
    (hUNL : U ≤ Subgroup.normalizer (L : Set G)) :
    U ≤ CFSG.inSubgroup (CFSG.pPrimeCore 3) M ∨ L ≤ U := by
  have hLnormX : (L.subgroupOf X).Normal :=
    subgroupOf_normal_of_le_normalizer hLX hXM (fourteenNine_M_le_normalizer_L h8)
  have hNnorm : ((U ⊓ L).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnU : (⟨n, hLX n.2⟩ : X) ∈ U.subgroupOf X := hn.1
    have hconj := hUnorm.conj_mem (⟨n, hLX n.2⟩ : X) hnU (⟨g, hLX g.2⟩ : X)
    exact ⟨Subgroup.mem_subgroupOf.mp hconj,
      L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)⟩
  rcases h8.dichotomy (U ⊓ L) inf_le_right hNnorm with hNleD | hNeqL
  · left
    haveI : (U.subgroupOf X).Normal := hUnorm
    haveI : (L.subgroupOf X).Normal := hLnormX
    have hcommX : ⁅U.subgroupOf X, L.subgroupOf X⁆ ≤
        U.subgroupOf X ⊓ L.subgroupOf X :=
      le_inf (Subgroup.commutator_le_left _ _) (Subgroup.commutator_le_right _ _)
    have hcomm : ⁅U, L⁆ ≤ U ⊓ L := by
      have h := Subgroup.map_mono (f := X.subtype) hcommX
      rw [Subgroup.map_commutator, Subgroup.map_inf _ _ _ X.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hUX,
        Subgroup.map_subgroupOf_eq_of_le hLX] at h
      exact h
    exact h8.centralizing U hUM hUNL (hcomm.trans hNleD)
  · right
    exact hNeqL ▸ inf_le_left

private theorem le_sup_of_sylow_of_surjective_isPGroup {X : Type*} [Group X] [Finite X]
    {S U Y : Subgroup X} {Q : Type} [Group Q] (f : U →* Q)
    (hf : Function.Surjective f) (hker : f.ker = Y.subgroupOf U)
    (hQ : IsPGroup 2 Q) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S U) :
    U ≤ S ⊔ Y := by
  obtain ⟨SU, hSU⟩ := hS.exists_sylow_eq_subgroupOf
  let R : Sylow 2 Q := SU.mapSurjective (f := f) hf
  have hRtop : (R : Subgroup Q) = ⊤ := by
    have htop2 : IsPGroup 2 (⊤ : Subgroup Q) := hQ.to_subgroup ⊤
    exact (R.is_maximal' htop2 le_top).symm
  intro u hu
  have hfu : f ⟨u, hu⟩ ∈ (R : Subgroup Q) := by
    rw [hRtop]
    exact Subgroup.mem_top _
  rw [Sylow.coe_mapSurjective] at hfu
  obtain ⟨s, hs, hfs⟩ := Subgroup.mem_map.mp hfu
  have hsS : (s : X) ∈ S := by
    have hs' : s ∈ S.subgroupOf U := hSU ▸ hs
    exact Subgroup.mem_subgroupOf.mp hs'
  have hkeru : (s : X)⁻¹ * u ∈ Y := by
    have h1 : s⁻¹ * ⟨u, hu⟩ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfs, inv_mul_cancel]
    rw [hker] at h1
    simpa using Subgroup.mem_subgroupOf.mp h1
  have hueq : u = (s : X) * ((s : X)⁻¹ * u) := by group
  rw [hueq]
  exact Subgroup.mul_mem_sup hsS hkeru

private theorem le_centralizer_normalClosure {X : Type*} [Group X] [Finite X]
    {U Z : Subgroup X} (hU : U.Normal) (hZ : Z ≤ Subgroup.centralizer (U : Set X)) :
    U ≤ Subgroup.centralizer (Subgroup.normalClosure (Z : Set X)) := by
  haveI : (Subgroup.centralizer (U : Set X)).Normal := Subgroup.normal_centralizer
  exact (Subgroup.le_centralizer_iff).mpr (Subgroup.normalClosure_le_normal hZ)

private theorem pCoreOf_top_map_facts {X : Subgroup G} :
    (((CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X)).map X.subtype).subgroupOf X).Normal ∧
      IsPGroup 2 ((CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X)).map X.subtype) ∧
      ((CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X)).map X.subtype) ≤ X := by
  let P : Subgroup ↥X := CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X)
  let O : Subgroup G := P.map X.subtype
  have hP2 : IsPGroup 2 P := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 ⊤
  have hPnorm : P.Normal := by
    rw [show P = (CFSG.pCore 2 (⊤ : Subgroup ↥X)).map (⊤ : Subgroup ↥X).subtype from
      CFSG.openPCoreOf_eq_map_pCore 2 (⊤ : Subgroup ↥X)]
    exact (CFSG.pCore_normal (p := 2) (G := ↥(⊤ : Subgroup ↥X))).map _
      (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have hOnormX : (O.subgroupOf X).Normal := by
    rw [subgroupOf_map_subtype_eq P]
    exact hPnorm
  have hO2 : IsPGroup 2 O := hP2.map X.subtype
  have hOX : O ≤ X := Subgroup.map_subtype_le P
  change (O.subgroupOf X).Normal ∧ IsPGroup 2 O ∧ O ≤ X
  exact ⟨hOnormX, hO2, hOX⟩

private theorem fourteenNine_quotient_isPGroup_two {X L T : Subgroup G}
    (hXL : X = L ⊔ T) (hLN : (L.subgroupOf X).Normal) (hT2 : IsPGroup 2 T) :
    IsPGroup 2 (↥X ⧸ L.subgroupOf X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥X →* (↥X ⧸ L.subgroupOf X) := QuotientGroup.mk' (L.subgroupOf X)
  have hT2' : IsPGroup 2 (T.subgroupOf X) := hT2.comap_subtype
  have hsurj : Function.Surjective (π.comp (T.subgroupOf X).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf X) q
    have htop : L.subgroupOf X ⊔ T.subgroupOf X = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (A := L) (A' := T) (B := X)
        (hXL ▸ le_sup_left) (hXL ▸ le_sup_right), hXL, Subgroup.subgroupOf_self]
    have hx : x ∈ L.subgroupOf X ⊔ T.subgroupOf X := by
      rw [htop]
      exact Subgroup.mem_top x
    obtain ⟨l, hl, t, ht, hlt⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    refine ⟨⟨t, ht⟩, ?_⟩
    change (π.comp (T.subgroupOf X).subtype) ⟨t, ht⟩ = π x
    have hl1 : π l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [← hlt, map_mul, hl1, one_mul]
    rfl
  exact hT2'.of_surjective _ hsurj

private theorem fourteenNine_primeResidual_subgroupOf {X L : Subgroup G} (hLX : L ≤ X)
    (hres : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3 ↥L = ⊤) :
    CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3 ↥(L.subgroupOf X) = ⊤ := by
  let e := Subgroup.subgroupOfEquivOfLe hLX
  have h2 : (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
      ↥(L.subgroupOf X)).map e.toMonoidHom = ⊤ := by
    rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_map_equiv 3 e, hres]
  have h3 : (⊤ : Subgroup ↥(L.subgroupOf X)).map e.toMonoidHom = ⊤ := by
    simpa using Subgroup.map_top_of_surjective e.toMonoidHom e.surjective
  exact Subgroup.map_injective e.injective (h2.trans h3.symm)

private theorem fourteenNine_primeResidual_le_of_quotient_two {X L : Subgroup G}
    (N0 : Subgroup ↥X) (hLN : (L.subgroupOf X).Normal)
    (hQ2 : IsPGroup 2 (↥X ⧸ L.subgroupOf X)) :
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3 ↥N0).map
        N0.subtype ≤ L.subgroupOf X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (L.subgroupOf X).Normal := hLN
  let π : ↥X →* (↥X ⧸ L.subgroupOf X) := QuotientGroup.mk' (L.subgroupOf X)
  rw [Subgroup.map_le_iff_le_comap,
    CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_closure]
  refine (Subgroup.closure_le (Subgroup.comap N0.subtype (L.subgroupOf X))).2 ?_
  rintro p ⟨k, hk⟩
  have hpX : (p : X) ∈ L.subgroupOf X := by
    have horder : orderOf ((π.comp N0.subtype) p) = 1 := by
      obtain ⟨j, hj⟩ := hQ2.exists_orderOf_eq_pow ((π.comp N0.subtype) p)
      have hdvd1 : orderOf ((π.comp N0.subtype) p) ∣ 3 ^ k := by
        rw [← hk]
        exact orderOf_map_dvd _ p
      have hdvd2 : orderOf ((π.comp N0.subtype) p) ∣ 2 ^ j := by
        rw [hj]
      have hcop : Nat.Coprime (3 ^ k) (2 ^ j) :=
        Nat.Coprime.pow k j (by norm_num : Nat.Coprime 3 2)
      exact Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
    have hone : (π.comp N0.subtype) p = 1 := orderOf_eq_one_iff.mp horder
    exact (QuotientGroup.eq_one_iff (p : X)).mp hone
  exact hpX

private theorem fourteenNine_coset_mem_sup {X : Type*} [Group X] [Finite X]
    {D N0 : Subgroup X} (hD : D.Normal) {x : X} (hx : x ∈ D ⊔ N0)
    (hx3 : ∃ k, orderOf x = 3 ^ k) :
    x ∈ (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3 ↥N0).map
        N0.subtype ⊔ D := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : D.Normal := hD
  let π : X →* (X ⧸ D) := QuotientGroup.mk' D
  obtain ⟨k, hk⟩ := hx3
  obtain ⟨d, hd, n, hn, hdn⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  have hπx : π n = π x := by
    rw [← hdn, map_mul]
    have hd1 : π d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
    rw [hd1, one_mul]
  have horder_dvd : orderOf (π n) ∣ 3 ^ k := by
    rw [hπx, ← hk]
    exact orderOf_map_dvd π x
  let y : ↥(N0.map π) := ⟨π n, Subgroup.mem_map_of_mem π hn⟩
  have hy_mem : y ∈ CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
      ↥(N0.map π) := by
    rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_closure]
    refine Subgroup.subset_closure ?_
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp horder_dvd
    exact ⟨j, (Subgroup.orderOf_coe y).symm.trans hj⟩
  have hy_image : y ∈ (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
      ↥N0).map (π.subgroupMap N0) := by
    rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_map_surjective 3
      (π.subgroupMap N0) (MonoidHom.subgroupMap_surjective π N0)]
    exact hy_mem
  obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hy_image
  have hπm : π (m : X) = π n := congrArg Subtype.val hmy
  have hker : (m : X)⁻¹ * n ∈ D := by
    exact (QuotientGroup.eq).mp (show ((m : X) : X ⧸ D) = (n : X ⧸ D) from hπm)
  have hn_mem : n ∈ (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
      ↥N0).map N0.subtype ⊔ D := by
    have hmO : (m : X) ∈ (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
        ↥N0).map N0.subtype := Subgroup.mem_map_of_mem N0.subtype hm
    have hmem : (m : X) * ((m : X)⁻¹ * n) ∈
        (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3 ↥N0).map
          N0.subtype ⊔ D :=
      Subgroup.mul_mem_sup hmO hker
    simpa [mul_assoc] using hmem
  have hxmem : d * n ∈ (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
      ↥N0).map N0.subtype ⊔ D :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right hd) hn_mem
  rwa [← hdn]

private theorem fourteenNine_le_sup_inf {X : Type*} [Group X] [Finite X]
    {L D N0 : Subgroup X} (hD : D.Normal) (hDN : D ⊔ N0 = ⊤)
    (hLres : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3 ↥L = ⊤)
    (hNres : (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3 ↥N0).map
      N0.subtype ≤ L) :
    L ≤ (L ⊓ N0) ⊔ D := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup X :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3 ↥N0).map N0.subtype
  have hO_le_L : O ≤ L := hNres
  have hO_le_N0 : O ≤ N0 := Subgroup.map_subtype_le _
  have hO_le_inf : O ≤ L ⊓ N0 := le_inf hO_le_L hO_le_N0
  have hgen : L = Subgroup.closure (L.subtype ''
      {x : ↥L | ∃ k, orderOf x = 3 ^ k}) := by
    have hmap : (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
        ↥L).map L.subtype = L := by
      rw [hLres, Subgroup.map_top, Subgroup.range_subtype]
    conv_lhs => rw [← hmap]
    rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_closure,
      MonoidHom.map_closure]
  conv_lhs => rw [hgen]
  refine (Subgroup.closure_le ((L ⊓ N0) ⊔ D)).2 ?_
  rintro x ⟨l, hl, rfl⟩
  obtain ⟨k, hk⟩ := hl
  have hx : (l : X) ∈ D ⊔ N0 := by
    rw [hDN]
    exact Subgroup.mem_top _
  have hx3 : ∃ j, orderOf (l : X) = 3 ^ j :=
    ⟨k, (Subgroup.orderOf_coe l).trans hk⟩
  have hcoset := fourteenNine_coset_mem_sup hD hx hx3
  exact (sup_le (show O ≤ (L ⊓ N0) ⊔ D from hO_le_inf.trans le_sup_left)
    (le_sup_right : D ≤ (L ⊓ N0) ⊔ D)) hcoset

private theorem fourteenNine_pCoreOf_two_M_le_TD {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h7 : FourteenSevenData M H Q R T) :
    CFSG.Open.pCoreOf 2 M ≤ T ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 M
  have hQ2 : IsPGroup 2 Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
  have hQM : Q ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hQnorm : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hQcop : Nat.Coprime 3 (Nat.card Q) := by
    obtain ⟨n, hn⟩ := hQ2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hQD : Q ≤ D :=
    CFSG.RankThree.PartOne.Sec9B.le_inSubgroup_pPrimeCore hQcop hQM hQnorm
  have hDleM : D ≤ M := CFSG.RankThree.PartOne.Sec9B.inSubgroup_pPrimeCore_le 3 M
  have hQDnorm : (Q.subgroupOf D).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQD]
    exact hDleM.trans hQnorm
  obtain ⟨S, hS⟩ := h7.sylow_D.exists_sylow_eq_subgroupOf
  haveI : (Q.subgroupOf D).Normal := hQDnorm
  have hQleS : Q.subgroupOf D ≤ (S : Subgroup D) :=
    @IsPGroup.le_sylow_of_normal 2 ↥D _ (Q.subgroupOf D) hQDnorm
      (hQ2.comap_subtype) S
  have hQleTD : Q ≤ T ⊓ D := by
    have hmap := Subgroup.map_mono (f := D.subtype) hQleS
    rw [Subgroup.map_subgroupOf_eq_of_le hQD] at hmap
    have hSD : (S : Subgroup D).map D.subtype = T ⊓ D := by
      rw [hS, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
    rwa [hSD] at hmap
  exact hQleTD

private theorem fourteenNine_charTwo_top {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h7 : FourteenSevenData M H Q R T)
    {L : Subgroup G} (h8 : FourteenEightData M L) :
    CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup ↥(L ⊔ T)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G := L ⊔ T
  have hXM : X ≤ M := fourteenNine_X_le_M c h8
  have hQTD := fourteenNine_pCoreOf_two_M_le_TD c h7
  have hQT : CFSG.Open.pCoreOf 2 M ≤ T := fun x hx => (hQTD hx).1
  have hQX : CFSG.Open.pCoreOf 2 M ≤ X := hQT.trans le_sup_right
  have hcharM : CFSG.QuasithinUnique.CharTwo M :=
    c.choice.cstar.charTwo M c.choice.maxLocal.1
  have hcharX : CFSG.QuasithinUnique.CharTwo X :=
    CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hcharM hXM hQX
  have hcharTop : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup ↥X) := by
    have h := CFSG.Quasithin.EmptyFaithfulMultiple.L15422.charTwo_subgroupOf
      (X := X) (L := X) le_rfl hcharX
    simpa [Subgroup.subgroupOf_self] using h
  exact hcharTop

private theorem fourteenNine_pCoreOf_top_le_D {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h7 : FourteenSevenData M H Q R T)
    {L : Subgroup G} (h8 : FourteenEightData M L) :
    ((CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥(L ⊔ T))).map (L ⊔ T).subtype) ≤
      CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G := L ⊔ T
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  have hXM : X ≤ M := fourteenNine_X_le_M c h8
  let O : Subgroup G := (CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X)).map X.subtype
  obtain ⟨hOnormX, hO2, hOX⟩ := pCoreOf_top_map_facts (X := X)
  have hO_le_D : O ≤ D := by
    rcases le_core_or_le_of_normal h8 (le_sup_left : L ≤ X) hXM hOX hOnormX
      (hOX.trans hXM)
      (hOX.trans (hXM.trans (fourteenNine_M_le_normalizer_L h8))) with hD | hL
    · exact hD
    · exfalso
      have hLbar2 : IsPGroup 2 (threeStar L) :=
        (hO2.to_le hL).of_surjective
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥L))
          (QuotientGroup.mk'_surjective _)
      haveI : IsSimpleGroup (threeStar L) := h8.simple
      letI : Nontrivial (threeStar L) := IsSimpleGroup.toNontrivial
      have hcent : Nontrivial ↥(Subgroup.center (threeStar L)) := hLbar2.center_nontrivial
      have hcenttop : Subgroup.center (threeStar L) = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (threeStar L)) with
          h | h
        · exact absurd h (nontrivial_iff_ne_bot (Subgroup.center (threeStar L)) |>.mp hcent)
        · exact h
      have hcomm : IsMulCommutative (threeStar L) := Subgroup.center_eq_top_iff.mp hcenttop
      obtain ⟨a, b, hab⟩ := h8.nonabelian
      exact hab (hcomm.is_comm.comm a b)
  show O ≤ D
  exact hO_le_D

private theorem fourteenNine_pCoreOf_top_le_T {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h7 : FourteenSevenData M H Q R T)
    {L : Subgroup G} (h8 : FourteenEightData M L) :
    CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥(L ⊔ T)) ≤ T.subgroupOf (L ⊔ T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G := L ⊔ T
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  have hXM : X ≤ M := fourteenNine_X_le_M c h8
  let O : Subgroup G := (CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X)).map X.subtype
  obtain ⟨hOnormX, hO2, hOX⟩ := pCoreOf_top_map_facts (X := X)
  have hO_le_D : O ≤ D := by
    show ((CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥(L ⊔ T))).map (L ⊔ T).subtype) ≤ D
    exact fourteenNine_pCoreOf_top_le_D c h7 h8
  have hO_le_D1 : O ≤ D ⊓ X := le_inf hO_le_D hOX
  have hX_le_NO : X ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mp hOnormX
  have hOD1norm : (O.subgroupOf (D ⊓ X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO_le_D1).mpr
      (inf_le_right.trans hX_le_NO)
  have hO_le_T : O ≤ T := by
    have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ D) (D ⊓ X) :=
      h7.sylow_D.of_le (le_inf inf_le_right (inf_le_left.trans le_sup_right)) inf_le_left
    obtain ⟨S₁, hS₁⟩ := hSyl.exists_sylow_eq_subgroupOf
    haveI : (O.subgroupOf (D ⊓ X)).Normal := hOD1norm
    have hle : O.subgroupOf (D ⊓ X) ≤ (S₁ : Subgroup ↥(D ⊓ X)) :=
      @IsPGroup.le_sylow_of_normal 2 ↥(D ⊓ X) _ (O.subgroupOf (D ⊓ X)) hOD1norm
        (hO2.comap_subtype) S₁
    have hmap := Subgroup.map_mono (f := (D ⊓ X).subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hO_le_D1] at hmap
    have hS₁D : (S₁ : Subgroup ↥(D ⊓ X)).map (D ⊓ X).subtype = T ⊓ D := by
      rw [hS₁, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (le_inf inf_le_right (inf_le_left.trans le_sup_right))]
    rw [hS₁D] at hmap
    exact fun x hx => (hmap hx).1
  show CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X) ≤ T.subgroupOf X
  exact (Subgroup.map_le_iff_le_comap).mp (by simpa [O] using hO_le_T)

theorem CaseOneCtx.fourteenNine_zero (c : CaseOneCtx G M H E Q J R T)
    (h7 : FourteenSevenData M H Q R T) {L : Subgroup G} (h8 : FourteenEightData M L) :
    CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup ↥(L ⊔ T)) ∧
      CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥(L ⊔ T)) ≤ T.subgroupOf (L ⊔ T) :=
  ⟨fourteenNine_charTwo_top c h7 h8, fourteenNine_pCoreOf_top_le_T c h7 h8⟩

theorem CaseOneCtx.fourteenNine_stepOne (c : CaseOneCtx G M H E Q J R T)
    (h7 : FourteenSevenData M H Q R T) {L : Subgroup G} (h8 : FourteenEightData M L)
    {C : Subgroup G} (hC1 : C ≠ ⊥) (hC2 : IsPGroup 2 C)
    (hTC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G)) :
    ¬ L ≤ (L ⊓ Subgroup.normalizer (C : Set G)) ⊔ CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
  intro hL
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  let N : Subgroup G := L ⊓ Subgroup.normalizer (C : Set G)
  obtain ⟨p, hp⟩ := c.choice.sigma_nonempty
  have hpprime : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hNM : N ≤ M := inf_le_left.trans h8.L_le
  have hDN : N ≤ Subgroup.normalizer (D : Set G) :=
    hNM.trans (fourteenNine_M_le_normalizer_D M)
  let f : ↥N →* threeStar L :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥L)).comp (Subgroup.inclusion inf_le_left)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥L) y
    have hlND : (l : G) ∈ ((N ⊔ D : Subgroup G) : Set G) := hL l.2
    have hmul : ((N ⊔ D : Subgroup G) : Set G) = (N : Set G) * (D : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right (H := N) (N := D) hDN
    rw [hmul, Set.mem_mul] at hlND
    obtain ⟨n, hnN, d, hdD, hnd⟩ := hlND
    have hnL : n ∈ L := (inf_le_left : N ≤ L) hnN
    have hdL : d ∈ L := by
      have hdn : d = n⁻¹ * l := by
        rw [← hnd]
        group
      rw [hdn]
      exact L.mul_mem (L.inv_mem hnL) l.2
    have hdker : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥L) ⟨d, hdL⟩ = 1 := by
      refine (QuotientGroup.eq_one_iff (⟨d, hdL⟩ : ↥L)).mpr ?_
      have hdmap : d ∈ (CFSG.pPrimeCore 3 ↥L).map L.subtype := by
        rw [h8.core_eq]
        exact ⟨hdL, hdD⟩
      obtain ⟨c, hc, hcd⟩ := Subgroup.mem_map.mp hdmap
      have hceq : (⟨d, hdL⟩ : ↥L) = c := Subtype.ext hcd.symm
      rw [hceq]
      exact hc
    refine ⟨⟨n, hnN⟩, ?_⟩
    change QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥L) ⟨n, hnL⟩ =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥L) ⟨l, l.2⟩
    have hl_eq : (⟨l, l.2⟩ : ↥L) = ⟨n, hnL⟩ * ⟨d, hdL⟩ := by
      apply Subtype.ext
      exact hnd.symm
    rw [hl_eq, map_mul, hdker, mul_one]
  have h2p : 2 ≤ CFSG.Open.pRank p N :=
    CFSG.Quasithin.H13.Ch4.T425C27.two_le_pRank_of_surjective f hf hp2
      (h8.rank_L p hp)
  obtain ⟨E, hEN, hEelem, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := p) hpprime.one_lt N
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  have hE2 : 2 ≤ CFSG.Open.pRank p E :=
    h2p.trans (CFSG.SectionRank.le_pRank (p := p) hpprime.one_lt le_rfl hEelem hEcard)
  have hEC : E ≤ Subgroup.normalizer (C : Set G) := hEN.trans inf_le_right
  have hEM : E ≤ M := hEN.trans hNM
  have hNleM : Subgroup.normalizer (C : Set G) ≤ M :=
    c.choice.cstar.embed p hp.1 M c.choice.maxLocal E hEM hEp hE2
      (Subgroup.normalizer (C : Set G)) ⟨C, hC1, hC2, rfl⟩ hEC
  exact h7.normalizer_T_not_le (hTC.trans hNleM)

theorem CaseOneCtx.fourteenNine_three (c : CaseOneCtx G M H E Q J R T)
    (h7 : FourteenSevenData M H Q R T) {L : Subgroup G} (h8 : FourteenEightData M L) :
    ¬ L.subgroupOf (L ⊔ T) ≤ gnC (T.subgroupOf (L ⊔ T)) := by
  intro hle
  let X : Subgroup G := L ⊔ T
  let Z : Subgroup G := CFSG.Quasithin.omegaOneCenterOf T
  have hT2 : IsPGroup 2 T := c.T_sylow.isPGroup
  have hTne : T ≠ ⊥ := fourteenNine_T_ne_bot c
  have hZne : Z ≠ ⊥ := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hT2 hTne
  have hZT : Z ≤ T := CFSG.LocalAnalysis.RankThreeUC.S15.omegaOneCenterOf_le_subgroup T
  have hZ2 : IsPGroup 2 Z := hT2.to_le hZT
  have hNTZ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
    CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf T
  have hUX : CFSG.LocalAnalysis.RankThreeUC.uCore X T ≤ X :=
    CFSG.LocalAnalysis.RankThreeUC.S15.uCore_le_of_le (le_sup_right : T ≤ X)
  have hLeC : L ≤ Subgroup.centralizer
      (CFSG.LocalAnalysis.RankThreeUC.uCore X T : Set G) := by
    intro l hl
    have hlX : (⟨l, (le_sup_left : L ≤ X) hl⟩ : X) ∈ L.subgroupOf X := hl
    have h1 : (⟨l, (le_sup_left : L ≤ X) hl⟩ : X) ∈ gnC (T.subgroupOf X) := hle hlX
    rw [CFSG.LocalAnalysis.RankThreeUC.S15.gnC_subgroupOf_eq (le_sup_right : T ≤ X)] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hLZ : L ≤ Subgroup.centralizer (Z : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzU : z ∈ CFSG.LocalAnalysis.RankThreeUC.uCore X T :=
      CFSG.LocalAnalysis.RankThreeUC.S15.omegaOneCenterOf_le_uCore X T hz
    exact (Subgroup.mem_centralizer_iff.mp (hLeC hl)) z hzU
  have hLN : L ≤ Subgroup.normalizer (Z : Set G) :=
    hLZ.trans (Subgroup.centralizer_le_normalizer (Z : Set G))
  exact (c.fourteenNine_stepOne h7 h8 hZne hZ2 hNTZ)
    (le_sup_of_le_left (le_inf le_rfl hLN))

theorem CaseOneCtx.gnC_le_core (c : CaseOneCtx G M H E Q J R T)
    (h7 : FourteenSevenData M H Q R T) {L : Subgroup G} (h8 : FourteenEightData M L) :
    (gnC (T.subgroupOf (L ⊔ T))).map (L ⊔ T).subtype ≤
      CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
  let X : Subgroup G := L ⊔ T
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  let Y : Subgroup ↥X := gnC (T.subgroupOf X)
  let Y₀ : Subgroup G := Y.map X.subtype
  have hXM : X ≤ M := fourteenNine_X_le_M c h8
  have hY0_le_X : Y₀ ≤ X := Subgroup.map_subtype_le Y
  have hY0_le_M : Y₀ ≤ M := hY0_le_X.trans hXM
  have hY0_le_NL : Y₀ ≤ Subgroup.normalizer (L : Set G) :=
    hY0_le_X.trans (hXM.trans (fourteenNine_M_le_normalizer_L h8))
  have hY0normX : (Y₀.subgroupOf X).Normal := by
    rw [subgroupOf_map_subtype_eq Y]
    infer_instance
  have hY0_le_D : Y₀ ≤ D := by
    rcases le_core_or_le_of_normal h8 (le_sup_left : L ≤ X) hXM hY0_le_X hY0normX
      hY0_le_M hY0_le_NL with hD | hL
    · exact hD
    · exfalso
      have hLsubY : L.subgroupOf X ≤ Y := by
        intro x hx
        have hxY0 : (x : G) ∈ Y.map X.subtype := hL hx
        rw [← subgroupOf_map_subtype_eq Y]
        exact hxY0
      exact c.fourteenNine_three h7 h8 hLsubY
  show (gnC (T.subgroupOf X)).map X.subtype ≤ D
  exact hY0_le_D

private theorem fourteenNine_four_frattini_top {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h7 : FourteenSevenData M H Q R T)
    {L : Subgroup G} (h8 : FourteenEightData M L)
    (hNleD : ⁅CFSG.Quasithin.thompsonJ T, L⁆ ≤ CFSG.inSubgroup (CFSG.pPrimeCore 3) M) :
    ((CFSG.inSubgroup (CFSG.pPrimeCore 3) M ⊓ (L ⊔ T)).subgroupOf (L ⊔ T)).Normal ∧
      ((CFSG.inSubgroup (CFSG.pPrimeCore 3) M ⊓ (L ⊔ T)).subgroupOf (L ⊔ T) ⊔
        Subgroup.normalizer ((CFSG.Quasithin.thompsonJ T).subgroupOf (L ⊔ T) :
          Set ↥(L ⊔ T))) = ⊤ := by
  let X : Subgroup G := L ⊔ T
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  let J : Subgroup G := CFSG.Quasithin.thompsonJ T
  have hT2 : IsPGroup 2 T := c.T_sylow.isPGroup
  have hT_le_M : T ≤ M := c.T_sylow.le.trans inf_le_right
  have hXM : X ≤ M := fourteenNine_X_le_M c h8
  have hM_le_NL : M ≤ Subgroup.normalizer (L : Set G) := fourteenNine_M_le_normalizer_L h8
  have hJ_le_T : J ≤ T := CFSG.Quasithin.B6.thompsonJ_le T
  have hJ_le_X : J ≤ X := hJ_le_T.trans le_sup_right
  have hJ_le_M : J ≤ M := hJ_le_T.trans hT_le_M
  have hJ_le_NL : J ≤ Subgroup.normalizer (L : Set G) := hJ_le_M.trans hM_le_NL
  have hJ_le_D : J ≤ D := h8.centralizing J hJ_le_M hJ_le_NL hNleD
  let S1 : Subgroup G := T ⊓ D
  have hJ_le_S1 : J ≤ S1 := le_inf hJ_le_T hJ_le_D
  have hJeq : CFSG.Quasithin.thompsonJ S1 = J :=
    CFSG.Quasithin.B6.thompsonJ_eq_of_le hJ_le_S1 inf_le_left
  have hS1_le_X : S1 ≤ X := inf_le_left.trans le_sup_right
  let D1 : Subgroup G := D ⊓ X
  have hS1_le_D1 : S1 ≤ D1 := le_inf inf_le_right (inf_le_left.trans le_sup_right)
  have hD1_le_X : D1 ≤ X := inf_le_right
  have hSylD1 : CFSG.ABGLocalTools.IsSylowOf 2 S1 D1 :=
    fourteenNine_sylow_D1 c h7 h8
  have hX_le_ND : X ≤ Subgroup.normalizer (D : Set G) :=
    hXM.trans (fourteenNine_M_le_normalizer_D M)
  have hX_le_ND1 : X ≤ Subgroup.normalizer (D1 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    rw [Subgroup.mem_inf] at hy ⊢
    exact ⟨Subgroup.le_normalizer_iff.mp hX_le_ND x hx y hy.1,
      Subgroup.le_normalizer_iff.mp (Subgroup.le_normalizer) x hx y hy.2⟩
  have hD1norm : (D1.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hD1_le_X).mpr hX_le_ND1
  have hSylX : CFSG.ABGLocalTools.IsSylowOf 2 (S1.subgroupOf X) (D1.subgroupOf X) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff X,
      Subgroup.map_subgroupOf_eq_of_le hS1_le_X,
      Subgroup.map_subgroupOf_eq_of_le hD1_le_X]
    exact hSylD1
  have hn : (⊤ : Subgroup ↥X) ≤ Subgroup.normalizer
      ((D1.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [Subgroup.le_normalizer_iff]
    intro x _ y hy
    exact hD1norm.conj_mem y hy x
  have hFrat := CFSG.LocalAnalysis.RankThreeTheoremC.le_sup_normalizer_of_isSylowOf
    (p := 2) (H := ⊤) (Y := D1.subgroupOf X) (S := S1.subgroupOf X) hn hSylX
  let J1 : Subgroup ↥X := CFSG.Quasithin.thompsonJ (S1.subgroupOf X)
  let N1 : Subgroup ↥X := Subgroup.normalizer ((S1.subgroupOf X : Subgroup ↥X) : Set ↥X)
  let N0 : Subgroup ↥X := Subgroup.normalizer (J.subgroupOf X : Set ↥X)
  have hJ1map : J1.map X.subtype = J := by
    dsimp [J1, J]
    rw [CFSG.Quasithin.SteinbergCG.thompsonJ_subgroupOf_map hS1_le_X, hJeq]
  have hJ1eq : J1 = J.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [hJ1map, Subgroup.map_subgroupOf_eq_of_le hJ_le_X]
  have hN1_le_N0 : N1 ≤ N0 := by
    have h := CFSG.Quasithin.normalizer_le_normalizer_thompsonJ (S1.subgroupOf X)
    simpa [N0, J1, hJ1eq] using h
  have hFratN0 : (⊤ : Subgroup ↥X) ≤ (D1.subgroupOf X) ⊔ N0 :=
    hFrat.trans (sup_le_sup_left hN1_le_N0 (D1.subgroupOf X))
  show (D1.subgroupOf X).Normal ∧ (D1.subgroupOf X ⊔ N0) = ⊤
  exact ⟨hD1norm, top_le_iff.mp hFratN0⟩

private theorem fourteenNine_four_frattini {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h7 : FourteenSevenData M H Q R T)
    {L : Subgroup G} (h8 : FourteenEightData M L)
    (hNleD : ⁅CFSG.Quasithin.thompsonJ T, L⁆ ≤ CFSG.inSubgroup (CFSG.pPrimeCore 3) M) :
    L.subgroupOf (L ⊔ T) ≤
      (L.subgroupOf (L ⊔ T) ⊓
        Subgroup.normalizer ((CFSG.Quasithin.thompsonJ T).subgroupOf (L ⊔ T) : Set ↥(L ⊔ T)))
      ⊔ (CFSG.inSubgroup (CFSG.pPrimeCore 3) M ⊓ (L ⊔ T)).subgroupOf (L ⊔ T) := by
  let X : Subgroup G := L ⊔ T
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  let J : Subgroup G := CFSG.Quasithin.thompsonJ T
  let D1 : Subgroup ↥X := (D ⊓ X).subgroupOf X
  let N0 : Subgroup ↥X := Subgroup.normalizer (J.subgroupOf X : Set ↥X)
  have hXM : X ≤ M := fourteenNine_X_le_M c h8
  have hM_le_NL : M ≤ Subgroup.normalizer (L : Set G) := fourteenNine_M_le_normalizer_L h8
  have hT2 : IsPGroup 2 T := c.T_sylow.isPGroup
  obtain ⟨hD1norm, hFratN0⟩ := fourteenNine_four_frattini_top c h7 h8 hNleD
  have hLnormX : (L.subgroupOf X).Normal :=
    subgroupOf_normal_of_le_normalizer le_sup_left hXM hM_le_NL
  have hQ2 : IsPGroup 2 (↥X ⧸ L.subgroupOf X) :=
    fourteenNine_quotient_isPGroup_two rfl hLnormX hT2
  have hNres : (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
      ↥N0).map N0.subtype ≤ L.subgroupOf X :=
    fourteenNine_primeResidual_le_of_quotient_two N0 hLnormX hQ2
  have hLres : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
      ↥(L.subgroupOf X) = ⊤ :=
    fourteenNine_primeResidual_subgroupOf (le_sup_left : L ≤ X) h8.residual
  have hL' : L.subgroupOf X ≤ (L.subgroupOf X ⊓ N0) ⊔ D1 :=
    fourteenNine_le_sup_inf hD1norm hFratN0 hLres hNres
  show L.subgroupOf X ≤ (L.subgroupOf X ⊓ N0) ⊔ D1
  exact hL'

theorem CaseOneCtx.fourteenNine_four (c : CaseOneCtx G M H E Q J R T)
    (h7 : FourteenSevenData M H Q R T) {L : Subgroup G} (h8 : FourteenEightData M L) :
    ⁅CFSG.Quasithin.thompsonJ T, L⁆ = L := by
  let X : Subgroup G := L ⊔ T
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  let J : Subgroup G := CFSG.Quasithin.thompsonJ T
  let N : Subgroup G := ⁅J, L⁆
  have hT2 : IsPGroup 2 T := c.T_sylow.isPGroup
  have hTne : T ≠ ⊥ := fourteenNine_T_ne_bot c
  have hT_le_M : T ≤ M := c.T_sylow.le.trans inf_le_right
  have hXM : X ≤ M := fourteenNine_X_le_M c h8
  have hM_le_NL : M ≤ Subgroup.normalizer (L : Set G) := fourteenNine_M_le_normalizer_L h8
  have hJ_le_T : J ≤ T := CFSG.Quasithin.B6.thompsonJ_le T
  have hJ_le_X : J ≤ X := hJ_le_T.trans le_sup_right
  have hJ_le_M : J ≤ M := hJ_le_T.trans hT_le_M
  have hJ_le_NL : J ≤ Subgroup.normalizer (L : Set G) := hJ_le_M.trans hM_le_NL
  have hN_le_L : N ≤ L := Subgroup.le_normalizer_iff_commutator_le_right.mp hJ_le_NL
  have hNnorm : (N.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_L]
    exact Subgroup.normalizer_commutator_ge_right J L
  rcases h8.dichotomy N hN_le_L hNnorm with hNleD | hNeqL
  · exfalso
    have hL' := fourteenNine_four_frattini c h7 h8 hNleD
    have hN0map_le : (Subgroup.normalizer (J.subgroupOf X : Set ↥X)).map X.subtype ≤
        Subgroup.normalizer (J : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro y hy j hj
      obtain ⟨n, hnN0, hny⟩ := Subgroup.mem_map.mp hy
      have hmem := (Subgroup.mem_normalizer_iff.mp hnN0
        (⟨j, hJ_le_X hj⟩ : ↥X)).mp hj
      have hval : X.subtype (n * (⟨j, hJ_le_X hj⟩ : ↥X) * n⁻¹) ∈ J := hmem
      rwa [map_mul, map_mul, map_inv, hny] at hval
    have hLgoal : L ≤ (L ⊓ Subgroup.normalizer (J : Set G)) ⊔ D := by
      have hmap := Subgroup.map_mono (f := X.subtype) hL'
      rw [Subgroup.map_subgroupOf_eq_of_le (le_sup_left : L ≤ X),
        Subgroup.map_sup, Subgroup.map_inf _ _ _ X.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le (le_sup_left : L ≤ X),
        Subgroup.map_subgroupOf_eq_of_le (inf_le_right : D ⊓ X ≤ X)] at hmap
      exact hmap.trans (sup_le ((inf_le_inf_left L hN0map_le).trans le_sup_left)
        ((inf_le_left : D ⊓ X ≤ D).trans le_sup_right))
    exact (c.fourteenNine_stepOne h7 h8
      (CFSG.Quasithin.thompsonJ_ne_bot_of_isPGroup hT2 hTne)
      (hT2.to_le hJ_le_T) (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ T)) hLgoal
  · exact hNeqL

private theorem fourteenNine_one_not_le {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h7 : FourteenSevenData M H Q R T)
    {L : Subgroup G} (h8 : FourteenEightData M L) :
    ¬ L.subgroupOf (L ⊔ T) ≤
      (CFSG.pCore 2 (↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T)))).comap
        (QuotientGroup.mk' (gnC (T.subgroupOf (L ⊔ T)))) := by
  let X : Subgroup G := L ⊔ T
  let Y : Subgroup ↥X := gnC (T.subgroupOf X)
  haveI : Y.Normal := inferInstance
  let Q : Type := ↥X ⧸ Y
  let π : ↥X →* Q := QuotientGroup.mk' Y
  let P : Subgroup Q := CFSG.pCore 2 Q
  let U : Subgroup ↥X := P.comap π
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup (p := 2) (G := Q)
  intro hLU
  apply c.fourteenNine_three h7 h8
  have hLres := fourteenNine_primeResidual_subgroupOf (le_sup_left : L ≤ X) h8.residual
  have hgen : L.subgroupOf X = Subgroup.closure ((L.subgroupOf X).subtype ''
      {x : ↥(L.subgroupOf X) | ∃ k, orderOf x = 3 ^ k}) := by
    have hmap : (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
        ↥(L.subgroupOf X)).map (L.subgroupOf X).subtype = L.subgroupOf X := by
      rw [hLres, Subgroup.map_top, Subgroup.range_subtype]
    conv_lhs => rw [← hmap]
    rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_closure,
      MonoidHom.map_closure]
  conv_lhs => rw [hgen]
  refine (Subgroup.closure_le Y).2 ?_
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨k, hk⟩ := hl
  have hlU : π l ∈ P := Subgroup.mem_comap.mp (hLU l.2)
  have hdvd1 : orderOf (π (l : ↥X)) ∣ 3 ^ k := by
    have h := orderOf_map_dvd π (l : ↥X)
    rwa [Subgroup.orderOf_coe l, hk] at h
  obtain ⟨j, hj⟩ := hP2.exists_orderOf_eq_pow (⟨π (l : ↥X), hlU⟩ : P)
  have hdvd2 : orderOf (π (l : ↥X)) ∣ 2 ^ j := by
    have hco := Subgroup.orderOf_coe (⟨π (l : ↥X), hlU⟩ : P)
    rw [hj] at hco
    rw [hco]
  have hcop : Nat.Coprime (3 ^ k) (2 ^ j) :=
    Nat.Coprime.pow k j (by norm_num : Nat.Coprime 3 2)
  have horder1 : orderOf (π (l : ↥X)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have hπl : π (l : ↥X) = 1 := orderOf_eq_one_iff.mp horder1
  exact (QuotientGroup.eq_one_iff (l : ↥X)).mp hπl

private theorem fourteenNine_one_le_D {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h7 : FourteenSevenData M H Q R T)
    {L : Subgroup G} (h8 : FourteenEightData M L) :
    (((CFSG.pCore 2 (↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T)))).comap
      (QuotientGroup.mk' (gnC (T.subgroupOf (L ⊔ T))))).map (L ⊔ T).subtype) ≤
      CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
  let X : Subgroup G := L ⊔ T
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  let Y : Subgroup ↥X := gnC (T.subgroupOf X)
  haveI : Y.Normal := inferInstance
  let Q : Type := ↥X ⧸ Y
  let π : ↥X →* Q := QuotientGroup.mk' Y
  let P : Subgroup Q := CFSG.pCore 2 Q
  let U : Subgroup ↥X := P.comap π
  let U0 : Subgroup G := U.map X.subtype
  have hUnorm : U.Normal := (CFSG.pCore_normal (p := 2) (G := Q)).comap π
  have hU0normX : (U0.subgroupOf X).Normal := by
    rw [subgroupOf_map_subtype_eq U]
    exact hUnorm
  have hXM : X ≤ M := fourteenNine_X_le_M c h8
  have hU0_le_X : U0 ≤ X := Subgroup.map_subtype_le U
  have hU0_le_D : U0 ≤ D := by
    rcases le_core_or_le_of_normal h8 (le_sup_left : L ≤ X) hXM hU0_le_X hU0normX
      (hU0_le_X.trans hXM)
      (hU0_le_X.trans (hXM.trans (fourteenNine_M_le_normalizer_L h8))) with hD | hL
    · exact hD
    · exfalso
      have hLU : L.subgroupOf X ≤ U := by
        intro x hx
        have hxU0 : (x : G) ∈ U.map X.subtype := hL hx
        rw [← subgroupOf_map_subtype_eq U]
        exact hxU0
      exact fourteenNine_one_not_le c h7 h8 hLU
  show U0 ≤ D
  exact hU0_le_D

private theorem fourteenNine_one_le_sup {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h7 : FourteenSevenData M H Q R T)
    {L : Subgroup G} (h8 : FourteenEightData M L) :
    ∃ S : Subgroup ↥(L ⊔ T),
      S ≤ T.subgroupOf (L ⊔ T) ∧
      ((CFSG.pCore 2 (↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T)))).comap
        (QuotientGroup.mk' (gnC (T.subgroupOf (L ⊔ T))))) ≤
        S ⊔ gnC (T.subgroupOf (L ⊔ T)) := by
  let X : Subgroup G := L ⊔ T
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  let Y : Subgroup ↥X := gnC (T.subgroupOf X)
  haveI : Y.Normal := inferInstance
  let Q : Type := ↥X ⧸ Y
  let π : ↥X →* Q := QuotientGroup.mk' Y
  let P : Subgroup Q := CFSG.pCore 2 Q
  let U : Subgroup ↥X := P.comap π
  let U0 : Subgroup G := U.map X.subtype
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup (p := 2) (G := Q)
  have hUnorm : U.Normal := (CFSG.pCore_normal (p := 2) (G := Q)).comap π
  have hU0_le_D : U0 ≤ D := fourteenNine_one_le_D c h7 h8
  have hU0_le_X : U0 ≤ X := Subgroup.map_subtype_le U
  have hU0normX : (U0.subgroupOf X).Normal := by
    rw [subgroupOf_map_subtype_eq U]
    exact hUnorm
  have hU0_le_D1 : U0 ≤ D ⊓ X := le_inf hU0_le_D hU0_le_X
  have hD1_le_NU0 : D ⊓ X ≤ Subgroup.normalizer (U0 : Set G) := by
    have hX_le_NU0 : X ≤ Subgroup.normalizer (U0 : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hU0_le_X).mp hU0normX
    exact inf_le_right.trans hX_le_NU0
  have hSylU0G : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ U0) U0 := by
    have h := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer
      (p := 2) (h := fourteenNine_sylow_D1 c h7 h8) hU0_le_D1 hD1_le_NU0
    have h' : (T ⊓ D) ⊓ U0 = T ⊓ U0 := by
      rw [inf_assoc, inf_eq_right.mpr hU0_le_D]
    rwa [h'] at h
  let S : Subgroup ↥X := (T ⊓ U0).subgroupOf X
  have hTU0_le_X : T ⊓ U0 ≤ X := (inf_le_left : T ⊓ U0 ≤ T).trans le_sup_right
  have hSylUX : CFSG.ABGLocalTools.IsSylowOf 2 S U := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff X]
    rw [Subgroup.map_subgroupOf_eq_of_le hTU0_le_X]
    exact hSylU0G
  have hUmapP : U.map π = P := by
    change (P.comap π).map π = P
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Y) P
  have hf : Function.Surjective (π.subgroupMap U) := MonoidHom.subgroupMap_surjective π U
  have hker : (π.subgroupMap U).ker = Y.subgroupOf U := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff (N := Y) (x : ↥X)).mp (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      change (QuotientGroup.mk' Y) (x : ↥X) = 1
      exact (QuotientGroup.eq_one_iff (N := Y) (x : ↥X)).mpr h
  have hQ2 : IsPGroup 2 ↥(U.map π) := by
    rw [hUmapP]
    exact hP2
  have hU_le_SY : U ≤ S ⊔ Y :=
    le_sup_of_sylow_of_surjective_isPGroup (π.subgroupMap U) hf hker hQ2 hSylUX
  have hS_le_Tsub : S ≤ T.subgroupOf X := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_subgroupOf.mp hx).1)
  exact ⟨S, hS_le_Tsub, hU_le_SY⟩

private theorem fourteenNine_one_le_Y {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h7 : FourteenSevenData M H Q R T)
    {L : Subgroup G} (h8 : FourteenEightData M L) :
    (CFSG.pCore 2 (↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T)))).comap
      (QuotientGroup.mk' (gnC (T.subgroupOf (L ⊔ T)))) ≤
      gnC (T.subgroupOf (L ⊔ T)) := by
  let X : Subgroup G := L ⊔ T
  let Y : Subgroup ↥X := gnC (T.subgroupOf X)
  haveI : Y.Normal := inferInstance
  let Q : Type := ↥X ⧸ Y
  let π : ↥X →* Q := QuotientGroup.mk' Y
  let P : Subgroup Q := CFSG.pCore 2 Q
  let U : Subgroup ↥X := P.comap π
  have hUnorm : U.Normal := (CFSG.pCore_normal (p := 2) (G := Q)).comap π
  obtain ⟨S, hS_le_Tsub, hU_le_SY⟩ := fourteenNine_one_le_sup c h7 h8
  let Z : Subgroup ↥X := CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf X)
  have hTsub_le_CZ : T.subgroupOf X ≤ Subgroup.centralizer (Z : Set ↥X) := by
    rw [Subgroup.le_centralizer_iff]
    exact (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf (T.subgroupOf X)).trans
      inf_le_right
  have hS_le_CZ : S ≤ Subgroup.centralizer (Z : Set ↥X) :=
    hS_le_Tsub.trans hTsub_le_CZ
  have hY_le_CZ : Y ≤ Subgroup.centralizer (Z : Set ↥X) := by
    change Subgroup.centralizer (gnV (T.subgroupOf X) : Set ↥X) ≤
      Subgroup.centralizer (Z : Set ↥X)
    exact Subgroup.centralizer_le (by
      intro z hz
      exact Subgroup.subset_normalClosure (by simpa [Z] using hz))
  have hU_le_CZ : U ≤ Subgroup.centralizer (Z : Set ↥X) :=
    hU_le_SY.trans (sup_le hS_le_CZ hY_le_CZ)
  have hZ_le_CU : Z ≤ Subgroup.centralizer (U : Set ↥X) :=
    (Subgroup.le_centralizer_iff).mpr hU_le_CZ
  have hU_le_Y : U ≤ Y := by
    have h := le_centralizer_normalClosure hUnorm hZ_le_CU
    simpa [Y, gnC, gnV, Z] using h
  show U ≤ Y
  exact hU_le_Y

theorem CaseOneCtx.fourteenNine_one (c : CaseOneCtx G M H E Q J R T)
    (h7 : FourteenSevenData M H Q R T) {L : Subgroup G} (h8 : FourteenEightData M L) :
    CFSG.pCore 2 (↥(L ⊔ T) ⧸ gnC (T.subgroupOf (L ⊔ T))) = ⊥ := by
  let X : Subgroup G := L ⊔ T
  let D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M
  let Y : Subgroup ↥X := gnC (T.subgroupOf X)
  haveI : Y.Normal := inferInstance
  let Q : Type := ↥X ⧸ Y
  let π : ↥X →* Q := QuotientGroup.mk' Y
  let P : Subgroup Q := CFSG.pCore 2 Q
  let U : Subgroup ↥X := P.comap π
  have hU_le_Y : U ≤ Y := fourteenNine_one_le_Y c h7 h8
  have hY_le_U : Y ≤ U := by
    intro y hy
    change y ∈ P.comap π
    rw [Subgroup.mem_comap]
    have hπy : π y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    rw [hπy]
    exact Subgroup.one_mem P
  have hUY : U = Y := le_antisymm hU_le_Y hY_le_U
  have hUmapP : U.map π = P := by
    change (P.comap π).map π = P
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Y) P
  show P = ⊥
  rw [← hUmapP, hUY]
  exact QuotientGroup.map_mk'_self Y

theorem CaseOneCtx.fourteenNineData_of (c : CaseOneCtx G M H E Q J R T)
    (h7 : FourteenSevenData M H Q R T) {L : Subgroup G} (h8 : FourteenEightData M L) :
    FourteenNineData M L T :=
  ⟨(c.fourteenNine_zero h7 h8).1, (c.fourteenNine_zero h7 h8).2,
   c.fourteenNine_one h7 h8, c.gnC_le_core h7 h8, c.fourteenNine_four h7 h8,
   c.fourteenNine_three h7 h8⟩
