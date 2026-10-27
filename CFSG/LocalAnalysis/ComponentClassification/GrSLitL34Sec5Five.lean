module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Pump
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Commute
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup
public import CFSG.RankThree.PartTwo.KFacts.K72Moving
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Cor211

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem lieModel_center_of_isStandardSubgroup {J : Subgroup G}
    (htype : IsL34Type (J ⧸ Open.fusionZStar J)) (hst : IsStandardSubgroup J)
    (hO : oddIn J ≤ (center ↥J).map J.subtype) :
    Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 3 2 2 := by
  have hq : IsQuasisimple J := hst.1
  have hO' : pPrimeCore 2 ↥J ≤ center ↥J := by
    intro y hy
    obtain ⟨w, hw, hwy⟩ := hO ⟨y, hy, rfl⟩
    rwa [← Subtype.ext hwy]
  have heq := fusionZStar_eq_center_of_le hq.1.commutator_eq_top hO'
  exact LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq heq) htype

theorem false_of_l34StandardOutcome (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hbase : L34BaseSetting G)
    (h : Nonempty (G ≃* Blueprint.NativeSporadic.Suz) ∨
      Nonempty (G ≃* Blueprint.NativeSporadic.He) ∨
      Nonempty (G ≃* Blueprint.NativeSporadic.ON)) : False := by
  obtain ⟨hsF, hnF, -⟩ := fstar_facts hbase
  obtain ⟨hsimple, -, -, hz, hUo, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  have htop : GeneralizedFitting.subgroup G = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  apply hUo
  refine hU G hsF hnF ?_ hz
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.Suz, ⟨eF.trans e⟩⟩)))
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.He, ⟨eF.trans e⟩⟩)))
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.ONan, ⟨eF.trans e⟩⟩)))

theorem not_isStandardSubgroup_of_l34 (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hStd : GSThmB.L34StandardInput) (hbase : L34BaseSetting G) {J : Subgroup G}
    (htype : IsL34Type (J ⧸ Open.fusionZStar J)) (hst : IsStandardSubgroup J)
    (hO : oddIn J ≤ (center ↥J).map J.subtype) : False := by
  have : IsSimpleGroup G := hbase.1
  exact false_of_l34StandardOutcome hU hbase
    (hStd G hbase.2.1 hbase.2.2.1 J hst (lieModel_center_of_isStandardSubgroup htype hst hO))

theorem exists_pumpUp_not_oddIn_le_center
    (hS : SchreierFor Blueprint.Catalog) (hMax : MaximalTwoComponentInput)
    (hbase : L34BaseSetting G) {a x : G} {J : Subgroup G} (hT : GSUnbalancingTriple a x J)
    (htype : IsL34Type (J ⧸ Open.fusionZStar J)) (hmax : GSWeakMaximalComponent J)
    (hns : IsStandardSubgroup J → oddIn J ≤ (center ↥J).map J.subtype → False) :
    ∃ b t : G, orderOf b = 2 ∧ J ≤ centralizer ({b} : Set G) ∧
      IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))) ∧ orderOf t = 2 ∧
      b * t = t * b ∧ J ≤ centralizer ({t} : Set G) ∧
      ¬ oddIn (pumpUp J t) ≤ (center ↥J).map J.subtype := by
  obtain ⟨hsF, hnF, hoF⟩ := fstar_facts hbase
  have hbase' := hbase
  obtain ⟨hsimple, hnab, hK, -, -, -, -, -⟩ := hbase'
  have : IsSimpleGroup G := hsimple
  have hZ : ∀ g : G, g ≠ 1 → g ∉ center G := fun g hg => not_mem_center_of_ne_one hnab hg
  obtain ⟨ha, -, -, hJa, hJp, -, -⟩ := hT
  have h3 := three_le_pRank_of_l34 htype
  have hT9 := hMax G hsF hnF hoF hK J hmax (by omega) (Sol78.not_psp4_of_l34 htype)
    (Or.inl ⟨htype, hbase⟩)
  by_contra hno
  push Not at hno
  obtain ⟨hst, hO⟩ := isStandardSubgroup_of_cor211 hS hK hZ ha hJa hJp
    (fun t ht hJt => (hT9 t ht hJt).1) ((hT9 a ha hJa).2 h3) hno
  exact hns hst hO

theorem odd_relIndex_of_sup_oddIn {J P : Subgroup G} (hJP : J ≤ P) (hsup : J ⊔ oddIn P = P) :
    Odd (J.relIndex P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, e, -⟩ := restriction_quotient_mulEquiv hJP hsup
  have hP := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥P)
  have hJ := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥J)
  have hq : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) = Nat.card (↥P ⧸ pPrimeCore 2 ↥P) :=
    Nat.card_congr e.toEquiv
  have hidx : J.relIndex P * Nat.card J = Nat.card P := by
    rw [Subgroup.relIndex, ← Nat.card_congr (subgroupOfEquivOfLe hJP).toEquiv]
    exact Subgroup.index_mul_card _
  have hqpos : 0 < Nat.card (↥P ⧸ pPrimeCore 2 ↥P) := Nat.card_pos
  have h1 : J.relIndex P * Nat.card (pPrimeCore 2 ↥J) = Nat.card (pPrimeCore 2 ↥P) := by
    rw [hJ, hq, hP] at hidx
    apply Nat.eq_of_mul_eq_mul_left hqpos
    rw [← hidx]
    ring
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥P)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rw [← h1] at hodd
  exact Nat.Odd.of_mul_left hodd

theorem isSylowTwoIn_of_sup_oddIn {Q J P : Subgroup G} (hQ : IsSylowTwoIn Q J) (hJP : J ≤ P)
    (hsup : J ⊔ oddIn P = P) : IsSylowTwoIn Q P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 := hQ.isPGroup
  obtain ⟨hQJ, R, hR⟩ := hQ
  have hQJidx : Odd (Q.relIndex J) := by
    have h1 := R.not_dvd_index
    rw [hR] at h1
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h1)
  have hodd : Odd (Q.relIndex P) := by
    rw [← Subgroup.relIndex_mul_relIndex Q J P hQJ hJP]
    exact hQJidx.mul (odd_relIndex_of_sup_oddIn hJP hsup)
  have hQP : Q ≤ P := hQJ.trans hJP
  have hQ2' : IsPGroup 2 ↥(Q.subgroupOf P) := hQ2.of_equiv (subgroupOfEquivOfLe hQP).symm
  have hnd : ¬ 2 ∣ (Q.subgroupOf P).index := Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)
  exact ⟨hQP, hQ2'.toSylow hnd, IsPGroup.toSylow_coe hQ2' hnd⟩

omit [Finite G] in
theorem mul_self_eq_one_of_mem_zpowers {t z : G} (ht : t * t = 1) (hz : z ∈ zpowers t) :
    z * z = 1 := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
  rw [← (Commute.refl t).mul_zpow, ht, one_zpow]

theorem wGroup_eq_bot_of_le_sup_zpowers {J : Subgroup G}
    (hW : ∀ A : Subgroup G, A ≤ withKernel J → IsEightGroup A → wGroup A = ⊥)
    {P Q : Subgroup G} {t : G} (hQ : IsSylowTwoIn Q P)
    (hQJ : Q ≤ J) (ht : t * t = 1) (hPt : P ≤ centralizer ({t} : Set G))
    (htK : t ∈ coreActionKernel J) {A : Subgroup G} (hA : IsEightGroup A)
    (hAP : A ≤ P ⊔ zpowers t) : wGroup A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzC : zpowers t ≤ centralizer ({t} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hAt : A ≤ centralizer ({t} : Set G) := hAP.trans (sup_le hPt hzC)
  have htP : zpowers t ≤ normalizer (P : Set G) := zpowers_le.mpr
    (mem_normalizer_of_commute fun y hy => (mem_centralizer_singleton_iff.mp (hPt hy)).symm)
  have htA : zpowers t ≤ normalizer (A : Set G) := zpowers_le.mpr
    (mem_normalizer_of_commute fun y hy => (mem_centralizer_singleton_iff.mp (hAt hy)).symm)
  have hPdec : ((P ⊔ zpowers t : Subgroup G) : Set G) = (P : Set G) * (zpowers t : Set G) :=
    coe_mul_of_right_le_normalizer_left P (zpowers t) htP
  have hAdec : ((A ⊔ zpowers t : Subgroup G) : Set G) = (A : Set G) * (zpowers t : Set G) :=
    coe_mul_of_right_le_normalizer_left A (zpowers t) htA
  have hzcomm : ∀ z ∈ zpowers t, ∀ y ∈ centralizer ({t} : Set G), z * y = y * z := by
    intro z hz y hy
    have hty : t ∈ centralizer ({y} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hy).symm
    exact mem_centralizer_singleton_iff.mp (zpowers_le.mpr hty hz)
  set A₁ := (A ⊔ zpowers t) ⊓ P with hA₁
  have hA₁2 : IsPGroup 2 A₁ := by
    intro y
    refine ⟨1, Subtype.ext ?_⟩
    have hy : (y : G) ∈ ((A ⊔ zpowers t : Subgroup G) : Set G) := (mem_inf.mp y.2).1
    rw [hAdec] at hy
    obtain ⟨c, hc, z, hz, hcz⟩ := hy
    have hcz' : c * z = (y : G) := hcz
    simp only [pow_one, pow_two, coe_mul, OneMemClass.coe_one]
    rw [← hcz', show c * z * (c * z) = c * (z * c) * z by group,
      hzcomm z hz c (hAt hc), show c * (c * z) * z = (c * c) * (z * z) by group,
      hA.1.2 c hc, mul_self_eq_one_of_mem_zpowers ht hz, one_mul]
  obtain ⟨g, hgP, hgQ⟩ := exists_conjugate_le_of_isSylowTwoIn hQ inf_le_right hA₁2
  have hle : conjugate A g ≤ withKernel J := by
    intro w hw
    rw [mem_conjugate_iff] at hw
    have hy : g * w * g⁻¹ ∈ ((P ⊔ zpowers t : Subgroup G) : Set G) := hAP hw
    rw [hPdec] at hy
    obtain ⟨p, hp, z, hz, hpz⟩ := hy
    have hpz' : p * z = g * w * g⁻¹ := hpz
    have hpA : p ∈ A₁ := by
      refine mem_inf.mpr ⟨?_, hp⟩
      rw [show p = (g * w * g⁻¹) * z⁻¹ by rw [← hpz']; group]
      exact mul_mem (mem_sup_left hw) (mem_sup_right (inv_mem hz))
    have hgz : z * g = g * z := hzcomm z hz g (hPt hgP)
    have hw' : w = (g⁻¹ * p * g) * z := by
      calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
        _ = g⁻¹ * (p * z) * g := by rw [hpz']
        _ = g⁻¹ * p * (z * g) := by group
        _ = g⁻¹ * p * (g * z) := by rw [hgz]
        _ = (g⁻¹ * p * g) * z := by group
    rw [hw']
    refine mul_mem (mem_sup_left (hQJ (hgQ ?_))) (mem_sup_right (zpowers_le.mpr htK hz))
    exact conj_mem_conjugate hpA g
  have h1 := hW (conjugate A g) hle (isEightGroup_conjugate hA g)
  rw [wGroup_conjugate] at h1
  rw [← conjugate_conjugate_inv (wGroup A) g, h1]
  exact Subgroup.map_bot _

theorem wGroup_eq_bot_of_le_coreActionKernel (hGW : GWTwoBalanced G) {P : Subgroup G}
    (h3 : 3 ≤ pRank 2 ↥P) (hP : ∀ B : Subgroup G, B ≤ P → IsEightGroup B → wGroup B = ⊥)
    {A : Subgroup G} (hA : IsEightGroup A) (hAK : A ≤ coreActionKernel P) : wGroup A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := hA.1.isPGroup
  have hAN : A ≤ normalizer (P : Set G) := fun c hc => (mem_coreActionKernel.mp (hAK hc)).1
  obtain ⟨R0, hR0⟩ := RankThree.PartTwo.KFacts.exists_sylow_le_normalizer hA2 hAN
  set R : Subgroup G := (R0 : Subgroup ↥P).map P.subtype with hR
  have hRsyl : IsSylowTwoIn R P :=
    ⟨map_subtype_le _, R0, (comap_map_eq_self_of_injective P.subtype_injective _).symm⟩
  have hRO : R ⊓ oddIn P = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    obtain ⟨k, hk⟩ := hRsyl.isPGroup.exists_card_eq
    have hodd : Odd (Nat.card (oddIn P)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    rw [hk]
    exact (Nat.coprime_two_left.mpr hodd).pow_left k
  have hRA : ∀ c ∈ A, ∀ r ∈ R, c * r = r * c := by
    intro c hc r hr
    have h1 : r⁻¹ * c⁻¹ * r * c ∈ oddIn P := (mem_coreActionKernel.mp (hAK hc)).2 r (hRsyl.1 hr)
    have h2 : r⁻¹ * c⁻¹ * r * c ∈ R := by
      have h3 := (mem_normalizer_iff.mp (inv_mem (hR0 hc)) r).mp hr
      rw [inv_inv] at h3
      rw [show r⁻¹ * c⁻¹ * r * c = r⁻¹ * (c⁻¹ * r * c) by group]
      exact mul_mem (inv_mem hr) h3
    have h4 : r⁻¹ * c⁻¹ * r * c = 1 := by
      have h5 : r⁻¹ * c⁻¹ * r * c ∈ R ⊓ oddIn P := mem_inf.mpr ⟨h2, h1⟩
      rw [hRO] at h5
      exact h5
    calc c * r = r * c * (r⁻¹ * c⁻¹ * r * c)⁻¹ := by group
      _ = r * c := by rw [h4, inv_one, mul_one]
  obtain ⟨F, hFP, hF, hF8⟩ := exists_isElemTwo_of_three_le_pRank h3
  obtain ⟨F', hF'F, hF'8⟩ := exists_le_card_eight hF.isPGroup hF8
  have hF'E : IsEightGroup F' := ⟨hF.mono hF'F, hF'8⟩
  obtain ⟨g, -, hgR⟩ :=
    exists_conjugate_le_of_isSylowTwoIn hRsyl (hF'F.trans hFP) hF'E.1.isPGroup
  have hBE : IsEightGroup (conjugate F' g) := isEightGroup_conjugate hF'E g
  rw [wGroup_eq_of_commute hGW (A := A) (A' := conjugate F' g)
    ⟨hA2, hA.1.1, hA.1.three_le_pRank hA.2.symm.le⟩
    ⟨hBE.1.isPGroup, hBE.1.1, hBE.1.three_le_pRank hBE.2.symm.le⟩
    fun c hc y hy => hRA c hc y (hgR hy)]
  exact hP _ (hgR.trans hRsyl.1) hBE

theorem isL34Family_pumpUp_of_bad
    (hS : SchreierFor Blueprint.Catalog) (hSol : SolomonCommutingCoreInput)
    (hbase : L34BaseSetting G) {a x b t : G} {J : Subgroup G}
    (hT : GSUnbalancingTriple a x J) (htype : IsL34Type (J ⧸ Open.fusionZStar J))
    (hmax : GSWeakMaximalComponent J) (hb : orderOf b = 2)
    (hJb : J ≤ centralizer ({b} : Set G))
    (hJbp : IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G)))) (ht : orderOf t = 2)
    (hbt : b * t = t * b) (hJt : J ≤ centralizer ({t} : Set G)) (hat : a * t = t * a)
    (hT91 : (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
      oddIn (centralizer ({t} : Set G)) ⊔ J)
    (hbad : ¬ oddIn (pumpUp J t) ≤ (center ↥J).map J.subtype)
    (hW : ∀ A : Subgroup G, A ≤ withKernel J → IsEightGroup A → wGroup A = ⊥) :
    IsL34Family (pumpUp J t) t ∧ J ⊔ oddIn (pumpUp J t) = pumpUp J t := by
  have hbase' := hbase
  obtain ⟨hsimple, hnab, hK, -, -, hLB, -, -⟩ := hbase'
  have : IsSimpleGroup G := hsimple
  have ht1 : t ≠ 1 := by rintro rfl; simp at ht
  have htZ : t ∉ center G := not_mem_center_of_ne_one hnab ht1
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hgs := gsFixedLayer_eq_of_le hJb hJbp hJt
  have hsup := sup_oddIn_pumpUp hJt hgs hT91
  have hPp := isPComponent_pumpUp hS hK hb ht hbt htZ hJb hJbp hJt hT91
  have hR : GSWeakReach J (pumpUp J t) := GSWeakReach.of_gsReach (GSReach.of_gsCorr
    (gsCorr_pumpUp hS hK hb ht hbt htZ hJb hJbp hJt hT91))
  obtain ⟨e⟩ := hmax.2 _ hR
  have htypeP : IsL34Type (pumpUp J t ⧸ Open.fusionZStar (pumpUp J t)) :=
    LieType.CurtisTits.lieModel_of_mulEquiv e htype
  have hperf : ⁅pumpUp J t, pumpUp J t⁆ = pumpUp J t := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hPp
    have h2 : Group.IsPerfect ↥(pumpUp J t) :=
      Group.IsPerfect.ofSurjective
        (f := (subgroupOfEquivOfLe (pumpUp_le_centralizer J t)).toMonoidHom)
        (subgroupOfEquivOfLe (pumpUp_le_centralizer J t)).surjective
    exact (Subgroup.isPerfect_iff (H := pumpUp J t)).mp h2
  have htK : t ∈ coreActionKernel J := by
    refine mem_coreActionKernel.mpr
      ⟨mem_normalizer_of_commute fun l hl => (mem_centralizer_singleton_iff.mp (hJt hl)).symm,
        fun j hj => ?_⟩
    rw [show j⁻¹ * t⁻¹ * j * t = j⁻¹ * t⁻¹ * (j * t) by group,
      mem_centralizer_singleton_iff.mp (hJt hj), show j⁻¹ * t⁻¹ * (t * j) = 1 by group]
    exact one_mem _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q0⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  have hQJ : IsSylowTwoIn ((Q0 : Subgroup ↥J).map J.subtype) J :=
    ⟨map_subtype_le _, Q0, (comap_map_eq_self_of_injective J.subtype_injective _).symm⟩
  have hQP := isSylowTwoIn_of_sup_oddIn hQJ (le_pumpUp hgs) hsup
  have hW1 : ∀ A : Subgroup G, IsEightGroup A → A ≤ pumpUp J t ⊔ zpowers t → wGroup A = ⊥ :=
    fun A hA hAP => wGroup_eq_bot_of_le_sup_zpowers hW hQP (map_subtype_le _) ht2
      (pumpUp_le_centralizer J t) htK hA hAP
  have hGW : GWTwoBalanced G := gwTwoBalanced_of_locallyTwoBalanced hSol hLB
  refine ⟨⟨⟨a, x, J, hT, htype, ht, ⟨htK, hat, hJt⟩, rfl⟩, htypeP,
    hmax.of_weakReach hR, not_oddIn_le_center_pumpUp hsup hperf hbad,
    fun A hA hAor => hAor.elim (hW1 A hA) fun hAK => ?_⟩, hsup⟩
  exact wGroup_eq_bot_of_le_coreActionKernel hGW (three_le_pRank_of_l34 htypeP)
    (fun B hBP hB => hW1 B hB (hBP.trans le_sup_left)) hA hAK

theorem exists_isL34Family_of_component
    (hS : SchreierFor Blueprint.Catalog) (hSol : SolomonCommutingCoreInput)
    (hMax : MaximalTwoComponentInput) (hbase : L34BaseSetting G) {a x : G} {J S : Subgroup G}
    (hT : GSUnbalancingTriple a x J) (htype : IsL34Type (J ⧸ Open.fusionZStar J))
    (hmax : GSWeakMaximalComponent J) (hSyl : IsSylowTwoIn S (normalizer (J : Set G)))
    (hcent : ∀ s ∈ S, s * a = a * s)
    (hns : IsStandardSubgroup J → oddIn J ≤ (center ↥J).map J.subtype → False)
    (hW : ∀ A : Subgroup G, A ≤ withKernel J → IsEightGroup A → wGroup A = ⊥) :
    ∃ t : G, J ≤ centralizer ({t} : Set G) ∧ IsL34Family (pumpUp J t) t ∧
      J ⊔ oddIn (pumpUp J t) = pumpUp J t := by
  obtain ⟨b, t, hb, hJb, hJbp, ht, hbt, hJt, hbad⟩ :=
    exists_pumpUp_not_oddIn_le_center hS hMax hbase hT htype hmax hns
  obtain ⟨hsF, hnF, hoF⟩ := fstar_facts hbase
  have : IsSimpleGroup G := hbase.1
  have hT91 := (hMax G hsF hnF hoF hbase.2.2.1 J hmax
    (by have := three_le_pRank_of_l34 htype; omega) (Sol78.not_psp4_of_l34 htype)
    (Or.inl ⟨htype, hbase⟩)
    t ht hJt).1
  obtain ⟨a', x', hT', hat'⟩ := exists_unbalancing_commute_of_sylow hT hSyl hcent ht hJt
  exact ⟨t, hJt, isL34Family_pumpUp_of_bad hS hSol hbase hT' htype hmax hb hJb hJbp ht hbt
    hJt hat' hT91 hbad hW⟩

theorem l34Prop51Five_of_inputs
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hSol : SolomonCommutingCoreInput) (hMax : MaximalTwoComponentInput)
    (hStd : GSThmB.L34StandardInput) (h41 : L34Prop41) : L34Prop51Five := by
  rintro G _ _ hbase ⟨a, x, J, S, hset, hcent, hZ⟩
  have hset' := hset
  obtain ⟨-, hT, htype, hmax, hSyl, -, -⟩ := hset'
  obtain ⟨t, -, hfam, -⟩ := exists_isL34Family_of_component hS hSol hMax hbase hT htype hmax
    hSyl hcent (not_isStandardSubgroup_of_l34 hU hStd hbase htype) fun A hA hA8 =>
      h41 G a x J S hset hcent hZ A hA hA8
  exact ⟨_, t, hfam⟩

end CFSG.ComponentClassification.GrSLit.GrS5
