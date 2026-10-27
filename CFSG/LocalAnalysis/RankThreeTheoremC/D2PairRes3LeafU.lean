module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Leaf
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6ResidueU
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2IndexCases3U
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Two
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Abel
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3L28
import CFSG.LocalAnalysis.AGLEmbeddingD2.SeitzLTwoEight

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D2PairStrongThree3CompU (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ (P : Sylow 3 G) (A H R : Subgroup G), 3 ∈ rankThreeSigmaA G →
    IsCoreMaxLocal 3 P M → D2Escape 3 P M A H R → AGLPair 3 M H R →
    rankThreeGamma 1 3 (P : Subgroup G) ≤ M → D2PerfectThreePrime H M →
    (IsElemAbelian 3 R → Nat.card R = 9 →
      IrreducibleOn (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R) →
    ((∀ x ∈ R, ∀ y ∈ R, x * y = y * x) → IsElemAbelian 3 R ∧ Nat.card R = 9) → False

variable {G : Type} [Group G] [Finite G]

theorem d2PairStrongThree3CompU_of_residue (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hX : D1NoXBlock3 G)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hout : KFactBlockOuterThree) (hK3 : KFactBlockPLElem)
    (hE9 : KFactBlockE9Transitive) (hA : D2PairA6Residue3U G) : D2PairStrongThree3CompU G := by
  intro hS hD1 M hM ha hb P A H R hp hMP hesc hpr hstr hperf hirr0 hab
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  have hNX : NoXBlockFor G := noXBlockFor_of_setting hX hS
  have hH : Open.pRank 3 H = 2 := hesc.pRank_H
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hMP
  have hM3 : 3 ≤ Open.pRank 3 M :=
    hP3.symm.le.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hPM)
  have hM3' : Open.pRank 3 M ≤ 3 := by
    have h1 := local_pRank_le_evenRank 3 h3 (by norm_num) M hesc.maxTwoLocal_M.1
    rw [hS.rank] at h1
    exact h1
  set S := pCoreOf 2 H with hSdef
  have hthree : ∀ L : Subgroup G, IsWeakSBlock M S L → BlockHasThree M S L := fun L hL =>
    hpr.blockHasThree h85 h86 h93 hNX hK2 hC3 hK5 hL
  have hsolvL : ∀ L : Subgroup G, IsWeakSBlock M S L → BlockPLThreeSolv M S L := fun L hL =>
    blockPLThreeSolv_of_perfectThreePrime hpr hperf hL
  have hnotX : ∀ L : Subgroup G, IsWeakSBlock M S L → ¬ InClassXBlock L := fun L hL hX' =>
    hNX M L hpr.maxTwoLocal_M hL.le hL.subnormal hX'
  have hnsyl : ∀ L : Subgroup G, IsWeakSBlock M S L → ¬ IsSylowTwoOf (S ⊓ L) L := fun L hL =>
    hpr.not_isSylowTwoOf_inf h85 hNX hL
  have hdat := fun (L : Subgroup G) (hL : IsWeakSBlock M S L) =>
    hout G M S L hpr.isKGroup.1 hpr.asc81bHyp hpr.twoCore_M_le hL (hnotX L hL) (hnsyl L hL)
      (hsolvL L hL) hM3'
  have hy : ∀ L : Subgroup G, IsWeakSBlock M S L →
      ∃ y ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L), y ^ 3 = 1 ∧
        y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro L hL
    by_cases hZ : 3 ∣ Nat.card (barM M L ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)
    · exact (hdat L hL).2 hZ
    · exact exists_order_three_noncentral hL.le (hthree L hL) hZ
  by_cases hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x
  swap
  · exact absurd (commutative_of_barM_commutative h3 (by norm_num) hpr.le_M hpr.isPGroup_R
      (hpr.commutative_barM h84 h86 hNX hH hM3' hthree (fun L hL => (hdat L hL).1) hy
        (fun L hL T hT hT3 => hK3 G M S L hpr.isKGroup.1 hpr.asc81bHyp hpr.twoCore_M_le hL
          (hnotX L hL) (hnsyl L hL) (h93 G M S L hpr.isKGroup.1 hpr.asc81bHyp hL) (hsolvL L hL)
          hM3' T hT hT3))) hcomm
  obtain ⟨hRel, hR9⟩ := hab hcomm
  have hirr := hirr0 hRel hR9
  obtain ⟨L, hL, hk1, hr3, hRL, hker⟩ := hpr.exists_survivor_of_irreducible h84 h86 hNX hH hM3
    hM3' hthree (fun L' hL' => (hdat L' hL').1) hy hRel hR9 hirr
  by_cases htrans : TransitiveOnNonidentity (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R
  swap
  · exact hA hS hD1 M hM ha hb P A H R hp hMP hesc hpr hstr hperf hRel hR9 hirr htrans L hL
      hk1 hr3 hRL hker
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set Bb := barM M (Subgroup.normalizer (S : Set G)) with hBb
  have hBH : Open.pRank 3 Bb ≤ 2 :=
    (hpr.pRank_barM_normalizer_le h3 (by decide)).trans hH.le
  have hCB : Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Bb := fun c hc =>
    hpr.mem_barM_normalizer_of_centralizes_weakSBlocks h84 h86 hNX fun L' hL' =>
      (hk1 L' hL').symm ▸ hc
  have hRB : barM M R ≤ Bb := barM_mono fun r hr => by
    rw [hpr.normalizer_twoCore_H]
    exact hpr.le_H hr
  have hRbarcard : Nat.card (barM M R) = 9 := by
    rw [hpr.card_barM_of_isPGroup hpr.le_M hpr.isPGroup_R, hR9]
  refine hE9 G M S L hpr.isKGroup.1 hpr.asc81bHyp hpr.twoCore_M_le hL (hnotX L hL) (hnsyl L hL)
    (hsolvL L hL) hM3'
    hr3 hBH hCB (barM M R) (CFSG.AGLEmbeddingD2.isElemAbelian_barM hRel) hRbarcard hRB hRL hker ?_
  intro x hx y hy hx1 hy1
  obtain ⟨r₁, hr₁R, rfl⟩ := mem_barM_iff.mp hx
  obtain ⟨r₂, hr₂R, rfl⟩ := mem_barM_iff.mp hy
  have hr₁1 : (r₁ : G) ≠ 1 := fun h1 => hx1 (by
    have : r₁ = 1 := Subtype.ext h1
    rw [this, map_one])
  have hr₂1 : (r₂ : G) ≠ 1 := fun h1 => hy1 (by
    have : r₂ = 1 := Subtype.ext h1
    rw [this, map_one])
  obtain ⟨n, hn, hnr⟩ := htrans _ hr₁R _ hr₂R hr₁1 hr₂1
  have hnM : n ∈ M := hn.1.2
  have hnS : n ∈ Subgroup.normalizer (S : Set G) := by
    rw [hpr.normalizer_twoCore_H]
    exact hn.1.1
  refine ⟨mk ⟨n, hnM⟩, ⟨⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hnS), ?_⟩, ?_⟩, ?_⟩
  ·
    have hw := ‹IsWeakSBlock M S L›.map_conj hnM hnS
    have he := hk1 _ hw
    rw [barM_map_conj hnM] at he
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr he
  ·
    have hmapR : R.map (MulAut.conj n).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hn.2
    have := barM_map_conj hnM R
    rw [hmapR] at this
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr this.symm
  · have e : mk ⟨n, hnM⟩ * mk r₁ * (mk ⟨n, hnM⟩)⁻¹ = mk ⟨n * r₁ * n⁻¹, M.mul_mem
        (M.mul_mem hnM r₁.2) (M.inv_mem hnM)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    have : (⟨n * r₁ * n⁻¹, M.mul_mem (M.mul_mem hnM r₁.2) (M.inv_mem hnM)⟩ : ↥M) = r₂ :=
      Subtype.ext hnr
    rw [this]

theorem d2IndexCaseStrongAt3U_of_pairStrongCompU {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (hPp : ∀ p, Pp p → p = 3) (hpair : D2PairAt i Pp) (hsolv : D2SolvableAt i Pp)
    (hauto : D2AutomizerAt i Pp) (hnine : D2SylowNineAt i Pp) (h : D2PairStrongThree3CompU G) :
    D2IndexCaseStrongAt3U G i Pp := by
  intro hS hD1 M hM ha hb p hp hpp P A H R hMP hesc hstr Rbar K hRbar hK he
  obtain rfl := hPp p hpp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpr : AGLPair 3 M H R := hesc.toPair (aglGlobal_of_setting hS)
    (hesc.twoCore_inf_eq_of_primeCore_inf_eq (hesc.primeCore_inf_eq_iff.mpr
      (hpair _ 3 hpp Rbar _ _ K hK he)))
  have hirr : IsElemAbelian 3 R → Nat.card R = 9 →
      IrreducibleOn (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R := by
    intro _ hR9
    refine hesc.irreducibleOn_of_automizer hR9 ?_
    have := hauto _ 3 hpp Rbar _ _ K hK he
    rwa [hRbar] at this
  exact h hS hD1 M hM ha hb P A H R hp hMP hesc hpr hstr
    (d2PerfectThreePrime_of_isSolvable (hsolv _ 3 hpp Rbar _ _ K hK he)) hirr
    fun _ => hesc.elemNine_of_card hRbar hK (hnine _ 3 hpp Rbar _ _ K hK he)

theorem d2U3ThreeStrong3U_of_pairStrongCompU (h : D2PairStrongThree3CompU G) :
    D2U3ThreeStrong3U G := by
  intro d hd hS hD1 M hM ha hb p hp hpp P A H R hMP hesc hstr Rbar K hRbar hK ⟨e⟩
  obtain ⟨hpc, rfl⟩ := hpp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdu, hnu⟩ := isUnitaryIndex_of_case hpc hd
  have hdata := hesc.heisData_of_u3 unitaryBorelKFacts
    (aglGlobal_of_setting hS) hRbar hK hdu hnu e
  exact h hS hD1 M hM ha hb P A H R hp hMP hesc hdata.pair hstr
    (d2PerfectThreePrime_of_le hdata.perfect_le)
    (fun _ h9 => absurd (hdata.card_R.symm.trans h9) (by norm_num)) fun hcomm => by
      exfalso
      obtain ⟨hZ, hRR, -⟩ := hdata.heis
      have hbot : ⁅R, R⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx =>
        Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx
      rw [hbot] at hRR
      rw [← hRR, Subgroup.card_bot] at hZ
      omega

theorem d2L28Strong3U_of_pairStrongCompU (hSch : KFactCatalogSchreier)
    (hK4 : KFactSylowThreeAbelian) (h : D2PairStrongThree3CompU G)
    (d : TauCeti.ValidLieTypeIndex) :
    D2IndexCaseStrongAt3U G (.lie d) fun p => IsD2SeitzLTwoEight p d.1 := by
  intro hS hD1 M hM ha hb p hp hpp P A H R hMP hesc hstr Rbar K hRbar hK he
  have hU := d2PairAt_l28 d _ p hpp Rbar _ _ K hK he
  obtain ⟨hp3, q, hq2, hq3, hdq⟩ := hpp
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := he
  obtain ⟨e'⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 2) (n := 3) (d := d)
    ⟨q, hdq, hq2, hq3⟩
  have hpr : AGLPair 3 M H R := hesc.toPair (aglGlobal_of_setting hS)
    (hesc.twoCore_inf_eq_of_primeCore_inf_eq (hesc.primeCore_inf_eq_iff.mpr hU))
  refine h hS hD1 M hM ha hb P A H R hp hMP hesc hpr hstr
    (d2PerfectThreePrime_of_perfect_eq_bot
      (hK.perfect_eq_bot_of_isSolvable_inf hSch (hK.isSolvable_inf_of_psl28 (e.trans e'))))
    (fun hel _ => ?_)
    (hesc.elemNine_of_abelian hRbar hK
      (hK4.2 _ K Rbar hK.normal hK.centralizer_eq_bot ⟨e.trans e'⟩))
  exfalso
  have hel' : IsElemAbelian 3 (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [hRbar]
    exact isElemAbelian_map_subgroupOf hel _
  exact not_isElemAbelian_of_psl28 Rbar (e.trans e') hel'

end CFSG.LocalAnalysis.RankThreeTheoremC
