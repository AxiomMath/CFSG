module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePPrime
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeAltSix
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeBlocks
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeComp
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeCube
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeSection
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools
import CFSG.LocalAnalysis.ComponentInitial.GroupComponents
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeSplit

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem exists_mul_pow_mem_of_blockThreeIb {Y : Type*} [Group Y] [Finite Y]
    [Fact (Nat.Prime 3)] {L B E X D : Subgroup Y} (hEp : IsPGroup 3 E) (hEc : IsMulCommutative E)
    (hE3 : 3 ≤ CFSG.Open.pRank 3 E) (hB : CFSG.Open.pRank 3 B ≤ 3) (hEB : E ≤ B)
    (hEL : E ≤ Subgroup.normalizer (L : Set Y))
    (hcopL : ∀ w ∈ L, w ∈ Subgroup.centralizer (L : Set Y) → w ^ 3 = 1 → w = 1)
    (hcen : ∀ y ∈ L, y ^ 3 = 1 → y ∈ Subgroup.centralizer (D : Set Y) →
      y ∈ D ⊔ Subgroup.centralizer (L : Set Y) → y ∈ Subgroup.centralizer (L : Set Y))
    {z : Y} (hzE : z ∈ E) (hzp : z ^ 3 = 1) (hzL : z ∉ Subgroup.centralizer (L : Set Y))
    (hzD : z ∈ D) (hXD : X ≤ Subgroup.centralizer (D : Set Y))
    (hEz : ∀ e ∈ E, ∃ x ∈ X, ∃ m : ℕ, e = x * z ^ m)
    {j : Y} (hj : j ∈ L ⊓ B) (hzj : z * j⁻¹ ∈ Subgroup.centralizer (L : Set Y)) :
    ∃ x ∈ X, ∃ a : ℕ, ¬ 3 ∣ a ∧ x * z ^ a ∈ L := by
  obtain ⟨y, hyE, hyL, hy1, hy3, k, hyk⟩ := exists_pElem_inf_component_pow hEp hEc hE3 hB hEB
    hEL (fun w hw => hcopL w hw.1) hzE hzp hzL hj hzj
  obtain ⟨x, hx, m, rfl⟩ := hEz y hyE
  refine ⟨x, hx, m, fun h3m => hy1 ?_, hyL⟩
  obtain ⟨c, rfl⟩ := h3m
  have hzm : z ^ (3 * c) = 1 := by rw [pow_mul, hzp, one_pow]
  rw [hzm, mul_one] at hyL hy3 hyk ⊢
  have hxC : x ∈ Subgroup.centralizer (L : Set Y) := by
    refine hcen x hyL hy3 (hXD hx) ?_
    have hxe : x = (x * (z ^ k)⁻¹) * z ^ k := by group
    rw [hxe]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hyk)
      (Subgroup.mem_sup_left (D.pow_mem hzD k))
  exact hcopL x hyL hxC hy3

theorem D1OneSmallData.le_centralizer_block_of_unitary (hSTO : KFactSmallThreeOrders)
    (hShp : KFactSmallSylowShape) (hBA : KFactBlockCentAbThreeIb)
    (hd : D1OneSmallData 3 P M H R Rbar K) {z : G} (hz : D1SmallCZElt 3 H R K z)
    (hU : IsSmallUnitary 3 K) {T : Sylow 3 K}
    (hT : (T : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K)
    {S L : Subgroup G} {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {x : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hBL : BlockThreeIbHyp M S L D x)
    (hXbN : barM M (d1LiftX 3 H R K) ≤
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hXbP : barM M (d1LiftX 3 H R K) ≤
      Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hXD : barM M (d1LiftX 3 H R K) ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hXbp : IsPGroup 3 (barM M (d1LiftX 3 H R K))) :
    barM M (d1LiftX 3 H R K ⊓ Subgroup.centralizer (d1LiftX 3 H R K : Set G)) ≤
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set X := d1LiftX 3 H R K with hXdef
  have hXM : X ≤ M := (d1LiftX_le 3 H R K).trans hd.cfg.ext.le_M
  have hZX := D1OneSmallData.centerOf_le_commutator_of_cube hShp hd hz
    (card_rbar_inf_of_unitary hSTO hU T hT)
  have hcomm := hBA G M S L D x hBL (barM M X) hXbN hXbP hXD hXbp
  have hle : ⁅X, X⁆ ≤ ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
      mk).map M.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, hXM ha⟩ : M), ⟨b, hXM hb⟩⁆, ?_, ?_⟩
    · show mk ⁅(⟨a, hXM ha⟩ : M), ⟨b, hXM hb⟩⁆ ∈
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact hcomm _ ⟨⟨a, hXM ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩ _
        ⟨⟨b, hXM hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    · rfl
  rintro _ ⟨⟨w, hwM⟩, hw, rfl⟩
  obtain ⟨w', hw', hw'w⟩ := hle (hZX (Subgroup.mem_subgroupOf.mp hw))
  have : w' = ⟨w, hwM⟩ := Subtype.ext hw'w
  rw [← this]
  exact hw'

theorem D1OneSmallData.le_centralizer_blocks_of_altSix (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hSch : KFactCatalogSchreier)
    (hBR : KFactBlockCentRankIbThree) (hBC : KFactBlockCenterThreeIb)
    (h3 : D1PhaseThree 3 P M H R) (hd : D1OneSmallData 3 P M H R Rbar K) (hA6 : IsAltTwoP 3 K)
    {z : G} (hz : D1SmallCZElt 3 H R K z) (hzM : z ∈ M)
    (hOp : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (hXL : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      d1LiftX 3 H R K ≤ Subgroup.normalizer (L : Set G))
    (hXexp : ∀ x ∈ d1LiftX 3 H R K, x ^ 3 = 1)
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hDp : ⁅D, D⁆ = D) (hDK : D ≤ barM M (H ⊓ M))
    (hXD : barM M (d1LiftX 3 H R K) ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hzD : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈ D)
    (hBL : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      D ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      BlockThreeIbHyp M (pCoreOf 2 H) L D (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩)) :
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M (d1LiftX 3 H R K) ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨-, hzo, hzH, -⟩ := id hz
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set zb := mk ⟨z, hzM⟩ with hzb
  set X := d1LiftX 3 H R K with hXdef
  set Xb := barM M X with hXb
  have hXz : X ≤ Subgroup.centralizer ({z} : Set G) := hd.d1LiftX_le_centralizer hz
  have hXH : X ≤ H := d1LiftX_le_H 3 H R K
  have hXM : X ≤ M := (d1LiftX_le 3 H R K).trans hd.cfg.ext.le_M
  have hNSH : Subgroup.normalizer (S : Set G) = H := h3.normalizer_twoCore_H
  have hXNS : X ≤ Subgroup.normalizer (S : Set G) := by rw [hNSH]; exact hXH
  have hXbN : ∀ L' : Subgroup G, IsWeakSBlock M S L' →
      Xb ≤ Subgroup.normalizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L' hL' =>
    barM_le_normalizer_barM (hXL L' hL')
  have hXbP : ∀ L' : Subgroup G, IsWeakSBlock M S L' →
      Xb ≤ Subgroup.normalizer (blockPL M S L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L' hL' =>
    barM_le_normalizer_barM fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hXNS hx), hXL L' hL' hx⟩
  obtain ⟨t, htK, htz, hcop, htX, hline, hinv, hX9⟩ :=
    D1OneSmallData.exists_torus_altSix_period h3 hd hA6 hz
  have htM : t ∈ M := htK.2
  set tb := mk ⟨t, htM⟩ with htb
  have htXb := mem_normalizer_barM htM htX
  have hlineb := not_mem_normalizer_line_barM hXexp htM htX hline
  have hXcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    have h1 := hinv (x * y) (X.mul_mem hx hy)
    have h2 : t ^ 2 * (x * y) * (t ^ 2)⁻¹ =
        (t ^ 2 * x * (t ^ 2)⁻¹) * (t ^ 2 * y * (t ^ 2)⁻¹) := by group
    rw [h2, hinv x hx, hinv y hy, mul_inv_rev] at h1
    have h3' := congrArg Inv.inv h1
    simp only [mul_inv_rev, inv_inv] at h3'
    exact h3'.symm
  have hXel : IsElemAbelian 3 X := ⟨⟨⟨fun a b => Subtype.ext (hXcomm a a.2 b b.2)⟩⟩, hXexp⟩
  have hXbel : IsElemAbelian 3 Xb := isElemAbelian_barM_of hXel
  have hXbcard : Nat.card Xb = 9 := (card_barM_of_elem hp3 (by norm_num) hXM hXel).trans hX9
  have hzbp : zb ^ 3 = 1 := by
    rw [hzb, ← map_pow]
    have : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [this, map_one]
  have hXbz : Xb ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨x, hxM⟩, hxX, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hzb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (hXz (Subgroup.mem_subgroupOf.mp hxX)))
  have hzbC : zb ∈ Subgroup.centralizer (Xb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    CFSG.LocalAnalysis.ComponentInitial.mem_centralizer_of_le_centralizer_singleton hXbz
  have hzbX : zb ∉ Xb :=
    mk_not_mem_barM_of_commute hp3 (by norm_num) hXexp hzM hz3 (hd.d1LiftX_facts hz).1 hXz
  have hzb1 : zb ≠ 1 := fun h => hzbX (h ▸ Xb.one_mem)
  have hzbord : orderOf zb = 3 := orderOf_eq_prime hzbp hzb1
  set E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := Xb ⊔ Subgroup.zpowers zb with hE
  have hEel : IsElemAbelian 3 E := isElemAbelian_sup_zpowers_of_le_centralizer hXbel hXbz hzbp
  have hEp : IsPGroup 3 E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hEel.2 e e.2)⟩
  have hX2 : 2 ≤ CFSG.Open.pRank 3 Xb :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 hp3 Xb)
      ⟨Xb, le_rfl, hXbel, by rw [hXbcard]; norm_num⟩
  have hE3 : 3 ≤ CFSG.Open.pRank 3 E :=
    hX2.trans_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (CFSG.AGLEmbeddingD2.pRank_succ_le_sup_zpowers Xb hzbp hzb1 hzbC
        (zpowers_inf_eq_bot_of_not_mem' hp3 hzbord hzbX)))
  have hr : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3 := hd.pRank_le_three_of_le_H inf_le_left
  have hB : CFSG.Open.pRank 3 (barM M (H ⊓ M)) ≤ 3 :=
    (pRank_barM_le hp3 (by norm_num) M (H ⊓ M) inf_le_right).trans hr
  have hEB : E ≤ barM M (H ⊓ M) := sup_le (barM_mono (le_inf hXH hXM))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
      (show z ∈ H ⊓ M from ⟨hzH, hzM⟩))))
  have hinvb : ∀ x ∈ Xb, tb ^ 2 * x * (tb ^ 2)⁻¹ = x⁻¹ := by
    rintro _ ⟨⟨x, hxM⟩, hxX, rfl⟩
    have key : (⟨t, htM⟩ : M) ^ 2 * ⟨x, hxM⟩ * ((⟨t, htM⟩ : M) ^ 2)⁻¹ = (⟨x, hxM⟩ : M)⁻¹ :=
      Subtype.ext (by simpa using hinv x (Subgroup.mem_subgroupOf.mp hxX))
    have h := congrArg mk key
    rw [map_mul, map_mul, map_inv, map_inv, map_pow] at h
    rw [htb]
    exact h
  set B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) → Prop :=
    fun Lb => ∃ L' : Subgroup G, IsWeakSBlock M S L' ∧ barM M L' = Lb with hBdef
  have hBt2 : ∀ Lb, B Lb → tb ^ 2 ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨L', hL', rfl⟩
    have h2 := mem_normalizer_barM (M.pow_mem htM 2)
      (D1PhaseThree.sq_mem_normalizer_of_coprime h3 hB3 hr hL' htK hcop)
    have : tb ^ 2 = mk ⟨t ^ 2, M.pow_mem htM 2⟩ := by
      rw [htb, ← map_pow]
      exact congrArg mk (Subtype.ext (by simp))
    rw [this]
    exact h2
  have hBz : ∀ Lb, B Lb → zb ∉ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨L', hL', rfl⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hzC, -⟩ := (hBL L' hL').2
    exact hzC
  have hBy : ∀ Lb, B Lb → ∃ x ∈ Xb, ∃ a : ℕ, ¬ 3 ∣ a ∧ x * zb ^ a ∈ Lb := by
    rintro _ ⟨L', hL', rfl⟩
    have hyp := (hBL L' hL').2
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hzC, -⟩ := id hyp
    obtain ⟨j, hjLB, hjc⟩ :=
      h3.exists_inner_mem_barM h84 h86 hD2 hSch hL' hDp hDK (hBL L' hL').1 hzD
    exact exists_mul_pow_mem_of_blockThreeIb hEp hEel.1 hE3 hB hEB
      (sup_le (hXbN L' hL') (Subgroup.zpowers_le.mpr ((hBL L' hL').1 hzD)))
      (fun w hw hwC hwp => eq_one_of_mem_center_component_of_pCore hOp hL'.component hw hwC hwp)
      (hBC G M S L' D zb hyp) (Subgroup.mem_sup_right (Subgroup.mem_zpowers zb)) hzbp hzC hzD
      hXD (fun e he => exists_mul_pow_of_le_centralizer hXbz he) hjLB hjc
  have hBa : ∀ Lb, B Lb → tb ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      Xb ⊓ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≠ ⊥ := by
    rintro _ ⟨L', hL', rfl⟩ htL
    exact hBR G M S L' D zb (hBL L' hL').2 Xb (hXbN L' hL') (hXbP L' hL') hXD hXbel
      (by rw [hXbcard]; norm_num) tb htL htXb hlineb
  have hmain := le_centralizer_blocks_of_torus (X := Xb) (zb := zb) (t := tb) hXbcard
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hXbz hx)) hzbp htXb
    (by rw [htb, hzb, ← map_mul, ← map_mul]; exact congrArg mk (Subtype.ext htz))
    hlineb hinvb B
    (fun Lb hLb => by
      obtain ⟨L', hL', rfl⟩ := hLb
      exact (CFSG.isComponent_iff_open _).mpr hL'.component)
    hBt2 hBz hBy hBa
  exact fun L hL => hmain _ ⟨L, hL, rfl⟩

theorem d1SmallSPLZeroIbThreeBlocks_of (hUP : KFactUPrimeSmall)
    (hSTO : KFactSmallThreeOrders) (hSE : KFactSmallSylowExp) (hShp : KFactSmallSylowShape)
    (hSch : KFactCatalogSchreier) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hBR : KFactBlockCentRankIbThree)
    (hBA : KFactBlockCentAbThreeIb) (hBC : KFactBlockCenterThreeIb) :
    D1SmallSPLZeroIbThreeBlocks := by
  intro G _ _ P M H R Rbar K hd _ z hz hspl hSP hout _ hnIa hOp hXL L hL
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨hzR, -, -, -⟩ := id hz
  have hzM : z ∈ M := hd.cfg.ext.le_M hzR
  obtain ⟨T, hT, h3, -, -, -⟩ := hd.exists_kFacts_three hUP hSTO hSch hspl
  obtain ⟨D, hDp, hDK, hXD, hzD, hBL⟩ := D1OneSmallData.exists_blockThreeIb hUP hSTO hSch hβ hKO
    hΓ h84 h85 h86 h93 hD2 hK2 hC3' hK5' hd hspl hnIa hz hSP hout hOp hzM
  set S := pCoreOf 2 H with hS
  set X := d1LiftX 3 H R K with hXdef
  obtain ⟨hXexp, -, -⟩ := hd.d1LiftX_three_facts hSE hShp hz
  have hcase : IsAltTwoP 3 K ∨ IsSmallUnitary 3 K := by
    rcases hspl with h | h | ⟨-, h⟩
    · exact Or.inl (isAltTwoP_of_isSmallLinTwo_three h)
    · exact Or.inr h
    · exact Or.inl h
  rcases hcase with hA6 | hU
  · have hB3 : ∀ L' : Subgroup G, IsWeakSBlock M S L' → BlockHasThree M S L' :=
      fun L' hL' => stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3' hK5' h3 hL'
    exact (barM_mono inf_le_left).trans (hd.le_centralizer_blocks_of_altSix h84 h86 hD2 hSch hBR
      hBC h3 hA6 hz hzM hOp hB3 hXL hXexp hDp hDK hXD hzD hBL L hL)
  have hXH : X ≤ H := d1LiftX_le_H 3 H R K
  have hXM : X ≤ M := (d1LiftX_le 3 H R K).trans hd.cfg.ext.le_M
  have hNSH : Subgroup.normalizer (S : Set G) = H := h3.normalizer_twoCore_H
  have hXNS : X ≤ Subgroup.normalizer (S : Set G) := by rw [hNSH]; exact hXH
  have hXbexp : ∀ y ∈ barM M X, y ^ 3 = 1 := by
    rintro _ ⟨⟨x, hxM⟩, hxX, rfl⟩
    rw [← map_pow]
    have : (⟨x, hxM⟩ : M) ^ 3 = 1 :=
      Subtype.ext (by simpa using hXexp x (Subgroup.mem_subgroupOf.mp hxX))
    rw [this, map_one]
  have hXbp : IsPGroup 3 (barM M X) := fun y =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hXbexp y y.2)⟩
  exact hd.le_centralizer_block_of_unitary hSTO hShp hBA hz hU hT (hBL L hL).2
    (barM_le_normalizer_barM (hXL L hL))
    (barM_le_normalizer_barM fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hXNS hx), hXL L hL hx⟩) hXD hXbp

theorem d1SmallSPLZeroIbThreeCore_of_kFacts (hUP : KFactUPrimeSmall)
    (hSTO : KFactSmallThreeOrders) (hSE : KFactSmallSylowExp) (hShp : KFactSmallSylowShape)
    (hSch : KFactCatalogSchreier) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hKS : KFactSPLInvolveScalar)
    (hKP : KFactPPrimeCompInvolutionP) (hBR : KFactBlockCentRankIbThree)
    (hBA : KFactBlockCentAbThreeIb) (hBC : KFactBlockCenterThreeIb) :
    D1SmallSPLZeroIbThreeCore :=
  d1SmallSPLZeroIbThreeCore_of_blocks hβ hKO hΓ hSch hKS hKP
    (d1SmallSPLZeroIbThreeBlocks_of hUP hSTO hSE hShp hSch hβ hKO hΓ h84 h85 h86 h93 hD2 hK2
      hC3' hK5' hBR hBA hBC)

end CFSG.AGLEmbedding
