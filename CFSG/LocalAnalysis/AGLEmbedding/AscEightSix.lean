module

public import CFSG.LocalAnalysis.AGLEmbedding.AscTenThree
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFiveAux
public import CFSG.CGT.PushingUpLit.BHS.BlockStatements
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSixBlock
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSixOdd
import CFSG.CGT.PushingUpLit.Glue.BlockInX
import CFSG.CGT.PushingUp.PartTwo
public import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridgeAux

public section

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace CFSG.AGLEmbedding

namespace AscEightSix

open AscEightFive CFSG.CGT.PushingUpLit.BHS

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem barM_le_normalizer_of_odd (hyp : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    {x : G} (hxL : x ∈ L) (hxS : x ∈ Subgroup.normalizer (S : Set G)) (hx : Odd (orderOf x))
    (hxQ : ¬ ⁅Subgroup.zpowers x, L⁆ ≤ pCoreOf 2 X) :
    barM X S ≤ Subgroup.normalizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hmk
  set L₀ : Subgroup ↥X := (barM X L).comap mk with hL₀
  have hNL : CFSG.pCore 2 ↥X ≤ L₀ := by
    intro y hy
    show mk y ∈ barM X L
    rw [hmk, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).mpr hy]
    exact one_mem _
  have hmap : L₀.map mk = barM X L :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hcomp : IsComponentOf (L₀.map mk) ⊤ := by rw [hmap]; exact hL.component
  have hS' : IsPGroup 2 ↥(S.subgroupOf X) := hyp.twoRadical.isPGroup.comap_subtype
  set x' : ↥X := ⟨x, hL.le hxL⟩ with hx'
  have hxL' : x' ∈ L₀ := ⟨x', hxL, rfl⟩
  have hxS' : x' ∈ Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := (Subgroup.mem_normalizer_iff.mp hxS) (y : G)
    simpa [x'] using this
  have hxo : Odd (orderOf x') := by rw [← Subgroup.orderOf_coe]; exact hx
  have hxN : ¬ ⁅Subgroup.zpowers x', L₀⁆ ≤ CFSG.pCore 2 ↥X := by
    intro h
    apply hxQ
    have h1 : ⁅Subgroup.zpowers x', L.subgroupOf X⁆ ≤ CFSG.pCore 2 ↥X :=
      (Subgroup.commutator_mono le_rfl
        (fun y hy => show mk y ∈ barM X L from ⟨y, hy, rfl⟩)).trans h
    have h2 := Subgroup.map_mono (f := X.subtype) h1
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le hL.le] at h2
    refine h2.trans ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  have key := le_normalizer_of_component_quotient hNL hcomp hS' hxL' hxS' hxo hxN
  have h3 : barM X S ≤ (Subgroup.normalizer (L₀ : Set ↥X)).map mk := Subgroup.map_mono key
  exact h3.trans ((Subgroup.le_normalizer_map mk).trans (by rw [hmap]))

theorem dBar_le_normalizer (hL : IsTwoPrimeComponent X L) :
    dBar X S L ≤ Subgroup.normalizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  have hLmem : barM X L ∈ orbitFS X S L := by
    refine mem_orbitFS.mpr ⟨1, one_mem _, ?_⟩
    ext x
    simp
  refine iSup₂_le fun A hA => ?_
  by_cases hAL : A = barM X L
  · rw [hAL]; exact Subgroup.le_normalizer
  · intro a ha
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro b hb
    exact (commute_of_mem_orbitFS hL hA hLmem hAL a ha b hb).symm

theorem barM_le_normalizer_of_conj (hL : IsTwoPrimeComponent X L) {g : ↥X ⧸ CFSG.pCore 2 ↥X}
    (hg : g ∈ hBar X S L)
    (h : barM X S ≤ Subgroup.normalizer
      ((barM X L).map (MulAut.conj g).toMonoidHom : Set (↥X ⧸ CFSG.pCore 2 ↥X))) :
    barM X S ≤ Subgroup.normalizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  have hN := barM_le_normalizer_dBar (X := X) (S := S) (L := L)
  have hg' : g ∈ ((barM X S ⊔ dBar X S L : Subgroup _) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
    rw [sup_comm]; exact hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hg'
  obtain ⟨s, hs, d, hd, rfl⟩ := hg'
  have hdN := Subgroup.mem_normalizer_iff.mp (dBar_le_normalizer (S := S) hL hd)
  intro t ht
  have ht' : s * t * s⁻¹ ∈ barM X S :=
    (barM X S).mul_mem ((barM X S).mul_mem hs ht) ((barM X S).inv_mem hs)
  have h1 := Subgroup.mem_normalizer_iff.mp (h ht')
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have e1 : y ∈ barM X L ↔ d⁻¹ * y * d ∈ barM X L := by
    have := hdN (d⁻¹ * y * d)
    rw [show d * (d⁻¹ * y * d) * d⁻¹ = y by group] at this
    exact this.symm
  have e2 : t * y * t⁻¹ ∈ barM X L ↔ d⁻¹ * (t * y * t⁻¹) * d ∈ barM X L := by
    have := hdN (d⁻¹ * (t * y * t⁻¹) * d)
    rw [show d * (d⁻¹ * (t * y * t⁻¹) * d) * d⁻¹ = t * y * t⁻¹ by group] at this
    exact this.symm
  have h2 := h1 (s * y * s⁻¹)
  rw [CFSG.CGT.PushingUp.mem_map_conj_iff, CFSG.CGT.PushingUp.mem_map_conj_iff] at h2
  rw [show (s * d)⁻¹ * (s * y * s⁻¹) * (s * d) = d⁻¹ * y * d by group,
    show (s * d)⁻¹ * (s * t * s⁻¹ * (s * y * s⁻¹) * (s * t * s⁻¹)⁻¹) * (s * d) =
      d⁻¹ * (t * y * t⁻¹) * d by group] at h2
  rw [e1, e2]
  exact h2

omit [Finite G] in
theorem inf_twoCore_le_twoCore {M J : Subgroup G} (hJM : J ≤ M) :
    J ⊓ pCoreOf 2 M ≤ pCoreOf 2 J :=
  CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (J ⊓ pCoreOf 2 M) J inf_le_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun _j hj =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hj,
        CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M (hJM hj)⟩)
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M).to_le inf_le_right)

theorem isSylowTwoOf_inf_of_isSubnormal_of_isSylowTwoOf {T H K : Subgroup G}
    (h : CFSG.Open.IsSubnormal K H) : IsSylowTwoOf T H → IsSylowTwoOf (T ⊓ K) K := by
  induction h with
  | refl K =>
    intro hT
    rwa [inf_eq_left.mpr hT.1]
  | @step K M H' hKM hN _ ih =>
    intro hT
    have h1 := ih hT
    have hnorm : M ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hN
    have h2 := CFSG.Quasithin.A4.isSylowTwoOf_inf_normal h1 hKM hnorm
    rwa [inf_assoc, inf_eq_right.mpr hKM] at h2

theorem barM_le_normalizer_of_isSylowTwoOf (hBHS : BHSLocalCStar) (hyp : Asc81bHyp X S)
    (hL : IsTwoPrimeComponent X L) (hsyl : IsSylowTwoOf (S ⊓ L) L) :
    barM X S ≤ Subgroup.normalizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  have hHX : hGrp5 X S L ≤ X := hGrp5_le
  have hSH : IsSylowTwoOf S (hGrp5 X S L) := isSylowTwoOf_hGrp5 hyp hL hsyl
  have hch : CharTwo (hGrp5 X S L) := charTwo_of_le hyp twoCore_le_hGrp5 hHX
  obtain ⟨E, hB, hEsO, hEM, he⟩ := exists_block_not_le_mGrp5 hBHS hyp hL hsyl
  have hEH : E ≤ hGrp5 X S L := hB.le
  have hEs : (E.subgroupOf (hGrp5 X S L)).IsSubnormal :=
    NoXBlock.isSubnormal_subgroupOf_of_open hEsO
  have hEch : CharTwo E := CharTwo.of_isSubnormal hch hEH hEs
  have hshort : IsShort2 E := (LocalCGT.inClassXBlock_of_inClassX
    (CFSG.CGT.PushingUpLit.Glue.inClassX_of_isBTBlock hB hEch)).1
  have hEN : ¬ E ≤ nGrp5 X S L := fun h => hEM (h.trans le_sup_left)
  obtain ⟨g, hgH, hEeq⟩ := eq_conj_of_short hL hEH hEs hshort hEN
  have hL' : IsTwoPrimeComponent X (L.map (MulAut.conj (g : G)).toMonoidHom) :=
    IsTwoPrimeComponent.map_conj g.2 hL
  have hEp : ⁅E, E⁆ = E := by rw [hEeq]; exact hL'.perfect
  have hSE : IsSylowTwoOf (S ⊓ E) E := isSylowTwoOf_inf_of_isSubnormal_of_isSylowTwoOf hEsO hSH
  obtain ⟨x, hxC, hxodd, hxQ⟩ : ∃ x : ↥E, (x : G) ∈ cStarIn (hGrp5 X S L) S ∧
      Odd (orderOf x) ∧ ¬ ⁅Subgroup.zpowers (x : G), E⁆ ≤ pCoreOf 2 E := by
    rcases he with ⟨⟨n, hn, hnat⟩, hCeq⟩ | ⟨m, hm, hnat, ⟨ι⟩⟩
    · obtain ⟨x, hxN, hxodd, hxQ⟩ := exists_odd_of_sl hSE hn hnat
      refine ⟨x, ?_, hxodd, hxQ⟩
      have : (x : G) ∈ cStarIn (hGrp5 X S L) S ⊓ E := hCeq ▸ ⟨hxN, x.2⟩
      exact this.1
    · rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · obtain rfl : m = 1 := by omega
        exact (false_of_alt_one hEp hnat).elim
      · exact exists_odd_of_alt hm2 hnat ι
  have hxK : (x : G) ∈ Subgroup.normalizer (S : Set G) :=
    ((cStarIn_le_normalizer hyp hHX) hxC).2
  have hxQ' : ¬ ⁅Subgroup.zpowers (x : G), L.map (MulAut.conj (g : G)).toMonoidHom⁆ ≤
      pCoreOf 2 X := by
    rw [← hEeq]
    intro h
    apply hxQ
    refine (le_inf ?_ h).trans (inf_twoCore_le_twoCore (hEH.trans hHX))
    exact (Subgroup.commutator_mono ((Subgroup.zpowers_le).mpr x.2) le_rfl).trans hEp.le
  have hxL' : (x : G) ∈ L.map (MulAut.conj (g : G)).toMonoidHom := hEeq ▸ x.2
  have hxo : Odd (orderOf (x : G)) := by rw [Subgroup.orderOf_coe]; exact hxodd
  have h1 := barM_le_normalizer_of_odd hyp hL' hxL' hxK hxo hxQ'
  rw [barM_map_conj g.2 L] at h1
  exact barM_le_normalizer_of_conj hL hgH h1

end AscEightSix

theorem asc81bEightSix_of_tenThree (hBHS : CFSG.CGT.PushingUpLit.BHS.BHSLocalCStar)
    : Asc81bEightSix := by
  have h103 := CFSG.AGLEmbedding.asc81bTenThree
  intro G _ _ X S hK hyp Lbar hLbar
  obtain ⟨L, hL, rfl⟩ := exists_isTwoPrimeComponent hLbar
  rcases h103 G X S L hK hyp hL with hsyl | hN
  · exact AscEightSix.barM_le_normalizer_of_isSylowTwoOf hBHS hyp hL hsyl
  · exact barM_le_normalizer_barM hN

theorem asc81bEightSix_of_bhs (hBHS : CFSG.CGT.PushingUpLit.BHS.BHSLocalCStar) :
    Asc81bEightSix :=
  asc81bEightSix_of_tenThree hBHS

end CFSG.AGLEmbedding
