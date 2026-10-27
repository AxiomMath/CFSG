module

public import CFSG.ClassicalInvolution.Q3.Q3TMFSBasic
public import CFSG.ClassicalInvolution.Q3.Q3B2
public import CFSG.GH74.GLS.Balance.Defs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T.MFS

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Balance
open CFSG.GH74.GLS CFSG.GH74.GLS.Balance CFSG.ComponentClassification CFSG.LocalCores
open scoped MatrixGroups

variable {Y : Type} [Group Y] [Finite Y] {z : Y} {L : Subgroup Y}

theorem mem_oddCore_iff_mem_oddCoreIn (hL : IsClassicalMember3 L z) (x : L) :
    x ∈ classicalInvolutionOddCore L ↔
      (x : Y) ∈ oddCoreIn (Subgroup.centralizer ({z} : Set Y)) := by
  constructor
  · intro hx
    have h1 : (x : Y) ∈ oddCoreIn L := ⟨x, hx, rfl⟩
    exact oddCoreIn_le_of_isSubnormal hL.subnormal h1
  · intro hx
    have hLC : L ≤ Subgroup.centralizer ({z} : Set Y) := isSubnormal_le hL.subnormal
    set S : Subgroup Y := oddCoreIn (Subgroup.centralizer ({z} : Set Y)) ⊓ L with hS
    have hSL : S ≤ L := inf_le_right
    have hodd : Odd (Nat.card S) :=
      (odd_card_oddCoreIn (Subgroup.centralizer ({z} : Set Y))).of_dvd_nat
        (Subgroup.card_dvd_of_le inf_le_left)
    have hnormal : (S.subgroupOf L).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact ⟨conj_mem_oddCoreIn (hLC g.2) hn.1, L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)⟩
    have hsub : IsSubnormal S L := isSubnormal_of_normal_subgroupOf hSL hnormal
    have h2 : S ≤ oddCoreIn L := le_oddCoreIn_of_isSubnormal hsub hodd
    obtain ⟨y, hy, hyx⟩ := h2 ⟨hx, x.2⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy

theorem pPrimeCore_two_eq_componentOddCore (G : Type*) [Group G] :
    pPrimeCore 2 G = componentClassificationOddCore G := by
  unfold CFSG.pPrimeCore componentClassificationOddCore
  congr 1
  ext N
  exact and_congr_right fun _ => Nat.coprime_two_left

omit [Finite Y] in
theorem subgroupOf_oddCoreIn_eq (C : Subgroup Y) :
    (oddCoreIn C).subgroupOf C = pPrimeCore 2 ↥C := by
  have h1 : (oddCoreIn C).subgroupOf C = componentClassificationOddCore ↥C :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  rw [h1]
  exact (pPrimeCore_two_eq_componentOddCore (↥C)).symm

theorem isSolvTwoCompSL23In_sup_oddCoreIn (hL : IsClassicalMember3 L z) :
    IsSolvTwoCompSL23In (Subgroup.centralizer ({z} : Set Y))
      (L ⊔ oddCoreIn (Subgroup.centralizer ({z} : Set Y))) := by
  set C : Subgroup Y := Subgroup.centralizer ({z} : Set Y) with hC
  have hLC : L ≤ C := isSubnormal_le hL.subnormal
  refine ⟨sup_le hLC (oddCoreIn_le C), ?_⟩
  let π : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C)
  let φ0 : ↥L →* ↥C ⧸ pPrimeCore 2 ↥C := π.comp (Subgroup.inclusion hLC)
  have hrange : φ0.range = (L.subgroupOf C).map π := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  refine ⟨φ0.range, ?_, ?_, ?_⟩
  · rw [hrange]
    have h1 : IsSubnormal (L.subgroupOf C) (C.subgroupOf C) :=
      isSubnormal_subgroupOf hL.subnormal C
    rw [Subgroup.subgroupOf_self] at h1
    exact (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h1
      Subgroup.IsSubnormal.top).map (QuotientGroup.mk'_surjective _)
  · obtain ⟨e⟩ := hL.nonempty_equiv
    have hker : φ0.ker = classicalInvolutionOddCore L := by
      ext x
      rw [MonoidHom.mem_ker]
      change π (Subgroup.inclusion hLC x) = 1 ↔ _
      have h1 : π (Subgroup.inclusion hLC x) = 1 ↔ Subgroup.inclusion hLC x ∈ pPrimeCore 2 ↥C :=
        QuotientGroup.eq_one_iff _
      rw [h1, mem_oddCore_iff_mem_oddCoreIn hL x, ← subgroupOf_oddCoreIn_eq C]
      rfl
    let Φ : ↥L →* ↥φ0.range := φ0.rangeRestrict
    have hΦ : Function.Surjective Φ := φ0.rangeRestrict_surjective
    have hkerΦ : Φ.ker = classicalInvolutionOddCore L := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hker
    exact ⟨((QuotientGroup.quotientKerEquivOfSurjective Φ hΦ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hkerΦ)).trans e⟩
  · rw [hrange, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      Subgroup.subgroupOf_sup hLC (oddCoreIn_le C), subgroupOf_oddCoreIn_eq]

theorem typeABExcluded_of_solvBalance (h : SolvableL2PrimeBalance) :
    ∀ (Y : Type) [Group Y] [Finite Y] (z : Y) (L T : Subgroup Y), Setting z L T →
      (memberIndex L T = 12 ∨ memberIndex L T = 24) → False := by
  intro Y _ _ z L T hS hidx
  have hL := hS.member
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hS.normal
  set C : Subgroup Y := Subgroup.centralizer ({z} : Set Y) with hC
  have hLC : L ≤ C := isSubnormal_le hL.subnormal
  have hbal := h Y z hL.orderOf_eq_two (L ⊔ oddCoreIn C) (isSolvTwoCompSL23In_sup_oddCoreIn hL)
  have hz2 : IsPGroup 2 (Subgroup.zpowers (⟨z, hL.mem⟩ : L)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk]; rw [hL.orderOf_eq_two]; norm_num)
  obtain ⟨Q, hzQ⟩ := hz2.exists_le_sylow
  have hzmem : (⟨z, hL.mem⟩ : L) ∈ (Q : Subgroup L) := hzQ (Subgroup.mem_zpowers _)
  have hQres : ∀ x ∈ (Q : Subgroup L),
      (x : Y) ∈ oPrimeResidualOf 2 (L ⊔ oddCoreIn C) := by
    intro x hx
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨x, hx⟩
    have hxV : (x : Y) ∈ L ⊔ oddCoreIn C := (le_sup_left : L ≤ L ⊔ oddCoreIn C) x.2
    have hk' : (x : Y) ^ 2 ^ k = 1 := by
      have := congrArg (fun q : (Q : Subgroup L) => ((q : L) : Y)) hk
      simpa using this
    refine ⟨⟨(x : Y), hxV⟩, Subgroup.subset_closure ⟨k, Subtype.ext hk'⟩, rfl⟩
  have hO : CFSG.pPrimeCore 2 Y = ⊥ := by
    rw [pPrimeCore_two_eq_componentOddCore]
    exact hS.oddCore
  have hCT : Subgroup.centralizer (T : Set Y) = ⊥ := hS.cent
  rcases hbal with hcase | ⟨L', hL', hzL', hres⟩
  ·
    have hzN : z ∈ pPrimePCore 2 Y := hcase (hQres _ hzmem)
    have hpc : pPrimePCore 2 Y ≤ pCore 2 Y := by
      refine le_sSup ⟨inferInstance, ?_⟩
      intro y
      have hy : (QuotientGroup.mk' (pPrimeCore 2 Y) (y : Y)) ∈ pCore 2 (Y ⧸ pPrimeCore 2 Y) := y.2
      obtain ⟨k, hk⟩ := pCore_isPGroup (p := 2) (G := Y ⧸ pPrimeCore 2 Y)
        ⟨_, hy⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : QuotientGroup.mk' (pPrimeCore 2 Y) ((y : Y) ^ 2 ^ k) = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have h2 : (y : Y) ^ 2 ^ k ∈ pPrimeCore 2 Y := (QuotientGroup.eq_one_iff _).mp h1
      rw [hO, Subgroup.mem_bot] at h2
      simpa using h2
    have hTpc := (Q3B.isComponentOf_le_centralizer_pCore_not_le hS.comp).1
    have hpcT : pCore 2 Y ≤ Subgroup.centralizer (T : Set Y) :=
      Subgroup.le_centralizer_iff.mp hTpc
    have : z ∈ Subgroup.centralizer (T : Set Y) := hpcT (hpc hzN)
    rw [hCT, Subgroup.mem_bot] at this
    exact hL.ne_one this
  ·
    have hcore : componentClassificationOddCore Y = ⊥ := hS.oddCore
    have hL'c : IsComponentOf L' ⊤ :=
      TwoComponents.ordinary_of_corefree hcore
        ((ComponentClassification.CatalogueBAlternating.pComponent_two_iff L').1 hL')
    have hcomm := distinct_components_commute ((isComponent_iff_open L').mpr hL'c)
      ((isComponent_iff_open T).mpr hS.comp)
    have hzL : z ∈ L' := hres (hQres _ hzmem)
    have hL'T : L' = T := by
      rcases hcomm with h1 | h1
      · exact h1
      · exfalso
        have hle : L' ≤ Subgroup.centralizer (T : Set Y) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
        rw [hCT] at hle
        have := hle hzL
        rw [Subgroup.mem_bot] at this
        exact hL.ne_one this
    have hQT : (Q : Subgroup L) ≤ T.subgroupOf L := by
      intro x hx
      rw [Subgroup.mem_subgroupOf, ← hL'T]
      exact hres (hQres x hx)
    have hdvd : (T.subgroupOf L ⊔ classicalInvolutionOddCore L).index ∣ (Q : Subgroup L).index :=
      Subgroup.index_dvd_of_le (hQT.trans le_sup_left)
    have hnd : ¬ 2 ∣ (Q : Subgroup L).index := Sylow.not_dvd_index Q
    apply hnd
    refine dvd_trans ?_ hdvd
    change 2 ∣ memberIndex L T
    rcases hidx with h | h <;> rw [h] <;> norm_num

end CFSG.ClassicalInvolution.Q3.Q3T.MFS
