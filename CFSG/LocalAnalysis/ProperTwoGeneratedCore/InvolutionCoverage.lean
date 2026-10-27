module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourExistence

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LargeEvenClassification.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem coset_involution_sign_obstruction
    (H : Subgroup G) (q : ℕ) (hq : Odd q) (hqpositive : 1 ≤ q)
    (hindex : H.index = 2 * q) (t : G) (ht : orderOf t = 2)
    (hmiss : ∀ g : G, g⁻¹ * t * g ∉ H) :
    ∃ sign : G →* ℤˣ, sign t = -1 ∧ sign.ker.Normal ∧ sign.ker.index = 2 ∧
      commutator G ≤ sign.ker ∧ t ∉ sign.ker := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let action := MulAction.toPermHom G (G ⧸ H)
  let sign : G →* ℤˣ := Equiv.Perm.sign.comp action
  have hfixedEmpty : IsEmpty (Function.fixedPoints (action t)) := by
    constructor
    intro fixed
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective fixed.val
    have hfixed : action t (QuotientGroup.mk g) = QuotientGroup.mk g := by
      rw [hg]
      exact fixed.property
    have hcoset : (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk (t * g) :=
      hfixed.symm
    have hconjugate : g⁻¹ * (t * g) ∈ H := QuotientGroup.eq.mp hcoset
    exact hmiss g (by simpa only [mul_assoc] using hconjugate)
  have hnegative : sign t = -1 := by
    have hpow : action t ^ 2 = 1 := by
      rw [← map_pow, show t ^ 2 = 1 from ht ▸ pow_orderOf_eq_one t, map_one]
    let : IsEmpty (Function.fixedPoints (action t)) := hfixedEmpty
    have hzero : Fintype.card (Function.fixedPoints (action t)) = 0 := Fintype.card_eq_zero
    have hcard : Fintype.card (G ⧸ H) = 2 * q := by
      rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hindex]
    change Equiv.Perm.sign (action t) = -1
    rw [Equiv.Perm.sign_of_pow_two_eq_one hpow, hzero,
      Nat.sub_zero, hcard, show 2 * q / 2 = q by omega]
    exact hq.neg_one_pow
  have hexcluded : t ∉ sign.ker := by
    rw [MonoidHom.mem_ker, hnegative]
    norm_num
  have hkernelIndex : sign.ker.index = 2 := by
    apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
    refine ⟨t, hexcluded, ?_⟩
    intro g
    rcases Int.units_eq_one_or (sign g) with hone | hminus
    · exact Or.inr (MonoidHom.mem_ker.mpr hone)
    · left
      rw [MonoidHom.mem_ker, map_mul, hminus, hnegative]
      norm_num
  have hqUsed : 0 < H.index := by rw [hindex]; omega
  have hcommutator := Abelianization.commutator_subset_ker sign
  exact ⟨sign, hnegative, inferInstance, hkernelIndex, hcommutator, hexcluded⟩

theorem derived_involution_sylow_maximal_transfer
    (S : Sylow 2 G) (U : Subgroup G) (hUS : U ≤ (S : Subgroup G))
    (hindex : U.relIndex (S : Subgroup G) = 2)
    (t : G) (ht : orderOf t = 2) (htDerived : t ∈ commutator G) :
    ∃ g : G, g⁻¹ * t * g ∈ U := by
  classical
  by_contra hnone
  have hmiss : ∀ g : G, g⁻¹ * t * g ∉ U := by simpa only [not_exists] using hnone
  have hodd : Odd (S : Subgroup G).index := by
    apply Nat.odd_iff.mpr
    have hnot := S.not_dvd_index
    omega
  have hpositive : 1 ≤ (S : Subgroup G).index :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hUindex : U.index = 2 * (S : Subgroup G).index := by
    simpa only [hindex] using (Subgroup.relIndex_mul_index hUS).symm
  obtain ⟨sign, _, _, _, hderived, hexcluded⟩ :=
    coset_involution_sign_obstruction U _ hodd hpositive hUindex t ht hmiss
  exact hexcluded (hderived htDerived)

omit [Finite G] in
theorem elementary_eight_coverage_lift
    (H : Subgroup G) (t : H)
    (hcoverage : ∃ E : Subgroup H, IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ t ∈ E) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ (t : G) ∈ E := by
  obtain ⟨E, hE, hcard, ht⟩ := hcoverage
  refine ⟨E.map H.subtype, Subgroup.map_subtype_le _,
    elementary_map E hE H.subtype, ?_, Subgroup.mem_map_of_mem H.subtype ht⟩
  rw [Subgroup.card_map_of_injective H.subtype_injective, hcard]

omit [Finite G] in
theorem elementary_eight_coverage_conjugate
    (t g : G) (E : Subgroup G) (hE : IsElemAbelian 2 E)
    (hcard : Nat.card E = 8) (ht : g⁻¹ * t * g ∈ E) :
    ∃ F : Subgroup G, IsElemAbelian 2 F ∧ Nat.card F = 8 ∧ t ∈ F := by
  let conjugation := MulAut.conj g
  refine ⟨E.map conjugation.toMonoidHom, elementary_map E hE conjugation.toMonoidHom,
    ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective conjugation.injective, hcard]
  · exact Subgroup.mem_map.mpr ⟨g⁻¹ * t * g, ht, by
      simp [conjugation, MulAut.conj_apply, mul_assoc]⟩

theorem normal_four_centralizer_involution_coverage
    (htwo : IsPGroup 2 G) (V : Subgroup G) [V.Normal]
    (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4)
    (A : Subgroup G) (hA : IsElemAbelian 2 A) (hAcard : Nat.card A = 8)
    (t : G) (ht : orderOf t = 2) (htC : t ∈ Subgroup.centralizer (V : Set G)) :
    ∃ E : Subgroup G, E ≤ Subgroup.centralizer (V : Set G) ∧
      IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ t ∈ E := by
  classical
  let C := Subgroup.centralizer (V : Set G)
  let U := (A ⊓ C) ⊔ V
  obtain ⟨_, hUC, hVU, hU, hUcard, _⟩ :=
    normal_four_centralizer_rank_three htwo V hV hVcard A hA hAcard
  change 8 ≤ Nat.card U at hUcard
  have hVC : V ≤ C := (normal_four_centralizer_index htwo V hV hVcard).2.1
  have hUneV : ¬ U ≤ V := by
    intro hle
    have hsmall := Subgroup.card_le_of_le hle
    rw [hVcard] at hsmall
    omega
  obtain ⟨u, huU, huV⟩ := IsConcreteLE.not_le_iff_exists.mp hUneV
  have huone : u ≠ 1 := by intro hone; exact huV (hone ▸ V.one_mem)
  have huorder : orderOf u = 2 :=
    orderOf_eq_prime (hU.2 u huU) huone
  let Vc := V.subgroupOf C
  have hVc : IsElemAbelian 2 Vc :=
    elementary_transport 2 V Vc (Subgroup.subgroupOfEquivOfLe hVC).symm hV
  have hVccard : Nat.card Vc = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv).trans hVcard
  have hcentral : Vc ≤ Subgroup.center C := by
    intro v hv
    apply Subgroup.mem_center_iff.mpr
    intro c
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp c.property v hv).symm
  let uc : C := ⟨u, hUC huU⟩
  let tc : C := ⟨t, htC⟩
  have huc : orderOf uc = 2 := (Subgroup.orderOf_coe uc).symm.trans huorder
  have hucOutside : uc ∉ Vc := huV
  have htc : orderOf tc = 2 := (Subgroup.orderOf_coe tc).symm.trans ht
  exact elementary_eight_coverage_lift C tc
    (central_four_involution_coverage Vc hcentral hVc hVccard uc huc hucOutside tc htc)

theorem exists_elementary_eight_of_rank_three (hrank : 3 ≤ twoRank G) :
    ∃ A : Subgroup G, IsElemAbelian 2 A ∧ Nat.card A = 8 := by
  obtain ⟨E, _, hE, hEcard⟩ := pRank_attained 2 (⊤ : Subgroup G) (by
    change 0 < twoRank G
    omega)
  have hdiv : 2 ^ 3 ∣ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_dvd_pow 2 hrank
  obtain ⟨A, hAcard, _, hAE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := (⊥ : Subgroup G)) (L := E) (by simp) hdiv bot_le
  exact ⟨A, elementary_subgroup_of_le E A hE hAE, by simpa using hAcard⟩

theorem derived_involution_coverage_of_sylow_normal_four
    (S : Sylow 2 G) (hrank : 3 ≤ twoRank G)
    (V : Subgroup (S : Subgroup G)) [V.Normal]
    (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4)
    (t : G) (ht : orderOf t = 2) (htDerived : t ∈ commutator G) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ t ∈ E := by
  classical
  let P := (S : Subgroup G)
  let C := Subgroup.centralizer (V : Set P)
  have hPrank : 3 ≤ twoRank P := by
    change 3 ≤ Open.pRank 2 (⊤ : Subgroup P)
    rw [← pRank_subgroup_eq_internal_top 2 (by decide), sylow_two_rank_eq]
    exact hrank
  obtain ⟨A, hA, hAcard⟩ := exists_elementary_eight_of_rank_three hPrank
  obtain ⟨_, _, hindex⟩ := normal_four_centralizer_index S.isPGroup' V hV hVcard
  change C.index ≤ 2 at hindex
  let Cimage := C.map P.subtype
  have hCimageP : Cimage ≤ P := Subgroup.map_subtype_le _
  have hrelative : Cimage.relIndex P = C.index := by
    change ((C.map P.subtype).comap P.subtype).index = C.index
    rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  have hconjugate : ∃ g : G, g⁻¹ * t * g ∈ Cimage := by
    by_cases hCtop : C = ⊤
    · have hCimage : Cimage = P := by
        change C.map P.subtype = P
        rw [hCtop, Subgroup.map_top, Subgroup.range_subtype]
      obtain ⟨g, _, hgt⟩ := involution_conjugate_into_sylow S (⊤ : Subgroup G) le_top
        t (by trivial) ht
      exact ⟨g, hCimage.symm ▸ hgt⟩
    · have hindexTwo : C.index = 2 := by
        have hpositive : 0 < C.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
        have hnotOne : C.index ≠ 1 := by
          exact fun heq => hCtop (Subgroup.index_eq_one.mp heq)
        omega
      exact derived_involution_sylow_maximal_transfer S Cimage hCimageP
        (hrelative.trans hindexTwo) t ht htDerived
  obtain ⟨g, hgCimage⟩ := hconjugate
  obtain ⟨x, hxC, hx⟩ := hgCimage
  change (x : G) = g⁻¹ * t * g at hx
  have hxOrder : orderOf (x : G) = 2 := by
    rw [hx]
    simpa only [MulAut.conj_apply, inv_inv, ht] using (MulAut.conj g⁻¹).orderOf_eq t
  have hxInternalOrder : orderOf x = 2 := (Subgroup.orderOf_coe x).symm.trans hxOrder
  obtain ⟨E, _, hE, hEcard, hxE⟩ := normal_four_centralizer_involution_coverage
    S.isPGroup' V hV hVcard A hA hAcard x hxInternalOrder hxC
  have hEambient := elementary_eight_coverage_lift P x ⟨E, hE, hEcard, hxE⟩
  obtain ⟨F, _, hF, hFcard, hxF⟩ := hEambient
  exact elementary_eight_coverage_conjugate t g F hF hFcard (hx ▸ hxF)

theorem derived_involution_rank_three_coverage
    (hrank : 3 ≤ twoRank G) (t : G) (ht : orderOf t = 2)
    (htDerived : t ∈ commutator G) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ t ∈ E := by
  classical
  let S : Sylow 2 G := default
  have hSrank : 3 ≤ twoRank (S : Subgroup G) := by
    change 3 ≤ Open.pRank 2 (⊤ : Subgroup (S : Subgroup G))
    rw [← pRank_subgroup_eq_internal_top 2 (by decide), sylow_two_rank_eq]
    exact hrank
  obtain ⟨V, hVnormal, hV, hVcard⟩ :=
    high_two_rank_normal_four (S : Subgroup G) S.isPGroup' hSrank
  let : V.Normal := hVnormal
  exact derived_involution_coverage_of_sylow_normal_four S hrank V hV hVcard t ht htDerived

theorem perfect_involution_rank_three_coverage [Group.IsPerfect G]
    (hrank : 3 ≤ twoRank G) (t : G) (ht : orderOf t = 2) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ t ∈ E :=
  derived_involution_rank_three_coverage hrank t ht
    (by rw [Group.IsPerfect.commutator_eq_top]; trivial)

end CFSG.ProperTwoGeneratedCore
