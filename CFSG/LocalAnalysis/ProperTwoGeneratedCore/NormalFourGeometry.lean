module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CharacteristicCore
public import CFSG.LocalAnalysis.LargeEvenClassification.NormalFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.CommutingElementaryProduct

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LargeEvenClassification.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem normal_four_centralizer_index
    (htwo : IsPGroup 2 G) (V : Subgroup G) [V.Normal]
    (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4) :
    let C := Subgroup.centralizer (V : Set G)
    C.Normal ∧ V ≤ C ∧ C.index ≤ 2 := by
  classical
  let conjugation : G →* MulAut V := MulAut.conjNormal
  let image := conjugation.range
  have hIgroup : IsPGroup 2 image :=
    htwo.of_surjective conjugation.rangeRestrict conjugation.rangeRestrict_surjective
  let : Fintype V := Fintype.ofFinite V
  let action := (automorphismNonidentityPermutation (Ambient := V)).comp image.subtype
  have hactionInjective : Function.Injective action :=
    automorphismNonidentityPermutation_injective.comp image.subtype_injective
  have hdiv := card_dvd_of_injective_hom action hactionInjective
  have hpoints : Fintype.card {v : V // v ≠ 1} = 3 := by
    have hformula := Fintype.card_subtype_compl (fun v : V => v = 1)
    have hcard : Fintype.card V = 4 := Nat.card_eq_fintype_card.symm.trans hVcard
    rw [hcard] at hformula
    simpa using hformula
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm {v : V // v ≠ 1}),
    Fintype.card_perm, hpoints] at hdiv
  norm_num at hdiv
  have hdivNat : Nat.card image ∣ 6 := by
    simpa only [Nat.card_eq_fintype_card] using hdiv
  obtain ⟨exponent, hcard⟩ := hIgroup.exists_card_eq
  have hexponent : exponent ≤ 1 := by
    by_contra hlarge
    have hfour : 4 ∣ 6 := by
      have hpow : 2 ^ 2 ∣ 2 ^ exponent := Nat.pow_dvd_pow 2 (by omega)
      rw [← hcard] at hpow
      exact hpow.trans hdivNat
    norm_num at hfour
  have hbound : Nat.card image ≤ 2 := by
    rw [hcard]
    exact (Nat.pow_le_pow_right (by decide) hexponent).trans (by decide)
  refine ⟨inferInstance, ?_, ?_⟩
  · let := hV.1
    exact Subgroup.le_centralizer V
  · rw [← normal_conjugation_kernel_eq_centralizer, Subgroup.index_ker]
    exact hbound

omit [Finite G] in
theorem involution_zpowers_elementary (t : G) (ht : orderOf t = 2) :
    IsElemAbelian 2 (Subgroup.zpowers t) := by
  refine ⟨inferInstance, ?_⟩
  intro x hx
  obtain ⟨power, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← ht]
  exact zpow_pow_orderOf

theorem involution_zpowers_disjoint
    (V : Subgroup G) (t : G) (ht : orderOf t = 2) (htV : t ∉ V) :
    Disjoint V (Subgroup.zpowers t) := by
  let T : Subgroup G := Subgroup.zpowers t
  have hTcard : Nat.card T = 2 := by rw [Nat.card_zpowers, ht]
  have hdiv : Nat.card (V ⊓ T : Subgroup G) ∣ 2 := by
    simpa only [hTcard] using
      (Subgroup.card_dvd_of_le (inf_le_right : V ⊓ T ≤ T))
  have hsmall : Nat.card (V ⊓ T : Subgroup G) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hsmall | hequal
    · exact hsmall
    · have heq : V ⊓ T = T := Subgroup.eq_of_le_of_card_ge inf_le_right (by
        rw [hequal, hTcard])
      have htInf : t ∈ V ⊓ T := by
        rw [heq]
        exact Subgroup.mem_zpowers t
      exact False.elim (htV htInf.1)
  exact disjoint_iff.mpr (Subgroup.card_eq_one.mp hsmall)

omit [Finite G] in
theorem commuting_elementary_sup
    (A B : Subgroup G) (hA : IsElemAbelian 2 A) (hB : IsElemAbelian 2 B)
    (hcommute : A ≤ Subgroup.centralizer (B : Set G)) :
    IsElemAbelian 2 (A ⊔ B) := by
  let : CommGroup A := { A.toGroup with mul_comm := @mul_comm' A _ hA.1 }
  let : CommGroup B := { B.toGroup with mul_comm := @mul_comm' B _ hB.1 }
  have commute : ∀ a : A, ∀ b : B, Commute (A.subtype a) (B.subtype b) := by
    intro a b
    exact (Subgroup.mem_centralizer_iff.mp (hcommute a.property) b b.property).symm
  let productMap := A.subtype.noncommCoprod B.subtype commute
  have htop : IsElemAbelian 2 (⊤ : Subgroup (A × B)) := by
    refine ⟨inferInstance, ?_⟩
    intro pair _
    exact Prod.ext (Subtype.ext (hA.2 pair.1 pair.1.property))
      (Subtype.ext (hB.2 pair.2 pair.2.property))
  have hrange : IsElemAbelian 2 productMap.range := by
    rw [MonoidHom.range_eq_map]
    exact elementary_map ⊤ htop productMap
  have heq : productMap.range = A ⊔ B := by
    simpa only [Subgroup.subtype_range] using
      MonoidHom.noncommCoprod_range A.subtype B.subtype commute
  exact heq ▸ hrange

theorem normal_four_centralizer_rank_three
    (htwo : IsPGroup 2 G) (V : Subgroup G) [V.Normal]
    (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4)
    (A : Subgroup G) (hA : IsElemAbelian 2 A) (hAcard : Nat.card A = 8) :
    let C := Subgroup.centralizer (V : Set G)
    let B := A ⊓ C
    let U := B ⊔ V
    4 ≤ Nat.card B ∧ U ≤ C ∧ V ≤ U ∧ IsElemAbelian 2 U ∧
      8 ≤ Nat.card U ∧ 3 ≤ twoRank C := by
  classical
  let C := Subgroup.centralizer (V : Set G)
  let B := A ⊓ C
  let U := B ⊔ V
  obtain ⟨hCnormal, hVC, hindex⟩ := normal_four_centralizer_index htwo V hV hVcard
  let : C.Normal := hCnormal
  have hindexPositive : 0 < C.index := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
  have hrelative : C.relIndex A ≤ 2 :=
    (Nat.le_of_dvd hindexPositive (Subgroup.relIndex_dvd_index_of_normal C A)).trans hindex
  have hproduct : C.relIndex A * Nat.card B = 8 := by
    simpa only [inf_comm, B, hAcard] using Subgroup.relIndex_mul_card C A
  have hBcard : 4 ≤ Nat.card B := by
    have hbound := Nat.mul_le_mul_right (Nat.card B) hrelative
    rw [hproduct] at hbound
    omega
  have hB : IsElemAbelian 2 B := elementary_subgroup_of_le A B hA inf_le_left
  have hU : IsElemAbelian 2 U := commuting_elementary_sup B V hB hV inf_le_right
  have hUC : U ≤ C := sup_le inf_le_right hVC
  have hVU : V ≤ U := le_sup_right
  have hUcard : 8 ≤ Nat.card U := by
    by_contra hsmall
    obtain ⟨rank, hcard⟩ := (elementary_isPGroup 2 U hU).exists_card_eq
    have hVbound : 4 ≤ Nat.card U := hVcard ▸ Subgroup.card_le_of_le hVU
    have hrank : rank = 2 := by
      have hupper : rank < 3 := by
        apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
        simpa only [← hcard] using (show Nat.card U < 8 by omega)
      have hlower : 2 ≤ rank := by
        apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
        simpa only [← hcard] using hVbound
      omega
    have hUfour : Nat.card U = 4 := by rw [hcard, hrank]; norm_num
    have hUV : U = V := Subgroup.eq_of_le_of_card_ge hVU (by rw [hUfour, hVcard]) |>.symm
    have hBV : B ≤ V := hUV ▸ (le_sup_left : B ≤ U)
    have hBVeq : B = V := Subgroup.eq_of_le_of_card_ge hBV (by rw [hVcard]; exact hBcard)
    have hVA : V ≤ A := hBVeq ▸ (inf_le_left : B ≤ A)
    have hAC : A ≤ C := by
      intro a ha
      apply Subgroup.mem_centralizer_iff.mpr
      intro v hv
      exact congrArg Subtype.val (@mul_comm' A _ hA.1 ⟨v, hVA hv⟩ ⟨a, ha⟩)
    have hBA : B = A := inf_eq_left.mpr hAC
    have hBeight : Nat.card B = 8 := hBA ▸ hAcard
    have hBfour : Nat.card B = 4 := hBVeq ▸ hVcard
    omega
  have hCrank : 3 ≤ twoRank C := by
    obtain ⟨rank, hcard⟩ := (elementary_isPGroup 2 U hU).exists_card_eq
    have hrank : 3 ≤ rank := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      simpa only [← hcard] using hUcard
    rw [twoRank, ← pRank_subgroup_eq_internal_top 2 (by decide)]
    exact hrank.trans (le_csSup (pRank_set_bddAbove 2 (by decide) C) ⟨U, hUC, hU, hcard⟩)
  exact ⟨hBcard, hUC, hVU, hU, hUcard, hCrank⟩

theorem central_four_involution_coverage
    (V : Subgroup G) (hcentral : V ≤ Subgroup.center G)
    (hV : IsElemAbelian 2 V) (hVcard : Nat.card V = 4)
    (u : G) (hu : orderOf u = 2) (huV : u ∉ V)
    (t : G) (ht : orderOf t = 2) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ t ∈ E := by
  classical
  have extend (x : G) (hx : orderOf x = 2) (hxV : x ∉ V) :
      ∃ E : Subgroup G, V ≤ E ∧ x ∈ E ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 := by
    let T := Subgroup.zpowers x
    have hcommute : V ≤ Subgroup.centralizer (T : Set G) := by
      intro v hv
      exact Subgroup.mem_centralizer_iff.mpr (fun y _ =>
        Subgroup.mem_center_iff.mp (hcentral hv) y)
    obtain ⟨E, hVE, hTE, hE, hEcard, _⟩ :=
      commuting_disjoint_elementary_product (firstRank := 2) (secondRank := 1) V T hV
        (involution_zpowers_elementary x hx) (by simpa using hVcard)
        (by simp [T, hx]) hcommute (involution_zpowers_disjoint V x hx hxV)
    exact ⟨E, hVE, hTE (Subgroup.mem_zpowers x), hE, by simpa using hEcard⟩
  by_cases htV : t ∈ V
  · obtain ⟨E, hVE, _, hE, hEcard⟩ := extend u hu huV
    exact ⟨E, hE, hEcard, hVE htV⟩
  · obtain ⟨E, _, htE, hE, hEcard⟩ := extend t ht htV
    exact ⟨E, hE, hEcard, htE⟩

end CFSG.ProperTwoGeneratedCore
