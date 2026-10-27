module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Sub
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryOut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternating
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoOdd

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem le_normalizer_of_normal_subgroupOf {K₀ H : Subgroup G} (hKH : K₀ ≤ H)
    (hn : (K₀.subgroupOf H).Normal) : H ≤ normalizer (K₀ : Set G) := by
  intro h hh
  refine (mem_normalizer_subgroupOf_iff hKH ⟨h, hh⟩).mp ?_
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hn.conj_mem y hy _
  · intro hy
    have := hn.conj_mem _ hy (⟨h, hh⟩ : H)⁻¹
    simpa [mul_assoc] using this

theorem outer_solvable_of_small {X : Type} [Group X]
    (h : Nonempty (X ≃* PSU3 2 2) ∨ Nonempty (X ≃* PSL(2, ZMod 7)) ∨
      Nonempty (X ≃* alternatingGroup (Fin 5)) ∨ Nonempty (X ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (X ≃* alternatingGroup (Fin 7))) :
    Group.IsSolvable (Outer X) := by
  rcases h with h | h | h | h | h
  · obtain ⟨e⟩ := h
    have : Group.IsSolvable (Outer (PSU3 2 2)) :=
      SignalizerFunctorTheorem.McBride.UnitaryOut.outer_solvable_psu3 le_rfl
    exact OuterAutomorphisms.solvable_of_equiv e.symm
  · obtain ⟨e⟩ := h
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact CatalogueSchreierLinearTwo.odd_outer_solvable_of_equiv (ZMod 7)
      (by rw [Nat.card_zmod]; decide) (by rw [Nat.card_zmod]; norm_num) e
  · exact CatalogueSchreierAlternating.alternating_schreier_of_nonempty_equiv 5 le_rfl h
  · exact CatalogueSchreierAlternating.alternating_schreier_of_nonempty_equiv 6 (by norm_num) h
  · exact CatalogueSchreierAlternating.alternating_schreier_of_nonempty_equiv 7 (by norm_num) h

theorem not_le_of_isQuasisimple {A X : Subgroup G} (hq : Open.IsQuasisimple A)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : ¬ A ≤ X := by
  intro hAX
  have h1 : ⁅A, A⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact hX b (hAX hb) a (hAX ha)
  rw [commutator_self_of_isQuasisimple hq] at h1
  have : Nontrivial (A ⧸ center A) := hq.2.toNontrivial
  have hcard : Nat.card A = 1 := by rw [h1, card_bot]
  have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hcard).1
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (A ⧸ center A)
  apply hxy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [Subsingleton.elim x y]

variable [Finite G]

omit [Finite G] in
theorem le_centralizer_of_outer_solvable {A K₀ H : Subgroup G} (hq : Open.IsQuasisimple A)
    (hAH : A ≤ normalizer (H : Set G)) (hAK : A ≤ centralizer (K₀ : Set G))
    (hout : Group.IsSolvable (Outer H))
    (hsolv : Group.IsSolvable (normalizer ((K₀.subgroupOf H : Subgroup H) : Set H))) :
    H ≤ centralizer (A : Set G) := by
  have : Group.IsPerfect A := ⟨hq.1⟩
  set K' : Subgroup H := K₀.subgroupOf H with hK'
  let action : A →* MulAut H := H.normalizerMonoidHom.comp (Subgroup.inclusion hAH)
  have haction : ∀ (a : A) (h : H), ((action a h : H) : G) = a * h * (a : G)⁻¹ :=
    fun _ _ => rfl
  set S : Subgroup (MulAut H) := (centralizer (K' : Set H)).map (MulAut.conj : H →* MulAut H)
    with hS
  have hmemS : ∀ a : A, action a ∈ S := by
    intro a
    obtain ⟨h, hh⟩ := OuterAutomorphisms.perfect_action_inner action a
    refine ⟨h, ?_, hh.symm⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro k hk
    have h1 : action a k = k := by
      apply Subtype.ext
      rw [haction]
      have hka : (k : G) * a = a * k :=
        (mem_centralizer_iff.mp (hAK a.2)) k (mem_subgroupOf.mp hk)
      rw [← hka, mul_inv_cancel_right]
    rw [hh, MulAut.conj_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hCN : centralizer (K' : Set H) ≤ normalizer (K' : Set H) := centralizer_le_normalizer _
  have : Group.IsSolvable (centralizer (K' : Set H)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hCN)
  have : Group.IsSolvable S :=
    Group.isSolvable_of_surjective
      ((MulAut.conj : H →* MulAut H).subgroupMap_surjective (centralizer (K' : Set H)))
  have hφ := SolvableKernelContainment.hom_eq_one (action.codRestrict S hmemS)
  intro h hh
  rw [mem_centralizer_iff]
  intro a ha
  have h1 : action ⟨a, ha⟩ = 1 := by
    have := congrArg (fun f : A →* S => (f ⟨a, ha⟩ : MulAut H)) hφ
    simpa using this
  have h2 : ((action ⟨a, ha⟩ ⟨h, hh⟩ : H) : G) = h := by rw [h1]; rfl
  rw [haction] at h2
  exact mul_inv_eq_iff_eq_mul.mp h2

theorem le_normalizer_of_cyclic {A R H : Subgroup G} (hA : standardComponentIsStandard A)
    (hRK : R ≤ centralizer (A : Set G)) (hRH : R ≤ H) (h4 : 4 ∣ Nat.card R)
    (hAH : A ≤ normalizer (H : Set G)) {U : Subgroup H} (hUR : U ≤ R.subgroupOf H)
    (hUidx : U.relIndex (R.subgroupOf H) = 2)
    (hUc : IsMulCommutative (normalClosure (U : Set H))) :
    H ≤ normalizer (centralizer (A : Set G) : Set G) := by
  set K := centralizer (A : Set G) with hKdef
  have hK : TightlyEmbedded K := tightlyEmbedded_centralizer hA
  have hq : Open.IsQuasisimple A := hA.1
  have hNK : normalizer (K : Set G) = normalizer (A : Set G) := normalizer_centralizer_eq hA
  set UG : Subgroup G := U.map H.subtype with hUG
  have hUGK : UG ≤ K := by
    rintro _ ⟨u, hu, rfl⟩
    exact hRK (mem_subgroupOf.mp (hUR hu))
  have h2U : 2 * Nat.card U = Nat.card R := by
    have h1 := Subgroup.relIndex_mul_card U (R.subgroupOf H)
    rwa [inf_eq_left.mpr hUR, hUidx, card_subgroupOf hRH] at h1
  have heven : Even (Nat.card UG) := by
    rw [hUG, card_map_of_injective H.subtype_injective]
    obtain ⟨c, hc⟩ := h4
    exact ⟨c, by omega⟩
  set X : Subgroup G := ncIn UG H with hXdef
  have hXmap : X ≤ (normalClosure (U : Set H)).map H.subtype := by
    refine (closure_le _).mpr ?_
    rintro _ ⟨h, hh, k, hk, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hk
    have hmem : (⟨h, hh⟩ : H) * u * (⟨h, hh⟩ : H)⁻¹ ∈ normalClosure (U : Set H) :=
      (normalClosure_normal (s := (U : Set H))).conj_mem _ (subset_normalClosure hu) _
    exact ⟨_, hmem, rfl⟩
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := hXmap hx
    obtain ⟨y', hy', rfl⟩ := hXmap hy
    have h1 := hUc.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩
    have h2 : x' * y' = y' * x' := congrArg Subtype.val h1
    exact congrArg Subtype.val h2
  have hUX : UG ≤ X := le_ncIn UG H
  have hXK : X ≤ normalizer (K : Set G) := by
    intro x hx
    refine normalizer_le_normalizer_of_tightlyEmbedded hK hUGK heven
      (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun u hu => ?_))
    exact (hXc x hx u (hUX hu)).symm
  have hXA : X ≤ normalizer (A : Set G) := hNK ▸ hXK
  have hAX : A ≤ normalizer (X : Set G) := by
    intro a ha
    refine mem_normalizer_of_map_conj_le (map_conj_ncIn_le
      (fun h hh => (mem_normalizer_iff.mp (hAH ha) h).mp hh) fun u hu => ?_)
    have hau : a * u = u * a := (mem_centralizer_iff.mp (hUGK hu)) a ha
    rw [hau, mul_inv_cancel_right]
    exact hu
  have hAXA : A ≤ normalizer ((X ⊓ A : Subgroup G) : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAX ha, le_normalizer ha⟩
  have hZ : X ⊓ A ≤ centralizer (A : Set G) := by
    rcases le_centerOf_or_eq_of_le_normalizer hq inf_le_right hAXA with h | h
    · exact h.trans inf_le_right
    · exact absurd (h.symm.le.trans inf_le_left) (not_le_of_isQuasisimple hq hXc)
  have hXK' : X ≤ K :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_inf_le_centerOf hq hXA hAX hZ)
  intro h hh
  by_contra hhN
  have hodd := hK.2 h hhN
  have hle : rightConjugate UG h ≤ K ⊓ rightConjugate K h := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    refine ⟨hXK' ?_, (mem_rightConjugate_iff K h x).mpr (hUGK hx)⟩
    have h1 : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ ∈ X := subset_closure ⟨h⁻¹, H.inv_mem hh, _, hx, rfl⟩
    simpa [mul_assoc] using h1
  have hdvd := card_dvd_of_le hle
  rw [rightConjugate_card] at hdvd
  exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr (heven.two_dvd.trans hdvd))

theorem exists_overlap_of_not_weaklyClosed {K R H : Subgroup G} (hR : IsSylowOf 2 R K)
    (hKH : K ≤ H)
    (hWC : ¬ ∃ S : Subgroup H, IsSylowOf 2 S ⊤ ∧ R.subgroupOf H ≤ S ∧
      ∀ x : H, rightConjugate (R.subgroupOf H) x ≤ S →
        rightConjugate (R.subgroupOf H) x = R.subgroupOf H) :
    ∃ x : G, x ∉ normalizer (K : Set G) ∧ rightConjugate R x ≤ normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRH : R ≤ H := hR.le.trans hKH
  obtain ⟨S₁, hS₁, hRS₁⟩ := AschbacherTheorem3.exists_isSylowOf_le hR.isPGroup
    (le_inf hRH (hR.le.trans le_normalizer) : R ≤ H ⊓ normalizer (K : Set G))
  obtain ⟨S, hS, hS₁S⟩ :=
    AschbacherTheorem3.exists_isSylowOf_le hS₁.isPGroup (hS₁.le.trans inf_le_left)
  have hS₁N : S₁ ≤ normalizer (K : Set G) := hS₁.le.trans inf_le_right
  have hS2 : IsPGroup 2 S := hS.isPGroup
  by_cases hSN : S ≤ normalizer (K : Set G)
  ·
    have hS' : IsSylowOf 2 (S.subgroupOf H) ⊤ := by
      rw [← subgroupOf_self H]
      exact (isSylowOf_subgroupOf_iff hS.le le_rfl).mpr hS
    have hRS' : R.subgroupOf H ≤ S.subgroupOf H := fun y hy =>
      mem_subgroupOf.mpr (hS₁S (hRS₁ (mem_subgroupOf.mp hy)))
    push Not at hWC
    obtain ⟨x, hxS, hxR⟩ := hWC (S.subgroupOf H) hS' hRS'
    rw [rightConjugate_subgroupOf] at hxS hxR
    have hRxH : rightConjugate R x ≤ H := AschbacherTheorem3.rightConjugate_le_of_mem hRH x.2
    have hRxS : rightConjugate R x ≤ S := fun y hy =>
      mem_subgroupOf.mp (hxS (show (⟨y, hRxH hy⟩ : H) ∈ (rightConjugate R x).subgroupOf H
        from hy))
    refine ⟨x, fun hxN => hxR ?_, hRxS.trans hSN⟩
    have hSK : R = S ⊓ K := Subgroup.eq_of_le_of_card_ge (le_inf (hRS₁.trans hS₁S) hR.le)
      (card_le_of_isSylowOf hR inf_le_right (hS2.to_le inf_le_left))
    have hRxR : rightConjugate R x = R := by
      refine Subgroup.eq_of_le_of_card_ge ((le_inf hRxS ?_).trans hSK.ge)
        (rightConjugate_card R x).ge
      rw [← (rightConjugate_eq_self_iff K x).mpr hxN]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate hR.le x
    rw [hRxR]
  ·
    have hne : S₁ ≠ S := fun h => hSN (h ▸ hS₁N)
    have : Group.IsNilpotent S := hS2.isNilpotent
    have hlt : S₁.subgroupOf S < ⊤ := lt_top_iff_ne_top.mpr fun h =>
      hne (le_antisymm hS₁S (subgroupOf_eq_top.mp h))
    obtain ⟨s, hsN, hsS₁⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    have hsN' : (s : G) ∈ normalizer (S₁ : Set G) := (mem_normalizer_subgroupOf_iff hS₁S s).mp hsN
    have hsS₁' : (s : G) ∉ S₁ := fun h => hsS₁ (mem_subgroupOf.mpr h)
    refine ⟨s, fun hsK => hsS₁' ?_, ?_⟩
    ·
      have hPS : S₁ ⊔ zpowers (s : G) ≤ S := sup_le hS₁S (zpowers_le.mpr s.2)
      have hPL : S₁ ⊔ zpowers (s : G) ≤ H ⊓ normalizer (K : Set G) :=
        sup_le hS₁.le (zpowers_le.mpr ⟨hS.le s.2, hsK⟩)
      have heq : S₁ = S₁ ⊔ zpowers (s : G) := Subgroup.eq_of_le_of_card_ge le_sup_left
        (card_le_of_isSylowOf hS₁ hPL (hS2.to_le hPS))
      rw [heq]
      exact mem_sup_right (mem_zpowers _)
    · have h1 : rightConjugate S₁ s = S₁ := (rightConjugate_eq_self_iff S₁ s).mpr hsN'
      exact ((AschbacherTheorem3.rightConjugate_le_rightConjugate hRS₁ (s : G)).trans
        h1.le).trans hS₁N

theorem dihedral_conclusion (h3L : Asc76Theorem3Large) (h3F : Asc76Theorem3Four) {G : Type}
    [Group G] [Finite G] {A : Subgroup G} (hO : standardComponentOddCore G = ⊥)
    (hA : standardComponentIsStandard A) {g : G} (hg : g ∉ normalizer (A : Set G))
    {R : Subgroup G} (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hRd : IsDihedralTwoGroup R)
    (_hm : 1 < Open.pRank 2 R) :
    Nat.card R = 4 ∧ IsElemAbelian 2 R ∧ ∃ g' : G, g' ∉ normalizer (A : Set G) ∧
      ∃ T' : Subgroup G,
        IsSylowOf 2 T' (rightConjugate (centralizer (A : Set G)) g' ⊓ normalizer (A : Set G)) ∧
          IsSylowOf 2 T' (rightConjugate (centralizer (A : Set G)) g') := by
  set K := centralizer (A : Set G) with hKdef
  have hK : TightlyEmbedded K := tightlyEmbedded_centralizer hA
  have hNK : normalizer (K : Set G) = normalizer (A : Set G) := normalizer_centralizer_eq hA
  obtain ⟨n, hn⟩ := exists_ncChain_succ_eq K
  set H := ncChain K n with hHdef
  have hst : ncIn K H = H := hn
  have hKH : K ≤ H := le_ncChain K n
  have hRH : R ≤ H := hR.le.trans hKH
  have hAN : A ≤ normalizer (K : Set G) := by rw [hNK]; exact le_normalizer
  have hAH : A ≤ normalizer (H : Set G) := hAN.trans (normalizer_le_normalizer_ncChain K n)
  have hHN : ¬ H ≤ normalizer (K : Set G) :=
    false_of_ncChain_le_normalizer hA hO le_rfl hK.1 le_rfl hg n
  have hK' : TightlyEmbedded (K.subgroupOf H) := tightlyEmbedded_subgroupOf hK hKH
  have hG' : normalClosure ((K.subgroupOf H : Subgroup H) : Set H) = ⊤ :=
    normalClosure_subgroupOf_eq_top hKH hst
  have hO' : standardComponentOddCore H = ⊥ :=
    standardComponentOddCore_eq_bot_of (eq_bot_of_odd_of_le_ncChain K hO n)
  have hR' : IsSylowOf 2 (R.subgroupOf H) (K.subgroupOf H) :=
    (isSylowOf_subgroupOf_iff hRH hKH).mpr hR
  obtain ⟨k, hk, ⟨e⟩⟩ := hRd
  have hRd' : IsDihedralTwoGroup (R.subgroupOf H) :=
    ⟨k, hk, ⟨(subgroupOfEquivOfLe hRH).trans e⟩⟩
  have hcardR : Nat.card R = 2 * 2 ^ (k - 1) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcardR' : Nat.card (R.subgroupOf H) = Nat.card R := card_subgroupOf hRH
  have h4R : 4 ∣ Nat.card R := by
    rw [hcardR]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    exact ⟨2 ^ j, by rw [show j + 2 - 1 = j + 1 by omega, pow_succ]; ring⟩
  have hfalse : Asc76Theorem3Conclusion (K.subgroupOf H) (R.subgroupOf H) → False := by
    rintro (hn' | ⟨hsmall, -, -, hsolv⟩ | ⟨U, hUR, -, hUidx, hUc⟩)
    · exact hHN (le_normalizer_of_normal_subgroupOf hKH hn')
    · exact hHN ((le_centralizer_of_outer_solvable hA.1 hAH (le_centralizer_iff.mpr le_rfl)
        (outer_solvable_of_small hsmall) hsolv).trans le_normalizer)
    · exact hHN (le_normalizer_of_cyclic hA hR.le hRH h4R hAH hUR hUidx hUc)
  have h4 : Nat.card R = 4 := by
    by_contra h4
    have hgt : 4 < Nat.card (R.subgroupOf H) := by
      rw [hcardR']
      obtain ⟨c, hc⟩ := h4R
      have hpos : 0 < Nat.card R := Nat.card_pos
      omega
    exact hfalse (h3L H (K.subgroupOf H) hK' hG' hO' (R.subgroupOf H) hR' hRd' hgt)
  refine ⟨h4, ?_, ?_⟩
  ·
    have hk2 : k = 2 := by
      have h1 : 2 ^ (k - 1) = 2 ^ 1 := by omega
      have h2 := Nat.pow_right_injective le_rfl h1
      omega
    subst hk2
    have hcomm : ∀ a b : DihedralGroup (2 ^ (2 - 1)), a * b = b * a := by decide
    have hsq : ∀ a : DihedralGroup (2 ^ (2 - 1)), a ^ 2 = 1 := by decide
    refine ⟨⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, hcomm])⟩⟩, fun x hx => ?_⟩
    have h1 : (⟨x, hx⟩ : R) ^ 2 = 1 := e.injective (by rw [map_pow, hsq, map_one])
    simpa using congrArg Subtype.val h1
  ·
    by_cases hWC : ∃ S : Subgroup H, IsSylowOf 2 S ⊤ ∧ R.subgroupOf H ≤ S ∧
        ∀ x : H, rightConjugate (R.subgroupOf H) x ≤ S →
          rightConjugate (R.subgroupOf H) x = R.subgroupOf H
    · exact (hfalse (h3F H (K.subgroupOf H) hK' hG' hO' (R.subgroupOf H) hR' hRd'
        (by rw [hcardR', h4]) hWC)).elim
    · obtain ⟨x, hxN, hxle⟩ := exists_overlap_of_not_weaklyClosed hR hKH hWC
      have hsyl : IsSylowOf 2 (rightConjugate R x) (rightConjugate K x) :=
        AschbacherTheorem3.isSylowOf_rightConjugate hR x
      refine ⟨x, by rwa [← hNK], rightConjugate R x, ?_, hsyl⟩
      exact hsyl.of_le (le_inf hsyl.le (by rw [← hNK]; exact hxle)) inf_le_left

end CFSG.ComponentClassification.Asc76.Sec5
