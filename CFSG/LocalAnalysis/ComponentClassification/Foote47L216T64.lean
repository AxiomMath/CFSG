module

public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldProjection
import CFSG.CGT.Timmesfeld75.L2Aut
import CFSG.GH74.GLS.C3.Layer2.GenLemmas
import CFSG.GroupTheory.ElementaryAbelianBasis
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.ElemAbelianRank
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
public import CFSG.Open.LocalVocabulary

public noncomputable section

namespace CFSG.ComponentClassification.Foote47L216

open Subgroup CFSG.CGT.Timmesfeld75
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

private theorem fieldAction_utriElt {F : Type} [Field F] (σ : RingAut F) (x : F) :
    sl2FieldAction σ (utriElt x) = utriElt (σ x) :=
  sl2FieldAut_utriElt σ x

private theorem fieldAction_mem_utri {F : Type} [Field F] (σ : RingAut F)
    {x : SL(2, F)} (hx : x ∈ utri F) : sl2FieldAction σ x ∈ utri F := by
  obtain ⟨t, rfl⟩ := mem_utri_iff.mp hx
  rw [fieldAction_utriElt]
  exact utriElt_mem_utri _

private def upperSemilinear (F : Type) [Field F] : Subgroup (Gamma F) where
  carrier := {a | a.left ∈ utri F}
  one_mem' := (utri F).one_mem
  mul_mem' ha hb := (utri F).mul_mem ha (fieldAction_mem_utri _ hb)
  inv_mem' ha := fieldAction_mem_utri _ ((utri F).inv_mem ha)

private theorem card_upperSemilinear {F : Type} [Field F] :
    Nat.card (upperSemilinear F) = Nat.card F * Nat.card (RingAut F) := by
  let e : upperSemilinear F ≃ utri F × RingAut F :=
    { toFun := fun a => (⟨a.val.left, a.property⟩, a.val.right)
      invFun := fun a => ⟨⟨a.1, a.2⟩, a.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_utri]

private abbrev F16 := GaloisField 2 4

private theorem card_field : Nat.card F16 = 2 ^ 4 := GaloisField.card 2 4 (by decide)

private theorem card_upper : Nat.card (upperSemilinear F16) = 64 := by
  rw [card_upperSemilinear, card_field, (ringAut_card_and_cyclic card_field).1]
  norm_num

private theorem upper_isPGroup : IsPGroup 2 (upperSemilinear F16) :=
  IsPGroup.of_card (n := 6) (by rw [card_upper]; norm_num)

private theorem upper_index : (upperSemilinear F16).index = 255 := by
  have hc := (upperSemilinear F16).index_mul_card
  rw [card_upper, SemidirectProduct.card, card_sl2, card_field,
    (ringAut_card_and_cyclic card_field).1] at hc
  norm_num at hc
  omega

private def upperSylow : Sylow 2 (Gamma F16) :=
  upper_isPGroup.toSylow (by rw [upper_index]; decide)

private theorem inner_mem_utri {F : Type} [Field F] {a : Gamma F}
    (ha : a ∈ upperSemilinear F) (hi : a ∈ linearKernel F) :
    ∃ x : F, a = SemidirectProduct.inl (utriElt x) := by
  obtain ⟨x, hx⟩ := mem_utri_iff.mp ha
  refine ⟨x, SemidirectProduct.ext hx ?_⟩
  exact mem_linearKernel_iff a |>.mp hi

private theorem inner_commute {F : Type} [Field F] {a b : Gamma F}
    (ha : a ∈ upperSemilinear F) (hb : b ∈ upperSemilinear F)
    (hai : a ∈ linearKernel F) (hbi : b ∈ linearKernel F) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := inner_mem_utri ha hai
  obtain ⟨y, rfl⟩ := inner_mem_utri hb hbi
  rw [← map_mul, ← map_mul, ← utriElt_add, ← utriElt_add, add_comm]

private theorem outer_right_eq {F : Type} [Field F] [IsCyclic (RingAut F)]
    {a b : Gamma F} (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hai : a ∉ linearKernel F) (hbi : b ∉ linearKernel F) : a.right = b.right := by
  have har : a.right ≠ 1 := by simpa using hai
  have hbr : b.right ≠ 1 := by simpa using hbi
  have har2 : a.right ^ 2 = 1 := by
    simpa [pow_two] using congrArg SemidirectProduct.right ha2
  have hbr2 : b.right ^ 2 = 1 := by
    simpa [pow_two] using congrArg SemidirectProduct.right hb2
  exact cyclic_involutions_eq _ _ (orderOf_eq_prime har2 har) (orderOf_eq_prime hbr2 hbr)

private theorem outer_commute {F : Type} [Field F] [CharP F 2]
    [IsCyclic (RingAut F)] {a b : Gamma F}
    (ha : a ∈ upperSemilinear F) (hb : b ∈ upperSemilinear F)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hai : a ∉ linearKernel F) (hbi : b ∉ linearKernel F) : a * b = b * a := by
  have hr := outer_right_eq ha2 hb2 hai hbi
  obtain ⟨x, hx⟩ := mem_utri_iff.mp ha
  obtain ⟨y, hy⟩ := mem_utri_iff.mp hb
  have hfixa : sl2FieldAction a.right a.left = a.left := by
    apply mul_left_cancel (a := a.left)
    have h := congrArg SemidirectProduct.left ha2
    simpa [pow_two, hx, ← utriElt_add, CharTwo.add_self_eq_zero, utriElt_zero] using h
  have hfixb : sl2FieldAction b.right b.left = b.left := by
    apply mul_left_cancel (a := b.left)
    have h := congrArg SemidirectProduct.left hb2
    simpa [pow_two, hy, ← utriElt_add, CharTwo.add_self_eq_zero, utriElt_zero] using h
  apply SemidirectProduct.ext
  · change a.left * sl2FieldAction a.right b.left =
      b.left * sl2FieldAction b.right a.left
    rw [hr, hfixb, ← hr, hfixa, hx, hy, ← utriElt_add, ← utriElt_add, add_comm]
  · change a.right * b.right = b.right * a.right
    rw [hr]

private theorem inner_elementary {F : Type} [Field F] [CharP F 2]
    {H : Subgroup (Gamma F)} (hH : H ≤ upperSemilinear F) :
    CFSG.Open.IsElemAbelian 2 (H ⊓ linearKernel F) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (inner_commute (hH a.2.1) (hH b.2.1)
    a.2.2 b.2.2)⟩⟩, ?_⟩
  intro a ha
  obtain ⟨x, rfl⟩ := inner_mem_utri (hH ha.1) ha.2
  rw [← map_pow, pow_two, ← utriElt_add, CharTwo.add_self_eq_zero, utriElt_zero, map_one]

private theorem mixed_elementary_centralizes_outer {F : Type} [Field F] [CharP F 2]
    [IsCyclic (RingAut F)] {E : Subgroup (Gamma F)}
    (hE : CFSG.Open.IsElemAbelian 2 E) (hEP : E ≤ upperSemilinear F)
    (e : Gamma F) (heE : e ∈ E) (hei : e ∉ linearKernel F)
    {h : Gamma F} (hhP : h ∈ upperSemilinear F) (hh2 : h ^ 2 = 1)
    (hhi : h ∉ linearKernel F) : E ≤ centralizer ({h} : Set (Gamma F)) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  by_cases hxi : x ∈ linearKernel F
  · have hp : e * x ∉ linearKernel F := by
      simpa [mem_linearKernel_iff, (mem_linearKernel_iff x).mp hxi] using hei
    have hep := outer_commute (hEP (E.mul_mem heE hx)) hhP
      (hE.2 _ (E.mul_mem heE hx)) hh2 hp hhi
    have heh := outer_commute (hEP heE) hhP (hE.2 e heE) hh2 hei hhi
    apply mul_left_cancel (a := e)
    calc e * (x * h) = (e * x) * h := by group
      _ = h * (e * x) := hep
      _ = (h * e) * x := by group
      _ = (e * h) * x := by rw [heh]
      _ = e * (h * x) := by group
  · exact outer_commute (hEP hx) hhP (hE.2 x hx) hh2 hxi hhi

private theorem mixed_elementary_centralizes_inner {F : Type} [Field F]
    [IsCyclic (RingAut F)] {E : Subgroup (Gamma F)}
    (hE : CFSG.Open.IsElemAbelian 2 E) (hEP : E ≤ upperSemilinear F)
    (e : Gamma F) (heE : e ∈ E) (hei : e ∉ linearKernel F)
    {h : Gamma F} (hhP : h ∈ upperSemilinear F) (hhi : h ∈ linearKernel F)
    (heh : e * h = h * e) : E ≤ centralizer ({h} : Set (Gamma F)) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  by_cases hxi : x ∈ linearKernel F
  · exact inner_commute (hEP hx) hhP hxi hhi
  · have hr := outer_right_eq (hE.2 e heE) (hE.2 x hx) hei hxi
    have hp : e * x ∈ linearKernel F := by
      rw [mem_linearKernel_iff]
      have he2 := congrArg SemidirectProduct.right (hE.2 e heE)
      simpa [pow_two, hr] using he2
    have heph := inner_commute (hEP (E.mul_mem heE hx)) hhP hp hhi
    apply mul_left_cancel (a := e)
    calc e * (x * h) = (e * x) * h := by group
      _ = h * (e * x) := heph
      _ = (h * e) * x := by group
      _ = (e * h) * x := by rw [heh]
      _ = e * (h * x) := by group

private theorem three_le_rank_adjoin {G : Type} [Group G] [Finite G]
    {A H : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A)
    (hAH : A ≤ H) {h : G} (hhH : h ∈ H) (hh2 : h ^ 2 = 1) (hhA : h ∉ A)
    (hAh : ∀ a ∈ A, a * h = h * a) :
    3 ≤ CFSG.pRank 2 ↥(H ⊓ centralizer ({h} : Set G)) := by
  let D := A ⊔ zpowers h
  have hDc : D ≤ H ⊓ centralizer ({h} : Set G) := by
    refine sup_le (le_inf hAH ?_) (zpowers_le.mpr ⟨hhH, ?_⟩)
    · intro a ha
      exact mem_centralizer_singleton_iff.mpr (hAh a ha)
    · simp [mem_centralizer_singleton_iff]
  have hhC : h ∈ centralizer (A : Set G) := mem_centralizer_iff.mpr hAh
  have hD : CFSG.Open.IsElemAbelian 2 D :=
    hA.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hh2)
      (fun a ha b hb => ((le_centralizer_iff.mpr (zpowers_le.mpr hhC) ha) b hb).symm)
  have hcard : Nat.card D = 2 * Nat.card A :=
    CFSG.GroupTheory.card_sup_zpowers_of_sq_mem
      (centralizer_le_normalizer _ hhC) (by rw [← pow_two, hh2]; exact A.one_mem) hhA
  have hD3 : 3 ≤ CFSG.Open.pRank 2 D := by
    have hr := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hD
    have hp : 2 ^ 3 ≤ 2 ^ CFSG.Open.pRank 2 D := by omega
    exact (Nat.pow_le_pow_iff_right one_lt_two).mp hp
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact hD3.trans (CFSG.SectionRank.pRank_mono one_lt_two hDc)

private theorem three_le_rank_of_eight {G : Type} [Group G] [Finite G]
    {E H : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) (hEH : E ≤ H)
    (hE8 : Nat.card E = 8) : 3 ≤ CFSG.pRank 2 H := by
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact CFSG.SectionRank.le_pRank one_lt_two hEH hE (by rw [hE8]; norm_num)

private theorem mixed_intersection_card {F : Type} [Field F] [IsCyclic (RingAut F)]
    {E : Subgroup (Gamma F)} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hE8 : Nat.card E = 8) (e : Gamma F) (he : e ∈ E)
    (hei : e ∉ linearKernel F) : Nat.card ↥(E ⊓ linearKernel F) = 4 := by
  let : CFSG.IsElementaryAbelian 2 E := hE.isElementaryAbelian
  have hc := outer_elementary_card_factor E (fun hle => hei (hle he))
  have hi : Nat.card (linearIntersection E) = Nat.card ↥(E ⊓ linearKernel F) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hi, hE8] at hc
  omega

private theorem three_le_rank_centralizer_of_le_upper
    (H : Subgroup (Gamma F16)) (hHP : H ≤ upperSemilinear F16)
    (hrank : 3 ≤ CFSG.pRank 2 H) (h : Gamma F16) (hhH : h ∈ H)
    (hh2 : h ^ 2 = 1) :
    3 ≤ CFSG.pRank 2 ↥(H ⊓ centralizer ({h} : Set (Gamma F16))) := by
  let : IsCyclic (RingAut F16) := (ringAut_card_and_cyclic card_field).2
  have hrank' : 3 ≤ CFSG.Open.pRank 2 H := by
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at hrank
  obtain ⟨E, hEH, hE, hE8⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hrank'
  norm_num at hE8
  have hEP : E ≤ upperSemilinear F16 := hEH.trans hHP
  by_cases hEi : E ≤ linearKernel F16
  · by_cases hhi : h ∈ linearKernel F16
    · apply three_le_rank_of_eight hE (le_inf hEH ?_) hE8
      intro e he
      exact mem_centralizer_singleton_iff.mpr
        (inner_commute (hEP he) (hHP hhH) (hEi he) hhi)
    · let V := H ⊓ linearKernel F16
      have hV : CFSG.Open.IsElemAbelian 2 V := inner_elementary hHP
      let : CFSG.IsElementaryAbelian 2 V := hV.isElementaryAbelian
      have hE8V : 8 ≤ Nat.card V := hE8 ▸ card_le_of_le (le_inf hEH hEi)
      have hb := CFSG.GH74.GLS.C3.Layer2.card_le_sq_card_fixed V
        (a := h) (fun v hv => ⟨H.mul_mem (H.mul_mem hhH hv.1) (H.inv_mem hhH),
          by
            change h * v * h⁻¹ ∈ linearKernel F16
            rw [mem_linearKernel_iff]
            simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
              (mem_linearKernel_iff v).mp hv.2, mul_one, mul_inv_cancel]⟩)
        (fun v _ => by rw [hh2]; simp)
      let A := V ⊓ centralizer ({h} : Set (Gamma F16))
      have hA : CFSG.Open.IsElemAbelian 2 A := hV.mono inf_le_left
      have hA3 : 3 ≤ Nat.card A := by dsimp [A]; nlinarith
      have hA4 : 4 ≤ Nat.card A := by
        rcases hA.isPGroup.card_eq_or_dvd with hc | hc <;> omega
      apply three_le_rank_adjoin hA hA4 (inf_le_left.trans inf_le_left)
        hhH hh2 (fun ha => hhi ha.1.2)
      intro a ha
      exact mem_centralizer_singleton_iff.mp ha.2
  · obtain ⟨e, heE, hei⟩ : ∃ e ∈ E, e ∉ linearKernel F16 := by
      simpa only [SetLike.le_def, not_forall, exists_prop] using hEi
    by_cases hhi : h ∈ linearKernel F16
    · by_cases heh : e * h = h * e
      · exact three_le_rank_of_eight hE
          (le_inf hEH (mixed_elementary_centralizes_inner hE hEP e heE hei
            (hHP hhH) hhi heh)) hE8
      · have hi4 := mixed_intersection_card hE hE8 e heE hei
        have hi : CFSG.Open.IsElemAbelian 2 (E ⊓ linearKernel F16) := hE.mono inf_le_left
        apply three_le_rank_adjoin hi (by rw [hi4]) (inf_le_left.trans hEH) hhH hh2
          (fun hh => heh (hE.comm heE hh.1))
        intro a ha
        exact inner_commute (hEP ha.1) (hHP hhH) ha.2 hhi
    · exact three_le_rank_of_eight hE
        (le_inf hEH (mixed_elementary_centralizes_outer hE hEP e heE hei
          (hHP hhH) hh2 hhi)) hE8

private theorem three_le_rank_centralizer_gamma
    (H : Subgroup (Gamma F16)) (hH : IsPGroup 2 H)
    (hrank : 3 ≤ CFSG.pRank 2 H) (h : Gamma F16) (hhH : h ∈ H)
    (hh : orderOf h = 2) :
    3 ≤ CFSG.pRank 2 ↥(H ⊓ centralizer ({h} : Set (Gamma F16))) := by
  obtain ⟨Q, hHQ⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conjSubgroup_eq_of_sylow Q upperSylow
  let e := MulAut.conj g
  have hHP : H.map e.toMonoidHom ≤ upperSemilinear F16 := by
    change (Q : Subgroup (Gamma F16)).map e.toMonoidHom = upperSemilinear F16 at hg
    exact (map_mono hHQ).trans hg.le
  have hr : 3 ≤ CFSG.pRank 2 (H.map e.toMonoidHom) := by
    rwa [← CFSG.pRank_congr_of_mulEquiv (H.equivMapOfInjective _ e.injective) 2]
  have hc := three_le_rank_centralizer_of_le_upper (H.map e.toMonoidHom) hHP hr
    (e h) (mem_map_of_mem e.toMonoidHom hhH)
    (by simpa only [hh, map_pow, map_one] using congrArg e (pow_orderOf_eq_one h))
  have hm : (H ⊓ centralizer ({h} : Set (Gamma F16))).map e.toMonoidHom =
      H.map e.toMonoidHom ⊓ centralizer ({e h} : Set (Gamma F16)) := by
    rw [Subgroup.map_inf _ _ _ e.injective,
      CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv, Set.image_singleton]
    rfl
  rwa [← hm, ← CFSG.pRank_congr_of_mulEquiv
    ((H ⊓ centralizer ({h} : Set (Gamma F16))).equivMapOfInjective _ e.injective) 2] at hc

theorem three_le_pRank_centralizer_of_isPGroup
    {L : Type} [Group L] [Finite L]
    (eL : L ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4))
    (H : Subgroup (MulAut L)) (hH : IsPGroup 2 H)
    (hrank : 3 ≤ CFSG.pRank 2 ↥H)
    (h : MulAut L) (hhH : h ∈ H) (hh : orderOf h = 2) :
    3 ≤ CFSG.pRank 2
      ↥(H ⊓ Subgroup.centralizer ({h} : Set (MulAut L))) := by
  let e : MulAut L ≃* Gamma F16 :=
    (MulAut.congr (eL.trans sl2EquivPSL2.symm)).trans
      (gammaEquivMulAut (by decide : 1 ≤ 4) card_field).symm
  have hHp : IsPGroup 2 (H.map e.toMonoidHom) := hH.map _
  have hr : 3 ≤ CFSG.pRank 2 (H.map e.toMonoidHom) := by
    rwa [← CFSG.pRank_congr_of_mulEquiv (H.equivMapOfInjective _ e.injective) 2]
  have hc := three_le_rank_centralizer_gamma (H.map e.toMonoidHom) hHp hr
    (e h) (mem_map_of_mem e.toMonoidHom hhH) (by rw [e.orderOf_eq, hh])
  have hm : (H ⊓ centralizer ({h} : Set (MulAut L))).map e.toMonoidHom =
      H.map e.toMonoidHom ⊓ centralizer ({e h} : Set (Gamma F16)) := by
    rw [Subgroup.map_inf _ _ _ e.injective,
      CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv, Set.image_singleton]
    rfl
  rwa [← hm, ← CFSG.pRank_congr_of_mulEquiv
    ((H ⊓ centralizer ({h} : Set (MulAut L))).equivMapOfInjective _ e.injective) 2] at hc

end CFSG.ComponentClassification.Foote47L216
