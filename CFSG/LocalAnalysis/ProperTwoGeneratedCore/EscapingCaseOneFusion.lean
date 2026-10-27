module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneEmbedding

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type} [Group G] [Finite G]

structure CaseOneConfig (x : G) (J : Subgroup (EscapingQuotient x)) : Prop where
  bar_not_mem : escapingBar x ∉ J
  involution_mem : ∀ t : EscapingQuotient x, orderOf t = 2 → t ∈ J ∨ escapingBar x * t ∈ J
  conj : ∀ a ∈ J, ∀ b ∈ J, orderOf a = 2 → orderOf b = 2 → IsConj a b
  four : ∃ a ∈ J, ∃ b ∈ J, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ Commute a b

theorem orderOf_mul_eq_two_of_commute {K : Type*} [Group K] {a b : K} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : Commute a b) (hne : a ≠ b) : orderOf (a * b) = 2 := by
  have haa := mul_self_eq_one_of_orderOf_eq_two ha
  have hbb := mul_self_eq_one_of_orderOf_eq_two hb
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, mul_assoc, ← mul_assoc b a b, ← hab.eq, mul_assoc, hbb, mul_one, haa]
  · intro h
    apply hne
    rw [← inv_eq_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right haa]

theorem orderOf_mul_mul_inv {K : Type*} [Group K] (g a : K) :
    orderOf (g * a * g⁻¹) = orderOf a := by
  simpa only [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq a

theorem isConj_mul_left_of_commute {K : Type*} [Group K] {z a b : K}
    (hz : ∀ y : K, Commute y z) (h : IsConj a b) : IsConj (z * a) (z * b) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨c, ?_⟩
  rw [← hc, ← mul_assoc, (hz c).eq]
  group

omit [Finite G] in
theorem isConj_of_mem_involutionPointClass {z w : G} (hw : w ∈ involutionPointClass z) :
    IsConj z w := by
  obtain ⟨g, rfl⟩ := hw
  exact isConj_iff.mpr ⟨g⁻¹, by simp [rightConjugateElem]⟩

section Bar

variable {x : G}

omit [Finite G] in
theorem orderOf_escapingSelf (hx : orderOf x = 2) : orderOf (escapingSelf x) = 2 := by
  rw [Subgroup.orderOf_mk, hx]

omit [Finite G] in
theorem commute_escapingBar (y : EscapingQuotient x) : Commute y (escapingBar x) := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ y
  have h : Commute m (escapingSelf x) :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp m.property)
  exact Commute.map h (escapingMk x)

theorem escapingBar_mul_self (hx : orderOf x = 2) : escapingBar x * escapingBar x = 1 :=
  mul_self_eq_one_of_orderOf_eq_two (escaping_orderOf_mk x (orderOf_escapingSelf hx))

omit [Finite G] in
theorem eq_escapingSelf {a : Subgroup.centralizer ({x} : Set G)} (h : (a : G) = x) :
    a = escapingSelf x :=
  Subtype.ext h

theorem orderOf_bar_mul_mk (hx : orderOf x = 2) {a : Subgroup.centralizer ({x} : Set G)}
    (ha : orderOf a = 2) (hax : (a : G) ≠ x) : orderOf (escapingBar x * escapingMk x a) = 2 := by
  have hb := escapingBar_mul_self hx
  have hā := mul_self_eq_one_of_orderOf_eq_two (escaping_orderOf_mk x ha)
  refine orderOf_eq_prime ?_ ?_
  · calc (escapingBar x * escapingMk x a) ^ 2
        = escapingBar x * (escapingMk x a * escapingBar x) * escapingMk x a := by
          rw [pow_two]; group
      _ = escapingBar x * (escapingBar x * escapingMk x a) * escapingMk x a := by
        rw [(commute_escapingBar (escapingMk x a)).eq]
      _ = (escapingBar x * escapingBar x) * (escapingMk x a * escapingMk x a) := by group
      _ = 1 := by rw [hb, hā, one_mul]
  · intro h
    apply hax
    refine escaping_eq_of_mk_eq_bar (mul_self_eq_one_of_orderOf_eq_two hx)
      (mul_self_eq_one_of_orderOf_eq_two ha) ?_
    rw [← inv_eq_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hb]

end Bar

namespace CaseOneConfig

variable {x : G} {J : Subgroup (EscapingQuotient x)} (hJ : CaseOneConfig x J)
include hJ

theorem isConj_of_mk_mem {a b : Subgroup.centralizer ({x} : Set G)} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (haJ : escapingMk x a ∈ J) (hbJ : escapingMk x b ∈ J) :
    IsConj (a : G) (b : G) :=
  (Subgroup.centralizer ({x} : Set G)).subtype.map_isConj (escaping_isConj_of_isConj_mk x ha hb
    (hJ.conj _ haJ _ hbJ (escaping_orderOf_mk x ha) (escaping_orderOf_mk x hb)))

theorem isConj_of_bar_mul_mk_mem (hx : orderOf x = 2) {a b : Subgroup.centralizer ({x} : Set G)}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (haJ : escapingBar x * escapingMk x a ∈ J)
    (hbJ : escapingBar x * escapingMk x b ∈ J) (hax : (a : G) ≠ x) (hbx : (b : G) ≠ x) :
    IsConj (a : G) (b : G) := by
  have hj := isConj_mul_left_of_commute commute_escapingBar (hJ.conj _ haJ _ hbJ
    (orderOf_bar_mul_mk hx ha hax) (orderOf_bar_mul_mk hx hb hbx))
  rw [← mul_assoc, ← mul_assoc, escapingBar_mul_self hx, one_mul, one_mul] at hj
  exact (Subgroup.centralizer ({x} : Set G)).subtype.map_isConj
    (escaping_isConj_of_isConj_mk x ha hb hj)

variable (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
  (hx : orderOf x = 2) {w : Subgroup.centralizer ({x} : Set G)} (hw : orderOf w = 2)
  (hnc : ¬ IsConj (w : G) x)
include hsimple hnonab hx hw hnc

theorem not_mem_localInvolutionPointHull_of_mk_mem (hwJ : escapingMk x w ∈ J) :
    x ∉ localInvolutionPointHull (w : G) x := by
  obtain ⟨v, hxv, hv2, hvbar⟩ := exists_isConj_mk_ne_bar hsimple hnonab hx
  have hv2' : orderOf v = 2 := by rwa [← Subgroup.orderOf_coe]
  have hvx : (v : G) ≠ x := fun h => hvbar (by rw [eq_escapingSelf h])
  have hvJ : escapingBar x * escapingMk x v ∈ J := by
    rcases hJ.involution_mem _ (escaping_orderOf_mk x hv2') with h | h
    · exact absurd ((hxv.trans (hJ.isConj_of_mk_mem hv2' hw h hwJ)).symm) hnc
    · exact h
  intro hxL
  have hle : localInvolutionPointHull (w : G) x ≤
      (J.comap (escapingMk x)).map (Subgroup.centralizer ({x} : Set G)).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyw, hyM⟩
    have hwy : IsConj (w : G) y := isConj_of_mem_involutionPointClass hyw
    have hy2 : orderOf (⟨y, hyM⟩ : Subgroup.centralizer ({x} : Set G)) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact order_two_of_mem_pointClass (by rwa [Subgroup.orderOf_coe]) hyw
    refine ⟨⟨y, hyM⟩, ?_, rfl⟩
    rcases hJ.involution_mem _ (escaping_orderOf_mk x hy2) with h | h
    · exact h
    · have hyx : y ≠ x := fun h' => hnc (h' ▸ hwy)
      exact absurd (hwy.trans ((hJ.isConj_of_bar_mul_mk_mem hx hy2 hv2' h hvJ hyx hvx).trans
        hxv.symm)) hnc
  obtain ⟨m, hmJ, hmx⟩ := hle hxL
  rw [eq_escapingSelf hmx] at hmJ
  exact hJ.bar_not_mem hmJ

theorem bar_mul_mk_not_mem : escapingBar x * escapingMk x w ∉ J := by
  intro hwJ
  have hwx : (w : G) ≠ x := fun h => hnc (by rw [h])
  obtain ⟨v, hxv, hv2, hvbar⟩ := exists_isConj_mk_ne_bar hsimple hnonab hx
  have hv2' : orderOf v = 2 := by rwa [← Subgroup.orderOf_coe]
  have hvx : (v : G) ≠ x := fun h => hvbar (by rw [eq_escapingSelf h])
  have hvJ : escapingMk x v ∈ J := by
    rcases hJ.involution_mem _ (escaping_orderOf_mk x hv2') with h | h
    · exact h
    · exact absurd ((hxv.trans (hJ.isConj_of_bar_mul_mk_mem hx hv2' hw h hwJ hvx hwx)).symm)
        hnc
  have hcx : ∀ a : Subgroup.centralizer ({x} : Set G), orderOf a = 2 →
      escapingMk x a ∈ J → IsConj x (a : G) :=
    fun a ha haJ => hxv.trans (hJ.isConj_of_mk_mem hv2' ha hvJ haJ)
  have hcw : ∀ a : Subgroup.centralizer ({x} : Set G), orderOf a = 2 →
      escapingBar x * escapingMk x a ∈ J → (a : G) ≠ x → IsConj (w : G) (a : G) :=
    fun a ha haJ hax => hJ.isConj_of_bar_mul_mk_mem hx hw ha hwJ haJ hwx hax
  have hmx : ∀ a : Subgroup.centralizer ({x} : Set G), orderOf a = 2 →
      IsConj x (a : G) → (a : G) ≠ x → escapingMk x a ∈ J := by
    intro a ha hxa hax
    rcases hJ.involution_mem _ (escaping_orderOf_mk x ha) with h | h
    · exact h
    · exact absurd ((hcw a ha h hax).trans hxa.symm) hnc
  obtain ⟨a, haJ, b, hbJ, ha2, hb2, hab, hcomm⟩ := hJ.four
  obtain ⟨r, hr2, hrmk⟩ := escaping_exists_lift x ha2
  obtain ⟨r', hr'2, hrr', hr'mk⟩ := escaping_exists_commuting_lift x hr2 hb2
    (by rw [hrmk]; exact hcomm.symm)
  have hrx : (r : G) ≠ x := by
    intro h
    have h1 : escapingMk x r = escapingBar x := by rw [eq_escapingSelf h]
    exact hJ.bar_not_mem (by rw [← h1, hrmk]; exact haJ)
  have hr'x : (r' : G) ≠ x := by
    intro h
    have h1 : escapingMk x r' = escapingBar x := by rw [eq_escapingSelf h]
    exact hJ.bar_not_mem (by rw [← h1, hr'mk]; exact hbJ)
  have hrr'ne : (r' : G) ≠ (r : G) := fun h => hab (by rw [← hrmk, ← hr'mk, Subtype.ext h])
  have hxr : IsConj x (r : G) := hcx r hr2 (by rw [hrmk]; exact haJ)
  have hxr' : IsConj x (r' : G) := hcx r' hr'2 (by rw [hr'mk]; exact hbJ)
  have hxr'2 : orderOf (escapingSelf x * r') = 2 :=
    orderOf_mul_eq_two_of_commute (orderOf_escapingSelf hx) hr'2
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp r'.property).symm)
      (fun h => hr'x (congrArg Subtype.val h.symm))
  have hwxr' : IsConj (w : G) ((escapingSelf x * r' : Subgroup.centralizer ({x} : Set G)) : G) := by
    refine hcw _ hxr'2 ?_ ?_
    · rw [map_mul, ← mul_assoc, escapingBar_mul_self hx, one_mul, hr'mk]
      exact hbJ
    · intro h
      change x * (r' : G) = x at h
      have h2 : r' = 1 := Subtype.ext (mul_left_cancel (h.trans (mul_one x).symm))
      rw [h2, orderOf_one] at hr'2
      exact absurd hr'2 (by decide)
  obtain ⟨d, hd⟩ := isConj_iff.mp hxr.symm
  have hrxc : Commute (r : G) x := Subgroup.mem_centralizer_singleton_iff.mp r.property
  have hr'xc : Commute (r' : G) (r : G) := congrArg Subtype.val hrr'
  have hu₁M : d * x * d⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    have h := (hrxc.symm.conj d)
    rw [hd] at h
    exact Subgroup.mem_centralizer_singleton_iff.mpr h.eq
  have hr₁M : d * (r' : G) * d⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    have h := (hr'xc.conj d)
    rw [hd] at h
    exact Subgroup.mem_centralizer_singleton_iff.mpr h.eq
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : Subgroup.centralizer ({x} : Set G), (u₁ : G) = d * x * d⁻¹ :=
    ⟨⟨_, hu₁M⟩, rfl⟩
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : Subgroup.centralizer ({x} : Set G), (r₁ : G) = d * (r' : G) * d⁻¹ :=
    ⟨⟨_, hr₁M⟩, rfl⟩
  have hu₁2 : orderOf u₁ = 2 := by
    rw [← Subgroup.orderOf_coe, hu₁, orderOf_mul_mul_inv, hx]
  have hr₁2 : orderOf r₁ = 2 := by
    rw [← Subgroup.orderOf_coe, hr₁, orderOf_mul_mul_inv, Subgroup.orderOf_coe, hr'2]
  have hu₁J : escapingMk x u₁ ∈ J := by
    refine hmx u₁ hu₁2 (by rw [hu₁]; exact isConj_iff.mpr ⟨d, rfl⟩) ?_
    intro h
    apply hrx
    rw [hu₁] at h
    exact (conj_injective (h.trans hd.symm)).symm
  have hr₁J : escapingMk x r₁ ∈ J := by
    refine hmx r₁ hr₁2 (hxr'.trans (by rw [hr₁]; exact isConj_iff.mpr ⟨d, rfl⟩)) ?_
    intro h
    apply hrr'ne
    rw [hr₁] at h
    exact conj_injective (h.trans hd.symm)
  have hprod : ((u₁ * r₁ : Subgroup.centralizer ({x} : Set G)) : G) =
      d * ((escapingSelf x * r' : Subgroup.centralizer ({x} : Set G)) : G) * d⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hu₁, hr₁]
    group
  have hp2 : orderOf (u₁ * r₁) = 2 := by
    rw [← Subgroup.orderOf_coe, hprod, orderOf_mul_mul_inv, Subgroup.orderOf_coe, hxr'2]
  have hwp : IsConj (w : G) ((u₁ * r₁ : Subgroup.centralizer ({x} : Set G)) : G) := by
    rw [hprod]
    exact hwxr'.trans (isConj_iff.mpr ⟨d, rfl⟩)
  have hpJ : escapingMk x (u₁ * r₁) ∈ J := by
    rw [map_mul]
    exact J.mul_mem hu₁J hr₁J
  exact hnc (hwp.trans (hcx _ hp2 hpJ).symm)

theorem not_mem_localInvolutionPointHull : x ∉ localInvolutionPointHull (w : G) x := by
  rcases hJ.involution_mem _ (escaping_orderOf_mk x hw) with h | h
  · exact hJ.not_mem_localInvolutionPointHull_of_mk_mem hsimple hnonab hx hw hnc h
  · exact absurd h (hJ.bar_mul_mk_not_mem hsimple hnonab hx hw hnc)

end CaseOneConfig

end CFSG.ProperTwoGeneratedCore.Assembly
