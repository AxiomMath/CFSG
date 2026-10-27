module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.SectionStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Prelim
public import CFSG.SignalizerFunctorTheorem.Inheritance.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Standard
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Transport

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

omit [Group H] in
theorem not_solStd_fStarSimple {Y : Type} [Group Y] [Finite Y] {N' : Subgroup Y}
    (hN : FStarSimple N') (h : SolStd N') : False := by
  obtain ⟨-, t, ht2, hc⟩ := h
  have htC : t ∈ centralizer (N' : Set Y) := mem_centralizer_iff.2 fun m hm =>
    (mem_centralizer_singleton_iff.1 (hc.1 hm)).symm.symm
  have htN : t ∈ N' := hN.centralizer_le htC
  have hz : (⟨t, htN⟩ : ↥N') ∈ center ↥N' := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 htC g g.2)
  rw [center_eq_bot_of_simple hN.isSimpleGroup hN.nonabelian, Subgroup.mem_bot] at hz
  have h1 : t = 1 := congrArg Subtype.val hz
  rw [h1, orderOf_one] at ht2
  omega

section Link

variable [Finite H] {N : Subgroup H}

theorem link5b_setup {P Q : Subgroup H}
    (hPq : CFSG.IsQuasisimple ↥P) (hPne : P ≠ Q) {T : Subgroup H} {s : H}
    (hQc : IsCompIn Q (centralizer (T : Set H))) (hsT : s ^ 2 ∈ T)
    (hPc : IsCompIn P (centralizer ((T ⊔ zpowers s : Subgroup H) : Set H)))
    (hincl : P ≤ Q ⊔ Q.map (MulAut.conj s).toMonoidHom) (h5b : Sol78Link5b Q P s) :
    s ∈ normalizer (Q : Set H) ∧ P ≤ Q ∧ s ^ 2 ∈ centralizer (Q : Set H) ∧
      s ∈ centralizer (P : Set H) ∧ s ∉ centralizer (Q : Set H) := by
  have hs : s ∈ normalizer (Q : Set H) :=
    Solomon78.mem_normalizer_iff_map_conj_eq.2 h5b.1.symm
  have hPQ : P ≤ Q := by
    have := hincl
    rw [← h5b.1, sup_idem] at this
    exact this
  have hTQ : T ≤ centralizer (Q : Set H) := fun t ht =>
    mem_centralizer_iff.2 fun q hq => (mem_centralizer_iff.1 (hQc.1 hq) t ht).symm
  have hsP : s ∈ centralizer (P : Set H) := mem_centralizer_iff.2 fun p hp =>
    (mem_centralizer_iff.1 (hPc.1 hp) s (mem_sup_right (mem_zpowers s))).symm
  refine ⟨hs, hPQ, hTQ hsT, hsP, ?_⟩
  intro hsc
  have hQle : Q ≤ centralizer ((T ⊔ zpowers s : Subgroup H) : Set H) := by
    intro q hq
    refine mem_centralizer_iff.2 fun x hx => ?_
    have hxQ : x ∈ centralizer (Q : Set H) := by
      have hle : T ⊔ zpowers s ≤ centralizer (Q : Set H) :=
        sup_le hTQ (by rw [zpowers_le]; exact hsc)
      exact hle hx
    exact (mem_centralizer_iff.1 hxQ q hq).symm
  have hQc' : IsCompIn Q (centralizer ((T ⊔ zpowers s : Subgroup H) : Set H)) :=
    isCompIn_of_le hQc hQle (by
      intro x hx
      exact mem_centralizer_iff.2 fun t ht => (mem_centralizer_iff.1 hx t
        ((le_sup_left : T ≤ T ⊔ zpowers s) ht)))
  exact not_forall_commute_of_isQuasisimple hPq fun a ha b hb =>
    hPc.commute_of_ne hQc' hPne a ha b (hPQ hb)

omit [Finite H] in
theorem secStd_le_inn {P Q : Subgroup H} {s : H} (hs : s ∈ normalizer (Q : Set H)) (hPQ : P ≤ Q) :
    secStd Q P hs ≤ (innSub Q).subgroupOf (secGrp Q hs) := by
  rintro z ⟨x, hx, rfl⟩
  have hxQ : (x : H) ∈ Q := hPQ hx
  refine ⟨⟨(x : H), hxQ⟩, ?_⟩
  ext q
  show ((MulAut.conj (⟨(x : H), hxQ⟩ : ↥Q) q : ↥Q) : H) = ((secPre Q hs x q : ↥Q) : H)
  rw [secPre_apply]
  simp [MulAut.conj_apply]

theorem cqCard_lt_of_link5b {P Q : Subgroup H}
    (hQq : CFSG.IsQuasisimple ↥Q) (hPq : CFSG.IsQuasisimple ↥P) (hPne : P ≠ Q)
    {T : Subgroup H} {s : H} (hQc : IsCompIn Q (centralizer (T : Set H))) (hsT : s ^ 2 ∈ T)
    (hPc : IsCompIn P (centralizer ((T ⊔ zpowers s : Subgroup H) : Set H)))
    (hincl : P ≤ Q ⊔ Q.map (MulAut.conj s).toMonoidHom) (h5b : Sol78Link5b Q P s) :
    Nat.card (↥P ⧸ center ↥P) < Nat.card (↥Q ⧸ center ↥Q) := by
  obtain ⟨hs, hPQ, hs2, hsP, hsQ⟩ := link5b_setup hPq hPne hQc hsT hPc hincl h5b
  have hstd := secStd_stdBare Q P hs hPQ h5b.2
  have hsol := secStd_solStd Q P hs hPQ hPq hstd hs2 hsQ hsP
  have hFS := secGrp_fStarSimple Q hs hQq
  have hle := secStd_le_inn hs hPQ
  have hne : secStd Q P hs ≠ (innSub Q).subgroupOf (secGrp Q hs) := fun h =>
    not_solStd_fStarSimple hFS (h ▸ hsol)
  have hlt : secStd Q P hs < (innSub Q).subgroupOf (secGrp Q hs) := lt_of_le_of_ne hle hne
  have h1 : Nat.card ↥(secStd Q P hs) < Nat.card ↥((innSub Q).subgroupOf (secGrp Q hs)) :=
    Subgroup.card_lt_of_lt hlt
  have h2 : Nat.card ↥((innSub Q).subgroupOf (secGrp Q hs)) = Nat.card (↥Q ⧸ center ↥Q) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (innSub_le_secGrp Q hs)).toEquiv).trans
      (Nat.card_congr (innSubEquiv Q).toEquiv).symm
  have hq' := secStd_quasisimple Q P hs hPQ hPq
  obtain ⟨e⟩ := secStd_cqEquiv Q P hs hPQ hPq
  have h3 : Nat.card (↥P ⧸ center ↥P) = Nat.card (↥(secStd Q P hs) ⧸ center ↥(secStd Q P hs)) :=
    Nat.card_congr e.toEquiv
  have h4 : Nat.card (↥(secStd Q P hs) ⧸ center ↥(secStd Q P hs)) ≤
      Nat.card ↥(secStd Q P hs) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(secStd Q P hs))
    have hpos : 0 < Nat.card (center ↥(secStd Q P hs)) := Nat.card_pos
    nlinarith
  omega

omit [Finite H] in
theorem secGrp_isSectionOf (Q : Subgroup H) {s : H} (hs : s ∈ normalizer (Q : Set H)) :
    CFSG.SignalizerFunctorTheorem.IsSectionOf ↥(secGrp Q hs) H :=
  ⟨Q ⊔ zpowers s, (secPre Q hs).rangeRestrict, (secPre Q hs).rangeRestrict_surjective⟩

theorem link5b_section {N : Subgroup H} (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {P Q : Subgroup H}
    (hQq : CFSG.IsQuasisimple ↥Q) (hQne : Q ≠ N) (hPq : CFSG.IsQuasisimple ↥P) (hPne : P ≠ Q)
    {T : Subgroup H} {s : H} (hQc : IsCompIn Q (centralizer (T : Set H))) (hsT : s ^ 2 ∈ T)
    (hPc : IsCompIn P (centralizer ((T ⊔ zpowers s : Subgroup H) : Set H)))
    (hincl : P ≤ Q ⊔ Q.map (MulAut.conj s).toMonoidHom) (h5b : Sol78Link5b Q P s) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (N' P' : Subgroup Y), Nat.card Y < Nat.card H ∧
      CFSG.SignalizerFunctorTheorem.IsSectionOf Y H ∧ FStarSimple N' ∧ N'.index ≤ 2 ∧
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y ∧ SolStd P' ∧ CFSG.IsQuasisimple ↥P' ∧
      Nonempty ((↥P ⧸ center ↥P) ≃* (↥P' ⧸ center ↥P')) ∧
      Nonempty ((↥Q ⧸ center ↥Q) ≃* ↥N') ∧
      ∃ π : ↥P →* ↥P', Function.Surjective π ∧ π.ker ≤ center ↥P ∧
        ∀ x ∈ π.ker, ((x : ↥P) : H) ∈ centralizer (Q : Set H) := by
  have := hN.normal
  obtain ⟨hs, hPQ, hs2, hsP, hsQ⟩ := link5b_setup hPq hPne hQc hsT hPc hincl h5b
  have hQN : Q ≤ N := le_of_perfect_of_index_le_two hidx hQq.1
  have hstd := secStd_stdBare Q P hs hPQ h5b.2
  have hle := innSub_le_secGrp Q hs
  exact ⟨↥(secGrp Q hs), inferInstance, inferInstance, (innSub Q).subgroupOf (secGrp Q hs),
    secStd Q P hs, secGrp_card_lt Q hs hN hQq hQN hQne hs2, secGrp_isSectionOf Q hs,
    secGrp_fStarSimple Q hs hQq,
    secGrp_index_le_two Q hs hs2, secGrp_kProper Q hs hkp,
    secStd_solStd Q P hs hPQ hPq hstd hs2 hsQ hsP, secStd_quasisimple Q P hs hPQ hPq,
    secStd_cqEquiv Q P hs hPQ hPq,
    ⟨(innSubEquiv Q).trans (Subgroup.subgroupOfEquivOfLe hle).symm⟩,
    secStdHom Q P hs hPQ, secStdHom_surjective Q P hs hPQ, secStdHom_ker_le Q P hs hPQ,
    fun x hx => (rangeRestrict_eq_one_iff Q hs _).1 (congrArg Subtype.val hx)⟩

end Link

end CFSG.EvenSporadicStandard.Induction.Hyp
