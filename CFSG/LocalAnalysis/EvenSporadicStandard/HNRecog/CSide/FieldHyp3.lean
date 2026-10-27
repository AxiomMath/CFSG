module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.SetupModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.FreeSwap

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.CSide
open CFSG.EvenSporadicStandard.HNRecog.Fpf
open CFSG.RankThree.Literature.FSmith
open Module Subgroup
open scoped commutatorElement

private theorem ds_isPGroup_zpowers_of_sq_eq_one {C : Type*} [Group C] {t : C}
    (ht2 : t ^ 2 = 1) : IsPGroup 2 ↥(Subgroup.zpowers t) := by
  rw [isPGroup_iff_orderOf_dvd_pow]
  intro x
  refine ⟨1, ?_⟩
  simpa using dvd_trans (orderOf_dvd_of_mem_zpowers x.2)
    (orderOf_dvd_iff_pow_eq_one.mpr ht2)

theorem cSideFacts_hyp3_of_free :
    ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → CIrreducible C Q →
      ∀ t : C, t ∉ commutator C → t ^ 2 = 1 →
        Nat.card {q : C // q ∈ Q ∧ ⁅q, t⁆ ∈ centerOf Q} ≤ 2 ^ 5 →
          ∃ T : Sylow 2 C, t ∈ T ∧ ∃ x ∈ Q,
            (∀ s ∈ (T : Subgroup C) ⊓ commutator C, ⁅x, s⁆ ∈ centerOf Q) ∧
              ⁅t, x⁆ ∉ centerOf Q := by
  intro C _ Q _ hE hI t ht ht2 hcard
  haveI hQn : Q.Normal := inferInstance
  have hC : WeakHyp C Q := WeakHyp.of_cIrreducible hE hI
  haveI : Finite Q := hC.finite_Q
  haveI : Finite C := hC.finite
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hC.isExtraspecialPGroup
  obtain ⟨S⟩ := hC.nonempty_setup
  have M : CSideModel (extraspecialQuadForm hC.isExtraspecialPGroup) S.σ :=
    CSideSetup.model hC S
  obtain ⟨ω, hωcomm, hωpoly, hωb⟩ := M.omega
  have ht2' : (t : C ⧸ Q) ^ 2 = 1 := by
    change (QuotientGroup.mk' Q t) ^ 2 = 1
    rw [← map_pow (QuotientGroup.mk' Q) t 2, ht2, map_one]
  have hfree : cSideFreeSwap (extraspecialQuadForm hC.isExtraspecialPGroup) S.σ
      (conjLinEquiv hQn t) :=
    CSideSetup.cSideFreeSwap_of_card_le hC S ht ht2' hcard
  obtain ⟨T, hT⟩ := IsPGroup.exists_le_sylow (ds_isPGroup_zpowers_of_sq_eq_one ht2)
  have htT : t ∈ T := hT (Subgroup.mem_zpowers t)
  let H : Subgroup C := (T : Subgroup C) ⊓ commutator C
  have hH : IsPGroup 2 H := T.isPGroup'.to_inf_left
  let ρH : ↥H →* (Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q)) :=
    (conjLinEquiv hQn).comp H.subtype
  haveI : Finite (Additive (Abelianization Q)) := by
    change Finite (Q ⧸ _root_.commutator Q)
    infer_instance
  have hV : finrank (ZMod 2) (Additive (Abelianization Q)) = 8 := by
    simpa using hC.plus.finrank_quotient
  haveI : Nontrivial (Additive (Abelianization Q)) :=
    Module.nontrivial_of_finrank_pos (by rw [hV]; norm_num)
  obtain ⟨w, hwne, hwfix⟩ := cSide_exists_fixed_of_pGroup hH ρH
  let W : Set (Additive (Abelianization Q)) :=
    {v | ∀ h : ↥H, conjLinEquiv hQn (h : C) v = v}
  have hwW : w ∈ W := by
    intro h
    exact hwfix h
  have hωcomm_apply : ∀ g : A5 × A5, ∀ v : Additive (Abelianization Q),
      S.σ g (ω v) = ω (S.σ g v) := by
    intro g v
    have h := congrArg (fun e : Additive (Abelianization Q) ≃ₗ[ZMod 2]
        Additive (Abelianization Q) => e v) (hωcomm g)
    simpa [LinearEquiv.mul_apply] using h.symm
  have hωW : ∀ v ∈ W, ω v ∈ W := by
    intro v hv h
    have hl : (h : C) ∈ commutator C :=
      (Subgroup.mem_inf.mp (show (h : C) ∈ (T : Subgroup C) ⊓ commutator C from h.2)).2
    have hv' : S.σ (S.θ ⟨(h : C), hl⟩) v = v := by
      rw [← S.rho_eq hl]
      exact hv h
    rw [S.rho_eq hl, hωcomm_apply (S.θ ⟨(h : C), hl⟩) v, hv']
  have h_exists : ∃ x : Additive (Abelianization Q),
      x ∈ W ∧ conjLinEquiv hQn t x ≠ x := by
    by_contra hcon
    have hfixW : ∀ x ∈ W, conjLinEquiv hQn t x = x := by
      intro x hx
      by_contra hne
      exact hcon ⟨x, hx, hne⟩
    have hbw : conjLinEquiv hQn t w = w := hfixW w hwW
    have hbωw : conjLinEquiv hQn t (ω w) = ω w := hfixW (ω w) (hωW w hwW)
    have hωω : ω (ω w) = ω w := by
      have h1 := hωb (conjLinEquiv hQn t) hfree w
      rw [hbωw, hbw] at h1
      exact h1.symm
    have h2 : ω w + ω w = 0 := by
      rw [← two_smul (ZMod 2) (ω w), show (2 : ZMod 2) = 0 from by decide, zero_smul]
    have hw0 : w = 0 := by
      have h1 := hωpoly w
      rw [hωω, h2, zero_add] at h1
      exact h1
    exact hwne hw0
  obtain ⟨x, hxW, hxb⟩ := h_exists
  obtain ⟨x0, rfl⟩ := exists_ofMul_of x
  refine ⟨T, htT, x0, x0.2, ?_, ?_⟩
  · intro s hs
    have hfixs : ((extraspecialConjOrth hC.isExtraspecialPGroup hQn s :
        TauCeti.QuadraticMap.orthogonalGroup (extraspecialQuadForm hC.isExtraspecialPGroup)) :
        Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q))
        (Additive.ofMul (Abelianization.of x0)) =
        Additive.ofMul (Abelianization.of x0) :=
      hxW ⟨s, hs⟩
    have hc : ⁅s, (x0 : C)⁆ ∈ centerOf Q :=
      (extraspecialConjOrth_apply_eq_iff hC.isExtraspecialPGroup s x0).1 hfixs
    show ⁅(x0 : C), s⁆ ∈ centerOf Q
    rw [← commutatorElement_inv]
    exact (centerOf Q).inv_mem hc
  · intro hc
    exact hxb ((extraspecialConjOrth_apply_eq_iff hC.isExtraspecialPGroup t x0).2 hc)

end CFSG.EvenSporadicStandard.HNRecog.Section3
