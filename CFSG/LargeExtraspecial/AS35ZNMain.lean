module

public import CFSG.LargeExtraspecial.AS35ZNIrred
public import CFSG.LargeExtraspecial.AS35ZNSchur

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary

namespace AS35Z

variable {L : Type} [Group L] {D : Set L} {k : ℕ}

theorem exists_commute_of_isTClass (hD : AS35L.IsTClass D) (hk : 2 ≤ k)
    (ψ : L ⧸ center L ≃* PG (k + 2)) {a : L} (ha : a ∈ D) :
    ∃ b ∈ D, b ≠ a ∧ a * b = b * a := by
  have hm : 3 ≤ k + 2 := by omega
  have haDG := hD.mem_DG hk ψ ha
  have hcls := DG_eq_isConj hm (v₀_ne_zero (n := k)) herm_v₀_v₀
  rw [hcls] at haDG
  obtain ⟨c, hc⟩ := isConj_iff.1 (show IsConj (tq (v₀ k)) _ from haDG)
  have hz0 := isoVec_ne_zero hk
  have hz := isoVec_isotropic hk
  have hιz : herm frob (ι k (isoVec hk)) (ι k (isoVec hk)) = 0 := by rw [herm_ι_ι, hz]
  have hιz0 : ι k (isoVec hk) ≠ 0 := fun h0 => hz0 (ι_injective (by rw [h0, map_zero]))
  have heDG : c * tq (ι k (isoVec hk)) * c⁻¹ ∈ DG (k + 2) := by
    have h1 := tq_mem_DG hιz0 hιz
    rw [hcls] at h1 ⊢
    exact IsConj.trans (show IsConj (tq (v₀ k)) _ from h1) (isConj_iff.2 ⟨c, rfl⟩)
  obtain ⟨b, hb, hbe⟩ := hD.exists_eq hk ψ heDG
  have hne : tq (ι k (isoVec hk)) ≠ tq (v₀ k) := by
    intro h1
    obtain ⟨c', hc'⟩ := (tq_eq_tq_iff hm hιz0 hιz v₀_ne_zero herm_v₀_v₀).1 h1
    have := congrArg (π k) hc'
    rw [π_v₀, map_smul, π_ι] at this
    have hc'0 : c' = 0 := (smul_eq_zero.1 this.symm).resolve_right hz0
    rw [hc'0, zero_smul] at hc'
    exact v₀_ne_zero hc'
  refine ⟨b, hb, fun hba => hne ?_, ?_⟩
  · rw [hba, ← hc] at hbe
    exact (mul_left_cancel (mul_right_cancel hbe)).symm
  · refine (hD.commute_iff hk ψ ha hb).2 ?_
    rw [hbe, ← hc]
    calc c * tq (v₀ k) * c⁻¹ * (c * tq (ι k (isoVec hk)) * c⁻¹)
        = c * (tq (ι k (isoVec hk)) * tq (v₀ k)) * c⁻¹ := by
          rw [AS35L.tq_ι_mul_tq_v₀ hz]; group
      _ = c * tq (ι k (isoVec hk)) * c⁻¹ * (c * tq (v₀ k) * c⁻¹) := by group

end AS35Z

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace ZUHyp

variable {k : ℕ} (h : S.ZUHyp k)
include h

theorem irreducible (hloc : ∀ t ∈ S.DbarAsc, ∃ P, S.ZULocal t P) (V : Submodule (ZMod 2) S.Qt)
    (hV : ∀ d ∈ S.DbarAsc, ∀ v ∈ V, (d : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ V) : V = ⊥ ∨ V = ⊤ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hV0, hVtop⟩ := hcon
  obtain ⟨t, ht⟩ := h.nonempty
  set Vp := LinearMap.BilinForm.orthogonal S.q.polarBilin V with hVp
  have hVpinv : ∀ d ∈ S.DbarAsc, ∀ v ∈ Vp, (d : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vp := by
    intro d hd v hv
    rw [hVp, OrthoF2.mem_orthogonal_iff_polar] at hv ⊢
    intro y hy
    have hdd : (d : S.Qt ≃ₗ[ZMod 2] S.Qt) ((d : S.Qt ≃ₗ[ZMod 2] S.Qt) y) = y := by
      change ((d * d : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y = y
      rw [mul_self hd]
      rfl
    rw [← hdd, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup d.2]
    exact hv _ (hV d hd y hy)
  by_cases hrad : V ⊓ Vp = ⊥
  · obtain ⟨x₀, hx₀, hu0, -, horth⟩ := h.exists_point hloc hV hV0 hVtop ht
    have hmem : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ ∈ V ⊓ Vp := by
      refine Submodule.mem_inf.2 ⟨V.sub_mem (hV t ht x₀ hx₀) hx₀, ?_⟩
      rw [hVp, OrthoF2.mem_orthogonal_iff_polar]
      intro y hy
      rw [polar_comm]
      exact horth y hy
    rw [hrad, Submodule.mem_bot] at hmem
    exact hu0 hmem
  · refine h.false_of_isotropic hloc (U := V ⊓ Vp) (fun d hd u hu => ?_) hrad
      (fun htop => hVtop (eq_top_iff.2 (htop ▸ inf_le_left))) (fun x hx y hy => ?_)
    · obtain ⟨huV, huVp⟩ := Submodule.mem_inf.1 hu
      exact Submodule.mem_inf.2 ⟨hV d hd u huV, hVpinv d hd u huVp⟩
    · have hyp := (Submodule.mem_inf.1 hy).2
      rw [hVp, OrthoF2.mem_orthogonal_iff_polar] at hyp
      rw [polar_comm]
      exact hyp x (Submodule.mem_inf.1 hx).1

theorem fourStruct_of (hloc : ∀ t ∈ S.DbarAsc, ∃ P, S.ZULocal t P)
    (J : S.Qt ≃ₗ[ZMod 2] S.Qt) (hJ3 : ∀ v, J (J v) + J v + v = 0) (hJq : ∀ v, S.q (J v) = S.q v)
    (hJD : ∀ a ∈ S.DbarAsc, ∀ v,
      (a : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((a : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) :
    S.FourStruct := by
  have : Nontrivial S.Qt := by
    obtain ⟨t, ht⟩ := h.nonempty
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact (h.isTypeA ht).2.1 (LinearEquiv.ext fun v => Subsingleton.elim _ _)
  set D : Set (Module.End (ZMod 2) S.Qt) :=
    (fun d : S.O => ((d : S.Qt ≃ₗ[ZMod 2] S.Qt) : Module.End (ZMod 2) S.Qt)) '' S.DbarAsc with hD
  have hirr : ∀ W : Submodule (ZMod 2) S.Qt, (∀ d ∈ D, ∀ w ∈ W, d w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    refine h.irreducible hloc W fun d hd w hw => hW _ ⟨d, hd, rfl⟩ w hw
  set Jm : Module.End (ZMod 2) S.Qt := (J : Module.End (ZMod 2) S.Qt) with hJm
  have hJ3' : Jm * Jm + Jm + 1 = 0 := LinearMap.ext fun v => hJ3 v
  have hJc : ∀ d ∈ D, d * Jm = Jm * d := by
    rintro _ ⟨d, hd, rfl⟩
    exact LinearMap.ext fun v => hJD d hd v
  refine ⟨J, hJ3, hJq, hJD, fun m hm => ?_⟩
  set J' : Module.End (ZMod 2) S.Qt :=
    ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) : Module.End (ZMod 2) S.Qt) * Jm *
      (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : Module.End (ZMod 2) S.Qt) with hJ'
  have hmm : ∀ v, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
    intro v
    change ((m * m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
    rw [mul_inv_cancel]
    rfl
  have hJ'3 : J' * J' + J' + 1 = 0 := by
    refine LinearMap.ext fun v => ?_
    simp only [hJ', LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
      LinearMap.zero_apply, LinearEquiv.coe_coe, hJm]
    have e := hJ3 (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
    have e2 : ((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (J (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v))) =
        J (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
      change ((m⁻¹ * m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _ = _
      rw [inv_mul_cancel]
      rfl
    rw [e2]
    have := congrArg (m : S.Qt ≃ₗ[ZMod 2] S.Qt) e
    rwa [map_add, map_add, hmm, map_zero] at this
  have hJ'c : ∀ d ∈ D, d * J' = J' * d := by
    rintro _ ⟨d, hd, rfl⟩
    have hd' : m⁻¹ * d * m ∈ S.DbarAsc := by
      have := conj_mem (S.Mbar.inv_mem hm) hd
      rwa [inv_inv] at this
    refine LinearMap.ext fun v => ?_
    simp only [hJ', Module.End.mul_apply, LinearEquiv.coe_coe, hJm]
    have e1 : (d : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) (J
        (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v))) =
        (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (((m⁻¹ * d * m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (J (((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v))) := by
      change ((d * m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _ =
        ((m * (m⁻¹ * d * m) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _
      congr 2
      group
    rw [e1, hJD _ hd']
    congr 2
    change ((m⁻¹ * d * m * m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      ((m⁻¹ * d : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v
    congr 2
    group
  rcases AS35Z.eq_or_eq_sq_of_commute D hirr hJc hJ'c hJ3' hJ'3 with h1 | h1
  · left
    intro v
    have := congrArg (fun f : Module.End (ZMod 2) S.Qt => f ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) h1
    simp only [hJ', Module.End.mul_apply, LinearEquiv.coe_coe, hJm] at this
    have e2 : ((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
      change ((m⁻¹ * m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
      rw [inv_mul_cancel]
      rfl
    rwa [e2] at this
  · right
    intro v
    have := congrArg (fun f : Module.End (ZMod 2) S.Qt => f ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) h1
    simp only [hJ', Module.End.mul_apply, LinearEquiv.coe_coe, hJm] at this
    have e2 : ((m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
      change ((m⁻¹ * m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
      rw [inv_mul_cancel]
      rfl
    rwa [e2] at this

theorem disjoint_of (J : S.Qt ≃ₗ[ZMod 2] S.Qt) (hJ3 : ∀ v, J (J v) + J v + v = 0)
    (hJD : ∀ a ∈ S.DbarAsc, ∀ v,
      (a : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((a : S.Qt ≃ₗ[ZMod 2] S.Qt) v))
    {a b : S.O} (ha : a ∈ S.DbarAsc) (hb : b ∈ S.DbarAsc) (hab : a ≠ b) :
    commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (b : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  by_contra hne
  obtain ⟨v, hv, hv0⟩ := Submodule.ne_bot_iff _ |>.1 hne
  have hJc : ∀ c ∈ S.DbarAsc, ∀ w ∈ commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt),
      J w ∈ commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro c hc w hw
    obtain ⟨x, rfl⟩ := mem_commSpace.1 hw
    rw [map_sub, ← hJD c hc]
    exact sub_mem_commSpace _ _
  obtain ⟨hva, hvb⟩ := Submodule.mem_inf.1 hv
  have hJv : J v ∈ commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (b : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    Submodule.mem_inf.2 ⟨hJc a ha v hva, hJc b hb v hvb⟩
  have hJv1 : J v ≠ v := by
    intro h1
    have e := hJ3 v
    rw [h1, h1] at e
    apply hv0
    have h2 : v + v = 0 := by
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rw [h2, zero_add] at e
    exact e
  have hJv0 : J v ≠ 0 := fun h0 => hv0 (J.injective (by rw [h0, map_zero]))
  have hli : LinearIndependent (ZMod 2) ![v, J v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) s with rfl | rfl <;>
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [zero_smul, one_smul, zero_add] at hst; exact absurd hst hJv0
    · rw [zero_smul, one_smul, add_zero] at hst; exact absurd hst hv0
    · rw [one_smul, one_smul] at hst
      exact absurd (eq_of_sub_eq_zero (by rw [sub_eq_add_neg, ZModModule.neg_eq_self]; rwa
        [add_comm] at hst)) hJv1
  have hspan : Submodule.span (ZMod 2) (Set.range ![v, J v]) ≤
      commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (b : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hv
    · exact hJv
  have h2 : 2 ≤ finrank (ZMod 2)
      (commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (b : S.Qt ≃ₗ[ZMod 2] S.Qt) : _) := by
    have := Submodule.finrank_mono hspan
    rwa [finrank_span_eq_card hli, Fintype.card_fin] at this
  have hA := (h.isTypeA ha).2.2.2.1
  have hB := (h.isTypeA hb).2.2.2.1
  have e1 := Submodule.eq_of_le_of_finrank_le
    (inf_le_left : _ ≤ commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt)) (by rw [hA]; exact h2)
  have e2 := Submodule.eq_of_le_of_finrank_le
    (inf_le_right : _ ≤ commSpace (b : S.Qt ≃ₗ[ZMod 2] S.Qt)) (by rw [hB]; exact h2)
  exact hab (Subtype.ext (OrthoF2.eq_of_commSpace_eq S.q_nondegenerate (h.isTypeA ha)
    (h.isTypeA hb) (e1.symm.trans e2)))

theorem exists_commute {a : S.O} (ha : a ∈ S.DbarAsc) :
    ∃ b ∈ S.DbarAsc, b ≠ a ∧ a * b = b * a := by
  obtain ⟨ψ⟩ := h.psu
  obtain ⟨b, hb, hba, hab⟩ :=
    AS35Z.exists_commute_of_isTClass (h.hyp.isTClass ha) h.two_le ψ (a := mkL ha) ha
  exact ⟨b, hb, fun h1 => hba (Subtype.ext h1), congrArg Subtype.val hab⟩

end ZUHyp

end Setting

end CFSG.LargeExtraspecial
