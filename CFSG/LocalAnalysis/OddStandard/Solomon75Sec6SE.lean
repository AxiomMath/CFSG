module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Defs
public import CFSG.Timmesfeld.Bridge.Asc73Quotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingSolvable

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open Timmesfeld.Connectivity in
theorem sec6_disconnected_of_closed {X : Type} [Group X] {D : Set X} {H : Subgroup X} {d y : X}
    (hd : d ∈ D) (hdH : d ∈ H) (hy : y ∈ D) (hyH : y ∉ H)
    (hcl : ∀ x ∈ D, x ∈ H → ∀ z ∈ D, Commute x z → z ∈ H) : Disconnected D := by
  refine ⟨d, hd, y, hy, fun hr => hyH ?_⟩
  have key : ∀ w, Reach D d w → w ∈ H := by
    intro w hw
    unfold Reach at hw
    induction hw with
    | refl => exact hdH
    | tail _ hbc ih => exact hcl _ hbc.1 ih _ hbc.2.1 hbc.2.2
  exact key y hr

theorem sec6_not_isSolvable_centralizer_conj {X : Type} [Group X] {y : X} (g : X)
    (h : ¬ Group.IsSolvable ↥(centralizer ({y} : Set X))) :
    ¬ Group.IsSolvable ↥(centralizer ({g * y * g⁻¹} : Set X)) := by
  intro hs
  apply h
  let φ : ↥(centralizer ({y} : Set X)) →* ↥(centralizer ({g * y * g⁻¹} : Set X)) :=
    { toFun := fun c => ⟨g * c * g⁻¹, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hc : (c : X) * y = y * c := Subgroup.mem_centralizer_singleton_iff.1 c.2
        calc g * c * g⁻¹ * (g * y * g⁻¹) = g * ((c : X) * y) * g⁻¹ := by group
          _ = g * (y * c) * g⁻¹ := by rw [hc]
          _ = g * y * g⁻¹ * (g * c * g⁻¹) := by group⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : g * (a : X) * g⁻¹ = g * b * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using h1)
  exact Group.isSolvable_of_isSolvable_injective hφ

theorem sec6_false_of_disconnected {X : Type} [Group X] [Finite X]
    (hAsc : Timmesfeld.Bridge.Asc73For X) (hrank : 2 ≤ Open.twoRank X) {D : Set X}
    (hN : Timmesfeld.Connectivity.IsNormalSet D) (hD : Timmesfeld.Bridge.IsInvolutionSet D)
    (hgen : Subgroup.closure D = ⊤) (hnp : Timmesfeld.Moufang.NoPolar D)
    (hdisc : Timmesfeld.Connectivity.Disconnected D)
    (hns : ∀ d ∈ D, ¬ Group.IsSolvable ↥(centralizer ({d} : Set X))) : False := by
  obtain ⟨d, hd, -⟩ := id hdisc
  have hSE := hAsc D hN hD hgen hnp hdisc d hd
  set M := Timmesfeld.Connectivity.compStab hN d with hM
  have hF : Open.fusionStronglyEmbedded M := (Timmesfeld.Bridge.fusionStronglyEmbedded_iff M).2 hSE
  haveI hsol : Group.IsSolvable ↥M :=
    ComponentClassification.AschbacherStrongEmbedding.strongly_embedded_solvable X M hF hrank
  have hdM : d ∈ M := by
    show Timmesfeld.Connectivity.Reach D d (d * d * d⁻¹)
    rw [mul_inv_cancel_right]
    exact Relation.ReflTransGen.refl
  have hd2 : orderOf d = 2 := hD d hd
  have hCM : centralizer ({d} : Set X) ≤ M := by
    intro c hc
    by_contra hcM
    have hodd := hF.2.2 c hcM
    have hcd : c * d = d * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    have hdc : d ∈ M ⊓ M.map (MulAut.conj c⁻¹).toMonoidHom := by
      refine ⟨hdM, d, hdM, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [mul_assoc, ← hcd, ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : 2 ∣ Nat.card ↥(M ⊓ M.map (MulAut.conj c⁻¹).toMonoidHom) :=
      hd2 ▸ Subgroup.orderOf_dvd_natCard _ hdc
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  exact hns d hd (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hCM))

theorem sec6_false_of_fusion {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hAsc : Timmesfeld.Bridge.Asc73For X) (hrank : 2 ≤ Open.twoRank X)
    {N Y : Subgroup X} (h : Sec6Fusion X N Y) : False := by
  set D := sec6D Y with hDdef
  have hinv : Timmesfeld.Bridge.IsInvolutionSet D := by
    rintro x ⟨g, y, -, hy2, rfl⟩
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
    simpa [MulAut.conj_apply] using this.trans hy2
  have hNS : Timmesfeld.Connectivity.IsNormalSet D := by
    rintro g x ⟨h', y, hy, hy2, rfl⟩
    exact ⟨g * h', y, hy, hy2, by group⟩
  obtain ⟨y₀, hy₀Y, hy₀2⟩ := h.inv
  have hy₀D : y₀ ∈ D := ⟨1, y₀, hy₀Y, hy₀2, by group⟩
  have hgen : Subgroup.closure D = ⊤ := by
    have hsub : Group.conjugatesOfSet D ⊆ D := by
      intro b hb
      rw [Group.mem_conjugatesOfSet_iff] at hb
      obtain ⟨a, ha, hab⟩ := hb
      obtain ⟨c, rfl⟩ := isConj_iff.1 hab
      exact hNS c a ha
    have hle : Subgroup.normalClosure D ≤ Subgroup.closure D := Subgroup.closure_mono hsub
    have hne : Subgroup.normalClosure D ≠ ⊥ := by
      intro hbot
      have h1 : y₀ ∈ Subgroup.normalClosure D := Subgroup.subset_normalClosure hy₀D
      rw [hbot, Subgroup.mem_bot] at h1
      rw [h1, orderOf_one] at hy₀2
      exact absurd hy₀2 (by decide)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure D) with hb | ht
    · exact absurd hb hne
    · exact eq_top_iff.2 (ht ▸ hle)
  have hnp : Timmesfeld.Moufang.NoPolar D := by
    intro x hx z hz hxz hne
    obtain ⟨g, hgx, hgz⟩ := h.conj x hx z hz hxz
    have hxY : g * x * g⁻¹ ∈ Y := h.fus _ (hNS g x hx) hgx
    have hzY : g * z * g⁻¹ ∈ Y := h.fus _ (hNS g z hz) hgz
    have hxzY : g * (x * z) * g⁻¹ ∈ Y := by
      have := Y.mul_mem hxY hzY
      rwa [show g * x * g⁻¹ * (g * z * g⁻¹) = g * (x * z) * g⁻¹ by group] at this
    have hx2 : orderOf x = 2 := hinv x hx
    have hz2 : orderOf z = 2 := hinv z hz
    have hxz2 : orderOf (g * (x * z) * g⁻¹) = 2 := by
      have hxx : x ^ 2 = 1 := hx2 ▸ pow_orderOf_eq_one x
      have hzz : z ^ 2 = 1 := hz2 ▸ pow_orderOf_eq_one z
      have hsq : (x * z) ^ 2 = 1 := by rw [hxz.mul_pow, hxx, hzz, one_mul]
      have hne1 : x * z ≠ 1 := by
        intro h1
        apply hne
        have hzinv : z⁻¹ = z := by
          rw [inv_eq_iff_mul_eq_one, ← sq, hzz]
        rw [mul_eq_one_iff_eq_inv, hzinv] at h1
        exact h1
      have h2 : orderOf (x * z) = 2 := orderOf_eq_prime hsq hne1
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (x * z)
      simpa [MulAut.conj_apply] using this.trans h2
    exact ⟨g⁻¹, g * (x * z) * g⁻¹, hxzY, hxz2, by group⟩
  have hout : ∃ y ∈ D, y ∉ N := by
    by_contra hcon
    push Not at hcon
    apply h.ne_top
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le N).2 hcon
  obtain ⟨y, hyD, hyN⟩ := hout
  have hdisc : Timmesfeld.Connectivity.Disconnected D :=
    sec6_disconnected_of_closed hy₀D (h.le hy₀Y) hyD hyN fun x hx hxN z _ hxz =>
      h.cen x (h.fus x hx hxN) (hinv x hx) (Subgroup.mem_centralizer_singleton_iff.2 hxz.eq.symm)
  refine sec6_false_of_disconnected hAsc hrank hNS hinv hgen hnp hdisc ?_
  rintro d ⟨g, y', hy', hy'2, rfl⟩
  exact sec6_not_isSolvable_centralizer_conj g (h.ns y' hy' hy'2)

end CFSG.OddStandard.Solomon75
