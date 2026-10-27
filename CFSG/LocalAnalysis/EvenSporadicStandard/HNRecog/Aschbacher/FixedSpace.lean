module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Free.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.A5WrTwoInvolutions

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.RankThree.Literature.FSmith

variable {C : Type} [Group C] [Finite C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

theorem AschbacherHyp.exists_eq_add_of_fixed (hC : AschbacherHyp C Q) {τ : C}
    (hτ : τ ∉ commutator C) (hτ2 : τ ^ 2 ∈ centerOf Q) (x : Additive (Abelianization Q))
    (hx : conjLinEquiv hQn τ x = x) : ∃ y : Additive (Abelianization Q), x = y + conjLinEquiv hQn τ y := by
  classical
  haveI : Finite Q := hC.plus.finite
  haveI : Finite (Additive (Abelianization Q)) := by
    change Finite (Q ⧸ _root_.commutator Q)
    infer_instance
  obtain ⟨t, ht⟩ := hC.exists_isOuterInvolution
  have hfree := hC.exists_free_involution ht
  obtain ⟨e, θ, _, hθs, _, hθe, _, _, _⟩ := hC.exists_hom_baseEmb
  let Φ : C →* A5WrTwo := (e : C ⧸ Q →* A5WrTwo).comp (QuotientGroup.mk' Q)
  have hΦ_eq_one : ∀ g : C, Φ g = 1 ↔ g ∈ Q := by
    intro g
    change e (QuotientGroup.mk' Q g) = 1 ↔ g ∈ Q
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff g
  have hθe' : ∀ l : ↥(commutator C), A5WrTwo.baseEmb (θ l) = Φ (l : C) := fun l => hθe l
  have hu_out : Φ t ∉ commutator A5WrTwo := by
    intro hu
    have humem : Φ t ∈ A5WrTwo.baseEmb.range := by rwa [A5WrTwo.range_baseEmb]
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp humem
    obtain ⟨l, hl⟩ := hθs g
    have h1 : Φ (l : C) = Φ t := by
      calc Φ (l : C) = A5WrTwo.baseEmb (θ l) := (hθe' l).symm
        _ = A5WrTwo.baseEmb g := by rw [hl]
        _ = Φ t := hg
    have hq : (l : C) * t⁻¹ ∈ Q := by
      rw [← hΦ_eq_one ((l : C) * t⁻¹)]
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have htL : t ∈ commutator C := by
      have h2 : (l : C) * t⁻¹ ∈ commutator C := hC.le_commutator hq
      have h3 := mul_mem (inv_mem h2) l.2
      convert h3 using 1
      group
    exact ht.1 htL
  have hv_out : Φ τ ∉ commutator A5WrTwo := by
    intro hv
    have hvmem : Φ τ ∈ A5WrTwo.baseEmb.range := by rwa [A5WrTwo.range_baseEmb]
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hvmem
    obtain ⟨l, hl⟩ := hθs g
    have h1 : Φ (l : C) = Φ τ := by
      calc Φ (l : C) = A5WrTwo.baseEmb (θ l) := (hθe' l).symm
        _ = A5WrTwo.baseEmb g := by rw [hl]
        _ = Φ τ := hg
    have hq : (l : C) * τ⁻¹ ∈ Q := by
      rw [← hΦ_eq_one ((l : C) * τ⁻¹)]
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have hτL : τ ∈ commutator C := by
      have h2 : (l : C) * τ⁻¹ ∈ commutator C := hC.le_commutator hq
      have h3 := mul_mem (inv_mem h2) l.2
      convert h3 using 1
      group
    exact hτ hτL
  have hu2 : (Φ t) ^ 2 = 1 := by
    rw [← map_pow, ht.2.1, map_one]
  have hv2 : (Φ τ) ^ 2 = 1 := by
    rw [← map_pow, (hΦ_eq_one (τ ^ 2)).2 hτ2.1]
  obtain ⟨b', hb', hb'uv⟩ := A5WrTwo.exists_conj_of_outer_involutions
    (u := Φ τ) (v := Φ t) hv_out hu_out hv2 hu2
  have hb'mem : b' ∈ A5WrTwo.baseEmb.range := by rwa [A5WrTwo.range_baseEmb]
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hb'mem
  obtain ⟨l, hl⟩ := hθs g
  have hb'eq : b' = Φ (l : C) := by rw [← hg, ← hl, hθe' l]
  have hconj : Φ (l : C) * Φ τ * (Φ (l : C))⁻¹ = Φ t := by
    rw [← hb'eq]
    exact hb'uv
  have hΦx : Φ ((l : C) * τ * (l : C)⁻¹) = Φ t := by
    simpa only [map_mul, map_inv] using hconj
  have hq : ((l : C) * τ * (l : C)⁻¹) * t⁻¹ ∈ Q := by
    rw [← hΦ_eq_one (((l : C) * τ * (l : C)⁻¹) * t⁻¹)]
    rw [map_mul, map_inv, hΦx, mul_inv_cancel]
  have hρx : conjLinEquiv hQn ((l : C) * τ * (l : C)⁻¹) = conjLinEquiv hQn t := by
    have h1 : conjLinEquiv hQn (((l : C) * τ * (l : C)⁻¹) * t⁻¹) = 1 :=
      conjLinEquiv_eq_one_of_mem hq
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  have hrel : conjLinEquiv hQn (l : C) * conjLinEquiv hQn τ *
      (conjLinEquiv hQn (l : C))⁻¹ = conjLinEquiv hQn t := by
    simpa only [map_mul, map_inv] using hρx
  have hC_eq : conjLinEquiv hQn τ =
      (conjLinEquiv hQn (l : C))⁻¹ * conjLinEquiv hQn t * conjLinEquiv hQn (l : C) := by
    rw [← hrel]
    group
  have hρt2 : conjLinEquiv hQn t * conjLinEquiv hQn t = 1 := by
    rw [← pow_two, ← map_pow, ht.2.1, map_one]
  have hb : (↑(conjLinEquiv hQn t) : Additive (Abelianization Q) →ₗ[ZMod 2]
        Additive (Abelianization Q)) *
      (↑(conjLinEquiv hQn t) : Additive (Abelianization Q) →ₗ[ZMod 2]
        Additive (Abelianization Q)) = 1 := by
    ext z
    have h := congrArg (fun f : Additive (Abelianization Q) ≃ₗ[ZMod 2]
      Additive (Abelianization Q) => f z) hρt2
    simpa [LinearEquiv.mul_apply, Module.End.mul_apply] using h
  have h8 : Module.finrank (ZMod 2) (Additive (Abelianization Q)) = 8 := by
    rw [hC.plus.finrank_quotient]
  have hAx : (conjLinEquiv hQn t) ((conjLinEquiv hQn (l : C)) x) =
      (conjLinEquiv hQn (l : C)) x := by
    have h2 : (conjLinEquiv hQn (l : C))⁻¹
        ((conjLinEquiv hQn t) ((conjLinEquiv hQn (l : C)) x)) = x := by
      have h3 : ((conjLinEquiv hQn (l : C))⁻¹ * conjLinEquiv hQn t *
          conjLinEquiv hQn (l : C)) x = x := by
        rw [← hC_eq]
        exact hx
      simpa only [LinearEquiv.mul_apply] using h3
    have h4 := congrArg (fun z => (conjLinEquiv hQn (l : C)) z) h2
    simpa using h4
  obtain ⟨y, hy⟩ := Free.exists_eq_add_of_four_le_finrank_range
    (↑(conjLinEquiv hQn t) : Additive (Abelianization Q) →ₗ[ZMod 2] Additive (Abelianization Q))
    hb h8 hfree ((conjLinEquiv hQn (l : C)) x) hAx
  refine ⟨(conjLinEquiv hQn (l : C))⁻¹ y, ?_⟩
  calc x = (conjLinEquiv hQn (l : C))⁻¹ ((conjLinEquiv hQn (l : C)) x) := by simp
    _ = (conjLinEquiv hQn (l : C))⁻¹ (y + (conjLinEquiv hQn t) y) := by
        rw [hy]
        simp only [LinearEquiv.coe_toLinearMap]
    _ = (conjLinEquiv hQn (l : C))⁻¹ y +
          (conjLinEquiv hQn (l : C))⁻¹ ((conjLinEquiv hQn t) y) :=
        ((conjLinEquiv hQn (l : C))⁻¹).map_add y ((conjLinEquiv hQn t) y)
    _ = (conjLinEquiv hQn (l : C))⁻¹ y +
          conjLinEquiv hQn τ ((conjLinEquiv hQn (l : C))⁻¹ y) := by
        rw [hC_eq]
        simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

end CFSG.EvenSporadicStandard.HNRecog
