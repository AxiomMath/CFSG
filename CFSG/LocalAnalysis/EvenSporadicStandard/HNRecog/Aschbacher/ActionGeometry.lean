module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.AlphaIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.SwapAction
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Free.Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup Module CFSG.RankThree.Literature.FSmith

variable {C C' : Type} [Group C] [Group C'] [Finite C] [Finite C'] {Q : Subgroup C}
  {Q' : Subgroup C'} [hQn : Q.Normal] [hQn' : Q'.Normal]

private theorem polarBilin_map_eq {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] (q : QuadraticForm (ZMod 2) V)
    (q' : QuadraticForm (ZMod 2) V') (f : V ≃ₗ[ZMod 2] V') (hf : ∀ v, q' (f v) = q v) :
    ∀ x y, q'.polarBilin (f x) (f y) = q.polarBilin x y := by
  intro x y
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [← map_add f x y, hf (x + y), hf x, hf y]

theorem AschbacherHyp.exists_conj_mod_centerOf (hC : AschbacherHyp C Q)
    (hC' : AschbacherHyp C' Q') (α : ↥(commutator C) ≃* ↥(commutator C')) {t : C}
    (ht : IsOuterInvolution Q t) :
    ∃ τ : C', τ ∉ commutator C' ∧ ∀ x : ↥(commutator C'), (x : C') ∈ Q' →
      ((α (MulAut.conjNormal t (α.symm x)) : ↥(commutator C')) : C') *
        (τ * (x : C') * τ⁻¹)⁻¹ ∈ centerOf Q' := by
  classical
  haveI : Finite Q := hC.plus.finite
  have hE : IsExtraspecialPGroup 2 Q := hC.plus.isExtraspecialPGroup
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hE
  haveI : Finite Q' := hC'.plus.finite
  have hE' : IsExtraspecialPGroup 2 Q' := hC'.plus.isExtraspecialPGroup
  letI : Module (ZMod 2) (Additive (Abelianization Q')) :=
    CFSG.GroupTheory.extraspecialQuotientModule hE'
  haveI : Finite (Additive (Abelianization Q')) := by
    change Finite (Q' ⧸ _root_.commutator Q'); infer_instance
  obtain ⟨t', ht'⟩ := hC'.exists_isOuterInvolution
  obtain ⟨θ, σ, s, hθs, hθk, hσθ, hσi, hirr, hs_swap, hρt⟩ := hC.exists_hom_swap ht
  obtain ⟨θ', σ', s', hθs', hθk', hσθ', hσi', hirr', hs'_swap, hρt'⟩ := hC'.exists_hom_swap ht'
  obtain ⟨a, ha_q, ha_inter, ha_cls⟩ := hC.exists_isometry hC' α
  let ρL : ↥(commutator C) →* (Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q)) :=
    (conjLinEquiv hQn).comp (commutator C).subtype
  let ρ'L : ↥(commutator C') →* (Additive (Abelianization Q') ≃ₗ[ZMod 2] Additive (Abelianization Q')) :=
    (conjLinEquiv hQn').comp (commutator C').subtype
  have hσθ_hom : ∀ l, σ (θ l) = ρL l := fun l => hσθ l
  have hσθ'_hom : ∀ l, σ' (θ' l) = ρ'L l := fun l => hσθ' l
  have hker : ∀ l, θ l = 1 ↔ θ' (α l) = 1 := by
    intro l
    exact (hθk l).trans ((hC.map_mem_iff hC' α l).symm.trans (hθk' (α l)).symm)
  obtain ⟨ψ, hψ⟩ := Swap.exists_mulEquiv_of_ker θ θ' hθs hθs' α hker
  have hint : ∀ g v, a (σ g v) = σ' (ψ g) (a v) :=
    Swap.intertwine_of_surjective θ hθs θ' σ σ' ρL ρ'L hσθ_hom hσθ'_hom α a ha_inter ψ hψ
  let b : Additive (Abelianization Q') ≃ₗ[ZMod 2] Additive (Abelianization Q') :=
    Swap.transport a (conjLinEquiv hQn t)
  let b' : Additive (Abelianization Q') ≃ₗ[ZMod 2] Additive (Abelianization Q') :=
    conjLinEquiv hQn' t'
  have hρt2 : conjLinEquiv hQn t * conjLinEquiv hQn t = 1 := by
    rw [← map_mul, show t * t = t ^ 2 from (pow_two t).symm, ht.2.1, map_one]
  have hρt'2 : conjLinEquiv hQn' t' * conjLinEquiv hQn' t' = 1 := by
    rw [← map_mul, show t' * t' = t' ^ 2 from (pow_two t').symm, ht'.2.1, map_one]
  have hb : b * b = 1 := Swap.transport_mul_self a hρt2
  have hb' : b' * b' = 1 := hρt'2
  have hsw : Swap.SwapsFactors σ' b :=
    Swap.swapsFactors_transport σ σ' a ψ hint (conjLinEquiv hQn t) s hs_swap hρt
  have hsw' : Swap.SwapsFactors σ' b' :=
    Swap.swapsFactors_of_aut σ' b' s' hs'_swap hρt'
  let B : LinearMap.BilinForm (ZMod 2) (Additive (Abelianization Q)) :=
    (extraspecialQuadForm hE).polarBilin
  let B' : LinearMap.BilinForm (ZMod 2) (Additive (Abelianization Q')) :=
    (extraspecialQuadForm hE').polarBilin
  have hB' : B'.Nondegenerate := extraspecialQuadForm_nondegenerate hE'
  have hBσ' : ∀ g x y, B' (σ' g x) (σ' g y) = B' x y := by
    intro g x y
    obtain ⟨l, rfl⟩ := hθs' g
    rw [hσθ' l]
    exact polarBilin_map_eq (extraspecialQuadForm hE') (extraspecialQuadForm hE')
      (conjLinEquiv hQn' (l : C'))
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (conjLinEquiv_mem hE' hQn' (l : C'))) x y
  have hBa : ∀ x y, B' (a x) (a y) = B x y :=
    polarBilin_map_eq (extraspecialQuadForm hE) (extraspecialQuadForm hE') a ha_q
  have hBρt : ∀ x y, B (conjLinEquiv hQn t x) (conjLinEquiv hQn t y) = B x y :=
    polarBilin_map_eq (extraspecialQuadForm hE) (extraspecialQuadForm hE) (conjLinEquiv hQn t)
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (conjLinEquiv_mem hE hQn t))
  have hBρt' : ∀ x y, B' (conjLinEquiv hQn' t' x) (conjLinEquiv hQn' t' y) = B' x y :=
    polarBilin_map_eq (extraspecialQuadForm hE') (extraspecialQuadForm hE') (conjLinEquiv hQn' t')
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (conjLinEquiv_mem hE' hQn' t'))
  have hBb : ∀ x y, B' (b x) (b y) = B' x y :=
    Swap.isometry_transport a hBa hBρt
  have hBb' : ∀ x y, B' (b' x) (b' y) = B' x y := hBρt'
  have hfree : 4 ≤ finrank (ZMod 2) (LinearMap.range ((b : Additive (Abelianization Q') →ₗ[ZMod 2]
      Additive (Abelianization Q')) + 1)) :=
    (Swap.finrank_range_transport a (conjLinEquiv hQn t)).symm ▸ hC.exists_free_involution ht
  have hfree' : 4 ≤ finrank (ZMod 2) (LinearMap.range ((b' : Additive (Abelianization Q') →ₗ[ZMod 2]
      Additive (Abelianization Q')) + 1)) := hC'.exists_free_involution ht'
  have hS' : Swap.StdHyp σ' :=
    ⟨hσi', by rw [hC'.plus.finrank_quotient], hirr'⟩
  obtain ⟨g, hg⟩ := Swap.exists_mul_of_swap_free σ' hS' B' hB' hBσ' hb hb' hBb hBb' hsw hsw' hfree hfree'
  obtain ⟨l', hl'⟩ := hθs' g
  let τ : C' := (l' : C') * t'
  have hτ : τ ∉ commutator C' := by
    intro h
    have h2 : (l' : C')⁻¹ * τ ∈ commutator C' :=
      (commutator C').mul_mem ((commutator C').inv_mem l'.2) h
    apply ht'.1
    have h3 : (l' : C')⁻¹ * τ = t' := by
      change (l' : C')⁻¹ * ((l' : C') * t') = t'
      group
    rwa [h3] at h2
  refine ⟨τ, hτ, fun x hx => ?_⟩
  let y : ↥(commutator C) := α.symm x
  have hy : (y : C) ∈ Q := by
    refine (hC.map_mem_iff hC' α y).1 ?_
    simpa [y, MulEquiv.apply_symm_apply] using hx
  let m : ↥(commutator C) := MulAut.conjNormal t y
  have hm_Q : (m : C) ∈ Q := by
    have h : (m : C) = t * (y : C) * t⁻¹ := MulAut.conjNormal_apply t y
    rw [h]
    exact hQn.conj_mem (y : C) hy t
  set u₁ : Q' := ⟨((α m : ↥(commutator C')) : C'), hC.map_mem_of_mem hC' α hm_Q⟩ with hu₁
  set u₂ : Q' := conjAut hQn' τ (⟨(x : C'), hx⟩ : Q') with hu₂
  set vy : Additive (Abelianization Q) :=
    Additive.ofMul (Abelianization.of (⟨(y : C), hy⟩ : Q)) with hvy
  set vx : Additive (Abelianization Q') :=
    Additive.ofMul (Abelianization.of (⟨(x : C'), hx⟩ : Q')) with hvx
  have h_a_y : a vy = vx := by
    rw [hvy, hvx, ha_cls y hy]
    have hsub : (⟨((α y : ↥(commutator C')) : C'), hC.map_mem_of_mem hC' α hy⟩ : Q') =
        (⟨(x : C'), hx⟩ : Q') :=
      Subtype.ext (congrArg (fun z : ↥(commutator C') => (z : C'))
        (MulEquiv.apply_symm_apply α x))
    rw [hsub]
  have h_u1 : Additive.ofMul (Abelianization.of u₁) = a (conjLinEquiv hQn t vy) := by
    have h_my : (⟨(m : C), hm_Q⟩ : Q) = conjAut hQn t (⟨(y : C), hy⟩ : Q) := by
      refine Subtype.ext ?_
      rw [conjAut_apply,
        show (m : C) = t * (y : C) * t⁻¹ from MulAut.conjNormal_apply t y]
    rw [hu₁, ← ha_cls m hm_Q]
    apply congrArg (fun w => a w)
    rw [hvy, conjLinEquiv_apply hQn t (⟨(y : C), hy⟩ : Q)]
    exact congrArg (fun z : Q => Additive.ofMul (Abelianization.of z)) h_my
  have h_u2 : Additive.ofMul (Abelianization.of u₂) = conjLinEquiv hQn' τ vx := by
    rw [hu₂, hvx, conjLinEquiv_apply]
  have h_x_symm : a.symm vx = vy := by
    rw [LinearEquiv.symm_apply_eq]
    exact h_a_y.symm
  have h_b : b vx = a (conjLinEquiv hQn t vy) := by
    change Swap.transport a (conjLinEquiv hQn t) vx = a (conjLinEquiv hQn t vy)
    rw [Swap.transport_apply, h_x_symm]
  have h_main : a (conjLinEquiv hQn t vy) = conjLinEquiv hQn' τ vx := by
    rw [← h_b]
    rw [show b vx = (σ' g * b') vx from congrArg (fun f : Additive (Abelianization Q') ≃ₗ[ZMod 2]
      Additive (Abelianization Q') => f vx) hg]
    rw [LinearEquiv.mul_apply]
    have hσg : σ' g = conjLinEquiv hQn' (l' : C') := by rw [← hl', hσθ' l']
    rw [hσg]
    rw [show b' = conjLinEquiv hQn' t' from rfl, show τ = (l' : C') * t' from rfl, map_mul]
    rw [← LinearEquiv.mul_apply]
  have h_eq_class : Additive.ofMul (Abelianization.of u₁) =
      Additive.ofMul (Abelianization.of u₂) :=
    h_u1.trans (h_main.trans h_u2.symm)
  have h0 : Additive.ofMul (Abelianization.of (u₁ * u₂⁻¹)) = 0 := by
    rw [ofMul_of_mul, map_inv, ofMul_inv, h_eq_class, add_neg_cancel]
  have hcen : u₁ * u₂⁻¹ ∈ Subgroup.center Q' :=
    (ofMul_of_eq_zero_iff hE' (u₁ * u₂⁻¹)).mp h0
  have hgoal : ((u₁ * u₂⁻¹ : Q') : C') ∈ centerOf Q' :=
    (mem_centerOf_iff (u₁ * u₂⁻¹)).mpr hcen
  have heq : ((u₁ * u₂⁻¹ : Q') : C') =
      ((α (MulAut.conjNormal t (α.symm x)) : ↥(commutator C')) : C') *
        (τ * (x : C') * τ⁻¹)⁻¹ := by
    rw [hu₁, hu₂, Subgroup.coe_mul, Subgroup.coe_inv, conjAut_apply]
  rw [heq] at hgoal
  exact hgoal

end CFSG.EvenSporadicStandard.HNRecog
