module

public import CFSG.ClassicalInvolution.RouteD.TWZPair
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecNR

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TWZ
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.ModelFacts.Orth15
open CFSG.ClassicalInvolution.Q3 (CompData)
open scoped commutatorElement

@[expose] def SqNoRootC (c : CompData) : Prop :=
  ∀ (X : Type) [Group X] (θ : c.G →* X), Function.Surjective θ → θ.ker ≤ Subgroup.center c.G →
    ∀ (R R' : Subgroup c.G), R ∈ c.fund → R' ∈ c.fund → R ≠ R' →
      ∀ (x x' : c.G), x ∈ R → x * x = 1 → x ≠ 1 → x' ∈ R' → x' * x' = 1 → x' ≠ 1 →
        θ x = θ x' →
        ∀ α : MulAut X, (∀ r ∈ R, α (θ r) = θ r) → (∀ r ∈ R', α (θ r) = θ r) →
          α * α ≠ MulAut.conj (θ x)

section Generic

variable {S X P : Type} [Group S] [Group X] [Group P]

theorem sq_noRoot_of_autSq [Group.IsPerfect S] (π : S →* P) (hπ : Function.Surjective π)
    (hπk : π.ker = Subgroup.center S) (θ : S →* X) (hθ : Function.Surjective θ)
    (hθk : θ.ker ≤ Subgroup.center S) {R R' : Subgroup S} {x : S}
    (hsq : ∀ φ : MulAut P, (∀ r ∈ R, φ (π r) = π r) → (∀ r ∈ R', φ (π r) = π r) →
      φ * φ = MulAut.conj (π x) → φ * φ = 1)
    (hx : x ∉ Subgroup.center S) (α : MulAut X) (hαR : ∀ r ∈ R, α (θ r) = θ r)
    (hαR' : ∀ r ∈ R', α (θ r) = θ r) : α * α ≠ MulAut.conj (θ x) := by
  classical
  intro hαα
  set ψ' : S →* MulAut X := (MulAut.conj : X →* MulAut X).comp θ with hψ'
  have hker' : ψ'.ker ≤ Subgroup.center S := by
    intro m hm
    have hm1 : MulAut.conj (θ m) = 1 := hm
    have hcentral : θ m ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h1 : θ m * w * (θ m)⁻¹ = w := by
        have := DFunLike.congr_fun hm1 w
        simpa [MulAut.conj_apply] using this
      calc w * θ m = (θ m * w * (θ m)⁻¹) * θ m := by rw [h1]
        _ = θ m * w := by group
    refine mem_center_of_comm_mem_center fun s => ?_
    apply hθk
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hcentral (θ s)).symm
  have hαN : α ∈ Subgroup.normalizer ((ψ'.range : Subgroup (MulAut X)) : Set (MulAut X)) :=
    mem_normalizer_range_conj θ hθ α
  obtain ⟨v, hv⟩ : ∃ v : ↥(inducedAutOn ψ'.range), v = toInducedAutOn ψ'.range ⟨α, hαN⟩ :=
    ⟨_, rfl⟩
  have hvcomm : ∀ T : Subgroup S, (∀ r ∈ T, α (θ r) = θ r) → ∀ r ∈ T,
      v * innerHom ψ' r = innerHom ψ' r * v := by
    intro T hT r hr
    rw [hv, innerHom_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show α * ψ' r = ψ' r * α
    calc α * ψ' r = (α * MulAut.conj (θ r) * α⁻¹) * α := by
          show α * MulAut.conj (θ r) = (α * MulAut.conj (θ r) * α⁻¹) * α
          group
      _ = MulAut.conj (α (θ r)) * α := by rw [mulAut_mul_conj_mul_inv]
      _ = ψ' r * α := by rw [hT r hr]; rfl
  have hvv : v * v = innerHom ψ' x := by
    rw [hv, innerHom_apply, ← map_mul]
    congr 1
    exact Subtype.ext hαα
  have hfix : ∀ r : S, v * innerHom ψ' r = innerHom ψ' r * v →
      outerAction ψ' hker' π hπ hπk v (π r) = π r := by
    intro r hr
    apply (outerEquiv ψ' hker' π hπ hπk).injective
    apply Subtype.ext
    rw [outerAction_apply, outerEquiv_apply, hr]
    group
  have hφ : outerAction ψ' hker' π hπ hπk v * outerAction ψ' hker' π hπ hπk v =
      MulAut.conj (π x) := by
    rw [← map_mul, hvv, outerAction_innerHom]
  have h1 := hsq (outerAction ψ' hker' π hπ hπk v)
    (fun r hr => hfix r (hvcomm R hαR r hr)) (fun r hr => hfix r (hvcomm R' hαR' r hr)) hφ
  have hv2 : v * v = 1 := by
    apply eq_one_of_outerAction_eq_one ψ' hker' π hπ hπk
    rw [map_mul, h1]
  have hxker : innerHom ψ' x = 1 := by rw [← hvv, hv2]
  have hxπ : x ∈ π.ker := by
    rw [ker_eq_innerHom_ker ψ' hker' π hπk, MonoidHom.mem_ker]
    exact hxker
  rw [hπk] at hxπ
  exact hx hxπ

end Generic

theorem sqNoRootC_of_autSq (c : CompData) [Group.IsPerfect c.G] {P : Type} [Group P]
    (π : c.G →* P) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center c.G)
    (hnc : ∀ R ∈ c.fund, ∀ r ∈ R, r ∈ Subgroup.center c.G → r = 1)
    (hsq : ∀ (R R' : Subgroup c.G), R ∈ c.fund → R' ∈ c.fund → R ≠ R' →
      ∀ (x x' : c.G), x ∈ R → x * x = 1 → x ≠ 1 → x' ∈ R' → x' * x' = 1 → x' ≠ 1 →
        x' * x⁻¹ ∈ Subgroup.center c.G →
        ∀ φ : MulAut P, (∀ r ∈ R, φ (π r) = π r) → (∀ r ∈ R', φ (π r) = π r) →
          φ * φ = MulAut.conj (π x) → φ * φ = 1) :
    SqNoRootC c := by
  intro X _ θ hθ hθk R R' hR hR' hne x x' hx hx2 hx1 hx' hx'2 hx'1 hxx' α hαR hαR'
  have hc : x' * x⁻¹ ∈ Subgroup.center c.G := by
    apply hθk
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', mul_inv_cancel]
  exact sq_noRoot_of_autSq π hπ hπk θ hθ hθk
    (hsq R R' hR hR' hne x x' hx hx2 hx1 hx' hx'2 hx'1 hc) (fun h => hx1 (hnc R hR x hx h)) α
    hαR hαR'

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecNR
