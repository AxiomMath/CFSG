module

public import CFSG.ClassicalInvolution.RouteD.TWZFrame
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinSpin
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerBasic
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExc

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD.Exotic (commutes_of_commutator_mem_center)
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.Models.Transfer (CenterScalar)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Aut

variable {S X : Type} [Group S] [Group X]

@[expose] def autRange (θ : S →* X) (hs : Function.Surjective θ) (α : MulAut X) :
    ↥θ.range ≃* ↥θ.range where
  toFun ℓ := ⟨α (ℓ : X), (MonoidHom.mem_range.mpr (hs _))⟩
  invFun ℓ := ⟨α.symm (ℓ : X), (MonoidHom.mem_range.mpr (hs _))⟩
  left_inv ℓ := by apply Subtype.ext; simp
  right_inv ℓ := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp

def fixerSub (θ : S →* X) (α : MulAut X) : Subgroup S where
  carrier := {s | α (θ s) = θ s}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    show α (θ (a * b)) = θ (a * b)
    rw [map_mul, map_mul]
    exact congrArg₂ (· * ·) ha hb
  inv_mem' {a} ha := by
    show α (θ a⁻¹) = θ a⁻¹
    rw [map_inv, map_inv]
    exact congrArg (·⁻¹) ha

end Aut

section Main

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem exists_sq_data (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {X : Type} [Group X] {θ : spinGroup Q →* X} (hθs : Function.Surjective θ)
    (hθk : θ.ker ≤ Subgroup.center (spinGroup Q)) (hlift : LiftSim Q θ)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hxx' : θ x = θ x')
    (α : MulAut X) (hα4 : α * α * (α * α) = 1)
    (hαR : ∀ r ∈ R, α (θ r) = θ r) (hαR' : ∀ r ∈ R', α (θ r) = θ r) :
    ∃ (fr : OFrame Q) (ŷ : spinGroup Q),
      R.map (spinAction Q) = fr.La.range ∧ R'.map (spinAction Q) = fr.swap.La.range ∧
      spinAction Q x = fr.La (-1) ∧ (∀ g : X, (α * α) g = θ ŷ * g * (θ ŷ)⁻¹) ∧
      spinAction Q ŷ * spinAction Q ŷ = 1 ∧ (∀ s ∈ fr.span, spinAction Q ŷ s = s) ∧
      spinAction Q ŷ ∈ elementaryGroup Q := by
  classical
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨fr, hF₁, hF₁', hθx, -⟩ := swap_of_twin_pair hodd hrange hZ hproj hRp hR'p hR hR'
    hinj hinj' hne hx hx2 hx1 hx' hx'2 hx'1 θ hθk hxx'
  set σ := autRange θ hθs α with hσ
  have hfix : R ⊔ R' ≤ fixerSub θ α := sup_le (fun r hr => hαR r hr) (fun r hr => hαR' r hr)
  have hσc : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥θ.range, σ (θ.rangeRestrict s * ℓ * (θ.rangeRestrict s)⁻¹) =
        θ.rangeRestrict s * σ ℓ * (θ.rangeRestrict s)⁻¹ := by
    intro s hs ℓ
    rw [← hF₁, ← hF₁', ← Subgroup.map_sup] at hs
    obtain ⟨w, hw, hws⟩ := hs
    have hwfix : α (θ w) = θ w := hfix hw
    have hκ : w⁻¹ * s ∈ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hws, inv_mul_cancel])
    have hcc : ∀ g : X, θ (w⁻¹ * s) * g = g * θ (w⁻¹ * s) := by
      intro g
      obtain ⟨t, rfl⟩ := hθs g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hκ t]
    have hθs' : θ s = θ w * θ (w⁻¹ * s) := by rw [← map_mul]; congr 1; group
    have key : ∀ g : X, θ s * g * (θ s)⁻¹ = θ w * g * (θ w)⁻¹ := by
      intro g
      rw [hθs', mul_inv_rev]
      calc θ w * θ (w⁻¹ * s) * g * ((θ (w⁻¹ * s))⁻¹ * (θ w)⁻¹)
          = θ w * (θ (w⁻¹ * s) * g * (θ (w⁻¹ * s))⁻¹) * (θ w)⁻¹ := by group
        _ = θ w * g * (θ w)⁻¹ := by rw [hcc g]; group
    apply Subtype.ext
    show α (θ s * (ℓ : X) * (θ s)⁻¹) = θ s * α (ℓ : X) * (θ s)⁻¹
    rw [key, key, map_mul, map_mul, map_inv, hwfix]
  obtain ⟨α_K, w, hαψ, hwiso, hwspan, hθw⟩ :=
    exists_isometry_of_centralizing hodd h5 hrange fr hθk hlift σ hσc
  have hy_mem : w * w ∈ elementaryGroup Q := sq_mem_of_frame hodd hQ fr hV hwiso
  obtain ⟨ŷ, hŷ, hαα⟩ := exists_sq_lift hrange α_K hy_mem hθw
  have hθα : ∀ s : spinGroup Q, θ (α_K s) = α (θ s) := fun s => by
    have := congrArg Subtype.val (hαψ s)
    exact this
  have hsq : ∀ g : X, (α * α) g = θ ŷ * g * (θ ŷ)⁻¹ := by
    intro g
    obtain ⟨s, rfl⟩ := hθs g
    rw [MulAut.mul_apply, ← hθα, ← hθα, hαα, map_mul, map_mul, map_inv]
  have hspan_y : ∀ s ∈ fr.span, spinAction Q ŷ s = s := fun s hs => by
    rw [hŷ, LinearEquiv.mul_apply, hwspan s hs, hwspan s hs]
  have hy2 : spinAction Q ŷ * spinAction Q ŷ = 1 := by
    have hcent : ∀ g : X, θ (ŷ * ŷ) * g = g * θ (ŷ * ŷ) := by
      intro g
      have h4 := congrArg (fun a : MulAut X => a g) hα4
      simp only [MulAut.mul_apply, MulAut.one_apply, hsq] at h4
      have h5' : θ (ŷ * ŷ) * g * (θ (ŷ * ŷ))⁻¹ = g := by
        rw [map_mul]
        calc θ ŷ * θ ŷ * g * (θ ŷ * θ ŷ)⁻¹
            = θ ŷ * (θ ŷ * g * (θ ŷ)⁻¹) * (θ ŷ)⁻¹ := by group
          _ = g := h4
      calc θ (ŷ * ŷ) * g = θ (ŷ * ŷ) * g * (θ (ŷ * ŷ))⁻¹ * θ (ŷ * ŷ) := by group
        _ = g * θ (ŷ * ŷ) := by rw [h5']
    have hcenter : ŷ * ŷ ∈ Subgroup.center (spinGroup Q) := by
      refine mem_center_of_commutators_central fun t => hθk ?_
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcent (θ t))
    obtain ⟨μ, hμ⟩ := exists_smul_of_central hrange hZ hcenter
    have hne1 : fr.incl 1 ≠ 0 := by
      intro h0
      have := congrArg fr.coords h0
      rw [Frame.coords_incl, map_zero] at this
      exact one_ne_zero (congrFun (congrFun this 0) 0)
    have hv : fr.incl 1 ∈ fr.span := ⟨1, rfl⟩
    have h1 : spinAction Q (ŷ * ŷ) (fr.incl 1) = fr.incl 1 := by
      rw [map_mul, LinearEquiv.mul_apply, hspan_y _ hv, hspan_y _ hv]
    have hμ1 : μ = 1 := by
      have h2 := hμ (fr.incl 1)
      rw [h1] at h2
      have : (μ - 1) • fr.incl 1 = 0 := by rw [sub_smul, ← h2, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hne1)
    rw [← map_mul]
    ext v
    rw [hμ v, hμ1, one_smul]
    rfl
  exact ⟨fr, ŷ, hF₁, hF₁', hθx, hsq, hy2, hspan_y, hŷ ▸ hy_mem⟩

end Main

end CFSG.ClassicalInvolution.RouteD.TWZ
