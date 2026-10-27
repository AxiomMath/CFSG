module

public import CFSG.ClassicalInvolution.RouteD.TWZPair
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TWZ
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.ModelFacts.Orth15
open CFSG.ClassicalInvolution.Q3 (CompData)
open scoped commutatorElement

@[expose] def SqDichotomyC (c : CompData) : Prop :=
  ∀ (X : Type) [Group X] (θ : c.G →* X), Function.Surjective θ → θ.ker ≤ Subgroup.center c.G →
    ∀ (R R' : Subgroup c.G), R ∈ c.fund → R' ∈ c.fund → R ≠ R' →
      ∀ (x x' : c.G), x ∈ R → x * x = 1 → x ≠ 1 → x' ∈ R' → x' * x' = 1 → x' ≠ 1 →
        θ x = θ x' →
        ∀ α : MulAut X, α * α * (α * α) = 1 → (∀ r ∈ R, α (θ r) = θ r) →
          (∀ r ∈ R', α (θ r) = θ r) → α * α = 1 ∨ α * α = MulAut.conj (θ x)

section Generic

variable {S X P : Type} [Group S] [Group X] [Group P]

theorem sq_dichotomy_of_autVac [Group.IsPerfect S] (π : S →* P) (hπ : Function.Surjective π)
    (hπk : π.ker = Subgroup.center S) (θ : S →* X) (hθ : Function.Surjective θ)
    (hθk : θ.ker ≤ Subgroup.center S) {R R' : Subgroup S} {x : S}
    (hvac : ∀ φ : MulAut P, (∀ r ∈ R, φ (π r) = π r) → (∀ r ∈ R', φ (π r) = π r) →
      φ * φ * (φ * φ) = 1 → φ * φ = 1 ∨ φ * φ = MulAut.conj (π x))
    (α : MulAut X) (hα4 : α * α * (α * α) = 1) (hαR : ∀ r ∈ R, α (θ r) = θ r)
    (hαR' : ∀ r ∈ R', α (θ r) = θ r) : α * α = 1 ∨ α * α = MulAut.conj (θ x) := by
  classical
  have hXp : Group.IsPerfect X := Group.IsPerfect.ofSurjective hθ
  have hXtop : (⊤ : Subgroup X) ≤ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := by
    refine le_of_eq ?_
    rw [← commutator_def, Group.IsPerfect.commutator_eq_top]
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
  have hvcomm : ∀ T : Subgroup S, (∀ r ∈ T, α (θ r) = θ r) → ∀ r ∈ T,
      toInducedAutOn ψ'.range ⟨α, hαN⟩ * innerHom ψ' r =
        innerHom ψ' r * toInducedAutOn ψ'.range ⟨α, hαN⟩ := by
    intro T hT r hr
    rw [innerHom_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show α * ψ' r = ψ' r * α
    calc α * ψ' r = (α * MulAut.conj (θ r) * α⁻¹) * α := by
          show α * MulAut.conj (θ r) = (α * MulAut.conj (θ r) * α⁻¹) * α
          group
      _ = MulAut.conj (α (θ r)) * α := by rw [mulAut_mul_conj_mul_inv]
      _ = ψ' r * α := by rw [hT r hr]; rfl
  have hv4 : toInducedAutOn ψ'.range ⟨α, hαN⟩ * toInducedAutOn ψ'.range ⟨α, hαN⟩ *
      (toInducedAutOn ψ'.range ⟨α, hαN⟩ * toInducedAutOn ψ'.range ⟨α, hαN⟩) = 1 := by
    have : (⟨α, hαN⟩ * ⟨α, hαN⟩ * (⟨α, hαN⟩ * ⟨α, hαN⟩) :
        ↥(Subgroup.normalizer ((ψ'.range : Subgroup (MulAut X)) :
          Set (MulAut X)))) = 1 := Subtype.ext hα4
    have h' : toInducedAutOn ψ'.range ⟨α, hαN⟩ * toInducedAutOn ψ'.range ⟨α, hαN⟩ *
        (toInducedAutOn ψ'.range ⟨α, hαN⟩ * toInducedAutOn ψ'.range ⟨α, hαN⟩) =
        toInducedAutOn ψ'.range (⟨α, hαN⟩ * ⟨α, hαN⟩ * (⟨α, hαN⟩ * ⟨α, hαN⟩)) := by
      simp only [map_mul]
    rw [h', this, map_one]
  have hvv : toInducedAutOn ψ'.range ⟨α, hαN⟩ * toInducedAutOn ψ'.range ⟨α, hαN⟩ =
      toInducedAutOn ψ'.range ⟨α * α, Subgroup.mul_mem _ hαN hαN⟩ := by
    rw [← map_mul]
    rfl
  have hinn : ∀ g : X, MulAut.conj g ∈ ψ'.range := by
    intro g
    obtain ⟨m, rfl⟩ := hθ g
    exact ⟨m, rfl⟩
  rcases outer_of_autVac ψ' hker' π hπ hπk (R := R) (R' := R') (x := x) hvac
      (toInducedAutOn ψ'.range ⟨α, hαN⟩) (hvcomm R hαR) (hvcomm R' hαR') hv4 with h | h
  · left
    have key : ∀ g : X, g⁻¹ * (α * α) g ∈ Subgroup.center X := by
      intro g
      have h1 := conj_eq_of_toInducedAutOn_eq ψ'.range
        (n₁ := ⟨α * α, Subgroup.mul_mem _ hαN hαN⟩) (n₂ := 1)
        (by rw [← hvv, h, map_one]) (hinn g)
      simp only at h1
      rw [mulAut_mul_conj_mul_inv] at h1
      exact inv_mul_mem_center_of_conj_eq h1.symm
    refine MulEquiv.ext fun g => ?_
    exact eq_of_perfect_of_central hXtop (α * α) (fun y _ => key y) g trivial
  · right
    have hψx : ψ' x = MulAut.conj (θ x) := rfl
    have key2 : ∀ g : X, (θ x * g * (θ x)⁻¹)⁻¹ * (α * α) g ∈ Subgroup.center X := by
      intro g
      have h1 := conj_eq_of_toInducedAutOn_eq ψ'.range
        (n₁ := ⟨α * α, Subgroup.mul_mem _ hαN hαN⟩)
        (n₂ := ⟨ψ' x, FrameVertex.mem_normalizer_range ψ' x⟩)
        (by rw [← hvv, h, innerHom_apply]) (hinn g)
      simp only at h1
      rw [mulAut_mul_conj_mul_inv, hψx] at h1
      have h2 : MulAut.conj (θ x) * MulAut.conj g * (MulAut.conj (θ x))⁻¹ =
          MulAut.conj (θ x * g * (θ x)⁻¹) := by simp [map_mul, map_inv]
      rw [h2] at h1
      exact inv_mul_mem_center_of_conj_eq h1.symm
    have hβ : ∀ y ∈ (⊤ : Subgroup X),
        y⁻¹ * (MulAut.conj (θ x)⁻¹ * (α * α)) y ∈ Subgroup.center X := by
      intro y _
      have hw := key2 y
      have e : y⁻¹ * (MulAut.conj (θ x)⁻¹ * (α * α)) y =
          (θ x)⁻¹ * ((θ x * y * (θ x)⁻¹)⁻¹ * (α * α) y) * θ x := by
        simp
        group
      rw [e]
      have hc' := Subgroup.mem_center_iff.mp hw (θ x)⁻¹
      have e' : (θ x)⁻¹ * ((θ x * y * (θ x)⁻¹)⁻¹ * (α * α) y) * θ x =
          (θ x * y * (θ x)⁻¹)⁻¹ * (α * α) y :=
        calc (θ x)⁻¹ * ((θ x * y * (θ x)⁻¹)⁻¹ * (α * α) y) * θ x
            = ((θ x * y * (θ x)⁻¹)⁻¹ * (α * α) y) * (θ x)⁻¹ * θ x := by rw [← hc']
          _ = (θ x * y * (θ x)⁻¹)⁻¹ * (α * α) y := by group
      rw [e']
      exact hw
    refine MulEquiv.ext fun g => ?_
    have hβfix := eq_of_perfect_of_central hXtop (MulAut.conj (θ x)⁻¹ * (α * α)) hβ g trivial
    have h3 : (θ x)⁻¹ * (α * α) g * θ x = g := by
      simpa [MulAut.conj_apply] using hβfix
    calc (α * α) g = θ x * ((θ x)⁻¹ * (α * α) g * θ x) * (θ x)⁻¹ := by group
      _ = θ x * g * (θ x)⁻¹ := by rw [h3]
      _ = (MulAut.conj (θ x)) g := by rw [MulAut.conj_apply]

end Generic

theorem sqDichotomyC_of_autVac (c : CompData) [Group.IsPerfect c.G] {P : Type} [Group P]
    (π : c.G →* P) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center c.G)
    (hvac : ∀ (R R' : Subgroup c.G), R ∈ c.fund → R' ∈ c.fund → R ≠ R' →
      ∀ (x x' : c.G), x ∈ R → x * x = 1 → x ≠ 1 → x' ∈ R' → x' * x' = 1 → x' ≠ 1 →
        x' * x⁻¹ ∈ Subgroup.center c.G →
        ∀ φ : MulAut P, (∀ r ∈ R, φ (π r) = π r) → (∀ r ∈ R', φ (π r) = π r) →
          φ * φ * (φ * φ) = 1 → φ * φ = 1 ∨ φ * φ = MulAut.conj (π x)) :
    SqDichotomyC c := by
  intro X _ θ hθ hθk R R' hR hR' hne x x' hx hx2 hx1 hx' hx'2 hx'1 hxx' α hα4 hαR hαR'
  have hc : x' * x⁻¹ ∈ Subgroup.center c.G := by
    apply hθk
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', mul_inv_cancel]
  exact sq_dichotomy_of_autVac π hπ hπk θ hθ hθk
    (hvac R R' hR hR' hne x x' hx hx2 hx1 hx' hx'2 hx'1 hc) α hα4 hαR hαR'

end CFSG.ClassicalInvolution.Q3.Q3TIY
