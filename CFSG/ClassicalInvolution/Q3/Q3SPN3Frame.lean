module

public import CFSG.ClassicalInvolution.Q3.Q3SPN3Core
public import CFSG.ClassicalInvolution.Q3.Q3TY14
public import CFSG.ClassicalInvolution.Q3.Q3EPQuot

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3SPN3

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.SPN CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped commutatorElement MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

theorem spinGen_of_frame3 (hodd : Odd (Nat.card F)) (hF3 : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c)
    (hV : 7 ≤ Module.finrank F (ι → F)) {ψ : spinGroup Q →* H}
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q)) (hlift : LiftSimFr Q ψ)
    {R R' : Subgroup (spinGroup Q)} {x : spinGroup Q} (F₁ : OFrame Q)
    (hF₁ : R.map (spinAction Q) = F₁.La.range) (hF₁' : R'.map (spinAction Q) = F₁.swap.La.range)
    (hθx : spinAction Q x = F₁.La (-1)) (s : H) (hs : s ∈ Subgroup.normalizer (ψ.range : Set H))
    (hss : s * s = 1) (hsR : ∀ r ∈ R, s * ψ r = ψ r * s) (hsR' : ∀ r ∈ R', s * ψ r = ψ r * s) :
    (∀ y ∈ ψ.range, s * y = y * s) ∨ (∀ y ∈ ψ.range, s * y * s⁻¹ = ψ x * y * (ψ x)⁻¹) ∨
      (∀ q ∈ ψ.range, q ∈ Subgroup.closure ({q | q ∈ ψ.range ∧ s * q = q * s} ∪
        {q | q ∈ ψ.range ∧ ψ x * q = q * ψ x})) := by
  classical
  set v : ↥(inducedAutOn ψ.range) := toInducedAutOn ψ.range ⟨s, hs⟩ with hvdef
  have hvc : ∀ g : spinGroup Q, s * ψ g = ψ g * s →
      v * toInducedAutOn ψ.range ⟨ψ g, mem_normalizer_range ψ g⟩ =
        toInducedAutOn ψ.range ⟨ψ g, mem_normalizer_range ψ g⟩ * v := by
    intro g hg
    rw [hvdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hg
  have hvR : ∀ r ∈ R, v * spinInd ψ r = spinInd ψ r * v := fun r hr => hvc r (hsR r hr)
  have hvR' : ∀ r ∈ R', v * spinInd ψ r = spinInd ψ r * v := fun r hr => hvc r (hsR' r hr)
  have hv : ∀ g : spinGroup Q, spinAction Q g ∈ F₁.La.range ⊔ F₁.swap.La.range →
      v * toInducedAutOn ψ.range ⟨ψ g, mem_normalizer_range ψ g⟩ =
        toInducedAutOn ψ.range ⟨ψ g, mem_normalizer_range ψ g⟩ * v := by
    intro g hg
    rw [← hF₁, ← hF₁'] at hg
    exact commute_spinInd_of_mem_map_sup (ker_spinAction_le_center Q) ψ v hvR hvR' hg
  have hσ : ∀ g : spinGroup Q, spinAction Q g ∈ F₁.La.range ⊔ F₁.swap.La.range →
      ∀ ℓ : ↥ψ.range, (v : MulAut ↥ψ.range) (ψ.rangeRestrict g * ℓ * (ψ.rangeRestrict g)⁻¹) =
        ψ.rangeRestrict g * (v : MulAut ↥ψ.range) ℓ * (ψ.rangeRestrict g)⁻¹ := by
    intro g hg ℓ
    have h := congrArg (fun a : ↥(inducedAutOn ψ.range) => ((a : MulAut ↥ψ.range) ℓ : ↥ψ.range))
      (hv g hg)
    exact Subtype.ext (congrArg Subtype.val h)
  exact spinGen_core3 hodd hF3 hQ hrange hZ3 F₁ hV hψ hθx s hs hss
    (hlift F₁ (v : MulAut ↥ψ.range) hσ) hv

end Frame

section Transport


variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)}

theorem spinGenOn_of_spin3 (hodd : Odd (Nat.card F)) (hF3 : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q)
    (hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c)
    (hV : 7 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    (hlift : ∀ (H : Type) [Group H] [Finite H] (ψ : spinGroup Q →* H),
      ψ.ker ≤ Subgroup.center (spinGroup Q) → LiftSimFr Q ψ)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    {Z' : Subgroup ((ι → F) ≃ₗ[F] (ι → F))}
    (cq : Q3W.CentralQuot3 (spinAction Q) (Generic.fundamentalSubgroups t D) (fundSet Q) Z') :
    SpinGenOn t ⟨spinGroup Q, D⟩ := by
  intro H _ _ ψ R R' x x' hpair s hs hss hsR hsR'
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨F₁, hF₁, hF₁', hθx, -⟩ := Q3TY.swap_of_twin_pair3 hodd hrange hZ hproj
    (fun e => cq.map_inj hpair.mem hpair.mem' e) (cq.map_mem R hpair.mem)
    (cq.map_mem R' hpair.mem') (cq.inj R hpair.mem) (cq.inj R' hpair.mem') hpair.ne hpair.hx
    hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 ψ hpair.ker hpair.same
  exact spinGen_of_frame3 hodd hF3 hQ hrange hZ3 hV hpair.ker (hlift H ψ hpair.ker) F₁ hF₁ hF₁'
    hθx s hs hss hsR hsR'

end Transport

end CFSG.ClassicalInvolution.Q3.Q3SPN3
