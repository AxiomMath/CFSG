module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCoresAbstract

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (fixAll)

@[expose] def FixRigidComm {A M : Type*} [Group A] [Group M] (j : A →* M) (β₀ : MulAut M) :
    Prop :=
  ∀ α : MulAut M, (∀ a, α (j a) = j a) → α * β₀ = β₀ * α → α = 1 ∨ α = β₀

theorem map_apply_eq_of_fixRigidComm_of_odd {M E A : Type*} [Group M] [Group E] [Group A]
    {j : A →* M} {β₀ : MulAut M} (hβ₀ : β₀ * β₀ = 1) (hrig : FixRigidComm j β₀) (Φ : M ≃* E)
    {δ : MulAut M} {c : MulAut E} (hδA : ∀ a, ∃ a', δ⁻¹ (j a) = j a')
    (hfix : ∀ a, c (Φ (j a)) = Φ (δ (j a))) (hδβ : δ * β₀ = β₀ * δ)
    (hcβ : MulAut.congr Φ.symm c * β₀ = β₀ * MulAut.congr Φ.symm c) {m : ℕ} (hm : Odd m)
    (hδm : δ ^ m = 1) (hcm : c ^ m = 1) : ∀ x, Φ (δ x) = c (Φ x) := by
  set γ : MulAut M := MulAut.congr Φ.symm c with hγ
  have hγx : ∀ x, γ x = Φ.symm (c (Φ x)) := fun x => rfl
  have hψ : ∀ a, (γ * δ⁻¹) (j a) = j a := by
    intro a
    obtain ⟨a', ha'⟩ := hδA a
    change γ (δ⁻¹ (j a)) = j a
    rw [ha', hγx, hfix a', MulEquiv.symm_apply_apply, ← ha']
    change (δ * δ⁻¹) (j a) = j a
    rw [mul_inv_cancel]
    rfl
  have hψβ : (γ * δ⁻¹) * β₀ = β₀ * (γ * δ⁻¹) := by
    have hδβ' : δ⁻¹ * β₀ = β₀ * δ⁻¹ := ((Commute.inv_left (show Commute δ β₀ from hδβ))).eq
    rw [mul_assoc, hδβ', ← mul_assoc, hcβ, mul_assoc]
  have hγδ : γ = δ := by
    rcases hrig _ hψ hψβ with h1 | h1
    · exact mul_inv_eq_one.mp h1
    · have hγ' : γ = β₀ * δ := by rw [← h1, inv_mul_cancel_right]
      have hγm : γ ^ m = 1 := by rw [hγ, ← map_pow, hcm, map_one]
      have hcomm : Commute β₀ δ := hδβ.symm
      rw [hγ', hcomm.mul_pow, hδm, mul_one] at hγm
      obtain ⟨k, rfl⟩ := hm
      have hβ2 : β₀ ^ 2 = 1 := by rw [sq, hβ₀]
      rw [pow_succ, pow_mul, hβ2, one_pow, one_mul] at hγm
      rw [hγ', hγm, one_mul]
  intro x
  have h1 := congrArg (fun φ : MulAut M => φ x) hγδ
  change Φ.symm (c (Φ x)) = δ x at h1
  rw [← h1, MulEquiv.apply_symm_apply]

theorem centralizerPerfectCore_eq_map_of_mulEquiv {G M : Type*} [Group G] [Group M] [Finite G]
    [Finite M] {Y T : Subgroup G} (hYT : Y ≤ T) (Φ : M ≃* centralizerPerfectCore Y)
    (α : T → MulAut M)
    (hα : ∀ (d : T) (x : M), ((Φ (α d x) : centralizerPerfectCore Y) : G) =
      (d : G) * (Φ x : G) * (d : G)⁻¹) :
    centralizerPerfectCore T =
      ((perfectCore (fixAll α)).map Φ.toMonoidHom).map (centralizerPerfectCore Y).subtype := by
  have hinj : Function.Injective ((centralizerPerfectCore Y).subtype.comp Φ.toMonoidHom) :=
    (centralizerPerfectCore Y).subtype_injective.comp Φ.injective
  have hker : ((centralizerPerfectCore Y).subtype.comp Φ.toMonoidHom).ker ≤ center M := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
    exact bot_le
  have hrange : ((centralizerPerfectCore Y).subtype.comp Φ.toMonoidHom).range =
      centralizerPerfectCore Y := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 Φ.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  rw [CFSG.SeitzReduction.LinearPilot.centralizerPerfectCore_eq_map_of_le
    ((centralizerPerfectCore Y).subtype.comp Φ.toMonoidHom) hker hYT hrange α hα, map_map]

end CFSG.SeitzReduction.TwistedE6Pilot
