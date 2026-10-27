module

public import CFSG.ClassicalInvolution.Asc77.AscT7JSq
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterGen

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Asc77.FrameVertex

section Generic

variable {P : Type} [Group P]

theorem twinSqAlphaOn_of_autSq {t : StatedLieTag} (M : LieUniversal) [Group.IsPerfect M.K]
    (π : M.K →* P) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center M.K)
    (hnc : ∀ R ∈ fundamentalSubgroups t M.D, ∀ r ∈ R, r ∈ Subgroup.center M.K → r = 1)
    (hsq : ∀ (R R' : Subgroup M.K) (x x' : M.K), R ∈ fundamentalSubgroups t M.D →
      R' ∈ fundamentalSubgroups t M.D → R ≠ R' → Commutes R R' → x ∈ R → x * x = 1 → x ≠ 1 →
      x' ∈ R' → x' * x' = 1 → x' ≠ 1 → x' * x⁻¹ ∈ Subgroup.center M.K →
      ∀ φ : MulAut P, (∀ r ∈ R, φ (π r) = π r) → (∀ r ∈ R', φ (π r) = π r) →
        φ * φ = MulAut.conj (π x) → φ * φ = 1) :
    TwinSqAlphaOn t M := by
  intro H _ _ ψ R R' x x' hpair k hk hkk v hvR hvR' hvv
  exfalso
  have hc : x' * x⁻¹ ∈ Subgroup.center M.K := by
    apply hpair.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpair.same, mul_inv_cancel]
  have hfix : ∀ r : M.K, v * innerHom ψ r = innerHom ψ r * v →
      outerAction ψ hpair.ker π hπ hπk v (π r) = π r := by
    intro r hr
    apply (outerEquiv ψ hpair.ker π hπ hπk).injective
    apply Subtype.ext
    rw [outerAction_apply, outerEquiv_apply, hr]
    group
  have hφ : outerAction ψ hpair.ker π hπ hπk v * outerAction ψ hpair.ker π hπ hπk v =
      MulAut.conj (π x) := by
    rw [← map_mul, hvv, outerAction_innerHom]
  have h1 := hsq R R' x x' hpair.mem hpair.mem' hpair.ne hpair.comm hpair.hx hpair.hx2 hpair.hx1
    hpair.hx' hpair.hx'2 hpair.hx'1 hc (outerAction ψ hpair.ker π hπ hπk v)
    (fun r hr => hfix r (hvR r hr)) (fun r hr => hfix r (hvR' r hr)) hφ
  have hv2 : v * v = 1 := by
    apply eq_one_of_outerAction_eq_one ψ hpair.ker π hπ hπk
    rw [map_mul, h1]
  have hxker : innerHom ψ x = 1 := by rw [← hvv, hv2]
  have hxπ : x ∈ π.ker := by
    rw [ker_eq_innerHom_ker ψ hpair.ker π hπk, MonoidHom.mem_ker]
    exact hxker
  rw [hπk] at hxπ
  exact hpair.hx1 (hnc R hpair.mem x hpair.hx hxπ)

end Generic

end CFSG.ClassicalInvolution.Asc77
