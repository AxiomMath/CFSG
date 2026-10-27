module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinModel

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex

section Outer

variable {S H P : Type} [Group S] [Group H] [Group P]

theorem ker_eq_innerHom_ker [Group.IsPerfect S] (ψ : S →* H) (hψ : ψ.ker ≤ Subgroup.center S)
    (π : S →* P) (hπk : π.ker = Subgroup.center S) : π.ker = (innerHom ψ).ker := by
  refine le_antisymm (fun s hs => ?_) (fun s hs => ?_)
  · rw [hπk] at hs
    rw [MonoidHom.mem_ker, innerHom_apply]
    exact Lemma52Proof.toInducedAutOn_eq_one_of_commute _ (mem_normalizer_range ψ s)
      (fun y hy => by
        obtain ⟨t, rfl⟩ := hy
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hs t])
  · rw [hπk]
    exact (innerHom_spec ψ hψ).1 s hs

noncomputable def outerEquiv [Group.IsPerfect S] (ψ : S →* H) (hψ : ψ.ker ≤ Subgroup.center S)
    (π : S →* P) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center S) :
    P ≃* ↥(innerHom ψ).range :=
  (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_eq_innerHom_ker ψ hψ π hπk)).trans
      (QuotientGroup.quotientKerEquivRange _))

theorem outerEquiv_apply [Group.IsPerfect S] (ψ : S →* H) (hψ : ψ.ker ≤ Subgroup.center S)
    (π : S →* P) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center S) (s : S) :
    ((outerEquiv ψ hψ π hπ hπk (π s) : ↥(innerHom ψ).range) : ↥(inducedAutOn ψ.range)) =
      innerHom ψ s := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π s) =
      (s : S ⧸ π.ker) := (MulEquiv.symm_apply_eq _).mpr rfl
  show ((QuotientGroup.quotientKerEquivRange (innerHom ψ))
    ((QuotientGroup.quotientMulEquivOfEq (ker_eq_innerHom_ker ψ hψ π hπk))
      ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π s))) :
        ↥(inducedAutOn ψ.range)) = innerHom ψ s
  rw [h1, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

noncomputable def outerAction [Group.IsPerfect S] (ψ : S →* H) (hψ : ψ.ker ≤ Subgroup.center S)
    (π : S →* P) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center S) :
    ↥(inducedAutOn ψ.range) →* MulAut P :=
  have : (innerHom ψ).range.Normal := (innerHom_spec ψ hψ).2.1
  (MulAut.congr (outerEquiv ψ hψ π hπ hπk).symm).toMonoidHom.comp MulAut.conjNormal

theorem outerAction_apply [Group.IsPerfect S] (ψ : S →* H) (hψ : ψ.ker ≤ Subgroup.center S)
    (π : S →* P) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center S)
    (w : ↥(inducedAutOn ψ.range)) (p : P) :
    ((outerEquiv ψ hψ π hπ hπk (outerAction ψ hψ π hπ hπk w p) : ↥(innerHom ψ).range) :
      ↥(inducedAutOn ψ.range)) =
      w * ((outerEquiv ψ hψ π hπ hπk p : ↥(innerHom ψ).range) : ↥(inducedAutOn ψ.range)) *
        w⁻¹ := by
  have : (innerHom ψ).range.Normal := (innerHom_spec ψ hψ).2.1
  have h : outerAction ψ hψ π hπ hπk w p = (outerEquiv ψ hψ π hπ hπk).symm
      (MulAut.conjNormal w (outerEquiv ψ hψ π hπ hπk p)) := rfl
  rw [h, MulEquiv.apply_symm_apply]
  simp [MulAut.conjNormal_apply]

theorem eq_one_of_outerAction_eq_one [Group.IsPerfect S] (ψ : S →* H)
    (hψ : ψ.ker ≤ Subgroup.center S) (π : S →* P) (hπ : Function.Surjective π)
    (hπk : π.ker = Subgroup.center S) {w : ↥(inducedAutOn ψ.range)}
    (hw : outerAction ψ hψ π hπ hπk w = 1) : w = 1 := by
  refine (innerHom_spec ψ hψ).2.2 w fun y hy => ?_
  have h1 := outerAction_apply ψ hψ π hπ hπk w ((outerEquiv ψ hψ π hπ hπk).symm ⟨y, hy⟩)
  rw [hw, MulEquiv.apply_symm_apply] at h1
  simp only [MulAut.one_apply, MulEquiv.apply_symm_apply] at h1
  have h2 : (y : ↥(inducedAutOn ψ.range)) = w * y * w⁻¹ := h1
  calc w * y = (w * y * w⁻¹) * w := by group
    _ = y * w := by rw [← h2]

theorem outerAction_innerHom [Group.IsPerfect S] (ψ : S →* H) (hψ : ψ.ker ≤ Subgroup.center S)
    (π : S →* P) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center S) (x : S) :
    outerAction ψ hψ π hπ hπk (innerHom ψ x) = MulAut.conj (π x) := by
  ext p
  obtain ⟨s, rfl⟩ := hπ p
  apply (outerEquiv ψ hψ π hπ hπk).injective
  apply Subtype.ext
  rw [outerAction_apply, outerEquiv_apply]
  show _ = ((outerEquiv ψ hψ π hπ hπk (π x * π s * (π x)⁻¹) : ↥(innerHom ψ).range) :
    ↥(inducedAutOn ψ.range))
  rw [show π x * π s * (π x)⁻¹ = π (x * s * x⁻¹) by simp [map_mul, map_inv],
    outerEquiv_apply]
  simp only [map_mul, map_inv]

theorem outer_of_autVac [Group.IsPerfect S] (ψ : S →* H) (hψ : ψ.ker ≤ Subgroup.center S)
    (π : S →* P) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center S)
    {R R' : Subgroup S} {x : S}
    (hvac : ∀ φ : MulAut P, (∀ r ∈ R, φ (π r) = π r) → (∀ r ∈ R', φ (π r) = π r) →
      φ * φ * (φ * φ) = 1 → φ * φ = 1 ∨ φ * φ = MulAut.conj (π x))
    (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * innerHom ψ r = innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * innerHom ψ r = innerHom ψ r * v)
    (hv4 : v * v * (v * v) = 1) : v * v = 1 ∨ v * v = innerHom ψ x := by
  have hfix : ∀ r : S, v * innerHom ψ r = innerHom ψ r * v →
      outerAction ψ hψ π hπ hπk v (π r) = π r := by
    intro r hr
    apply (outerEquiv ψ hψ π hπ hπk).injective
    apply Subtype.ext
    rw [outerAction_apply, outerEquiv_apply, hr]
    group
  have hφ4 : outerAction ψ hψ π hπ hπk v * outerAction ψ hψ π hπ hπk v *
      (outerAction ψ hψ π hπ hπk v * outerAction ψ hψ π hπ hπk v) = 1 := by
    simpa only [map_mul, map_one] using congrArg (outerAction ψ hψ π hπ hπk) hv4
  rcases hvac _ (fun r hr => hfix r (hvR r hr)) (fun r hr => hfix r (hvR' r hr)) hφ4 with h | h
  · left
    apply eq_one_of_outerAction_eq_one ψ hψ π hπ hπk
    rw [map_mul, h]
  · right
    have h1 : outerAction ψ hψ π hπ hπk (v * v) = outerAction ψ hψ π hπ hπk (innerHom ψ x) := by
      rw [map_mul, h, outerAction_innerHom]
    have h2 : (innerHom ψ x)⁻¹ * (v * v) = 1 := by
      apply eq_one_of_outerAction_eq_one ψ hψ π hπ hπk
      rw [map_mul, map_inv, ← h1]
      simp
    exact (inv_mul_eq_one.mp h2).symm

end Outer

section Model

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

variable {P : Type} [Group P]

theorem twinOuterAlphaOn_of_autVac {t : StatedLieTag} (M : LieUniversal) [Group.IsPerfect M.K]
    (π : M.K →* P) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center M.K)
    (hvac : ∀ (R R' : Subgroup M.K) (x x' : M.K), R ∈ fundamentalSubgroups t M.D →
      R' ∈ fundamentalSubgroups t M.D → R ≠ R' → Commutes R R' → x ∈ R → x * x = 1 → x ≠ 1 →
      x' ∈ R' → x' * x' = 1 → x' ≠ 1 → x' * x⁻¹ ∈ Subgroup.center M.K →
      ∀ φ : MulAut P, (∀ r ∈ R, φ (π r) = π r) → (∀ r ∈ R', φ (π r) = π r) →
        φ * φ * (φ * φ) = 1 → φ * φ = 1 ∨ φ * φ = MulAut.conj (π x)) :
    TwinOuterAlphaOn t M := by
  intro H _ _ ψ R R' x x' hpair v hvR hvR' hv4 hv2 hv2x
  have hc : x' * x⁻¹ ∈ Subgroup.center M.K := by
    apply hpair.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpair.same, mul_inv_cancel]
  rcases outer_of_autVac ψ hpair.ker π hπ hπk (R := R) (R' := R') (x := x)
    (hvac R R' x x' hpair.mem hpair.mem' hpair.ne hpair.comm hpair.hx hpair.hx2 hpair.hx1
      hpair.hx' hpair.hx'2 hpair.hx'1 hc) v hvR hvR' hv4 with h | h
  · exact absurd h hv2
  · exact absurd h hv2x

end Model

end CFSG.ClassicalInvolution.ModelFacts.Orth15
