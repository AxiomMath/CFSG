module

public import CFSG.ClassicalInvolution.RouteD.MultiStarModel
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterGen
import CFSG.ClassicalInvolution.Asc77.WP3SCUBGL
import CFSG.ClassicalInvolution.ModelFacts.Orth15Aut

public section

namespace CFSG.ClassicalInvolution.Asc77.SCV

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank

section Bridge

theorem toInduced_commute_innerHom {S H : Type} [Group S] [Group H] (ψ : S →* H) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) {r : S} (h : v * ψ r = ψ r * v) :
    toInducedAutOn ψ.range ⟨v, hv⟩ * innerHom ψ r =
      innerHom ψ r * toInducedAutOn ψ.range ⟨v, hv⟩ := by
  rw [innerHom_apply, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h

theorem commute_of_toInduced_commute {S H : Type} [Group S] [Group H] (ψ : S →* H)
    {R' : Subgroup S} (hR' : ⁅R', R'⁆ = R') {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H))
    (h : ∀ s ∈ R', toInducedAutOn ψ.range ⟨v, hv⟩ * innerHom ψ s =
      innerHom ψ s * toInducedAutOn ψ.range ⟨v, hv⟩) :
    ∀ s ∈ R', v * ψ s = ψ s * v := by
  classical
  set L : Subgroup H := ψ.range with hL
  have hmemL : ∀ s, v * ψ s * v⁻¹ * (ψ s)⁻¹ ∈ L := fun s =>
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp hv (ψ s)).mp ⟨s, rfl⟩) (L.inv_mem ⟨s, rfl⟩)
  have hcent : ∀ s ∈ R', (⟨v * ψ s * v⁻¹ * (ψ s)⁻¹, hmemL s⟩ : ↥L) ∈ Subgroup.center ↥L := by
    intro s hs
    set m : ↥(Subgroup.normalizer (L : Set H)) :=
      ⟨ψ s, FrameVertex.mem_normalizer_range ψ s⟩ with hm
    set n : ↥(Subgroup.normalizer (L : Set H)) := ⟨v, hv⟩ with hn
    have hxc : toInducedAutOn L n * toInducedAutOn L m =
        toInducedAutOn L m * toInducedAutOn L n := by
      have := h s hs
      rwa [innerHom_apply] at this
    have h1 : toInducedAutOn L (n * m * n⁻¹ * m⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hxc]
      group
    have hc := Lemma52Proof.commute_of_toInducedAutOn_eq_one L (n * m * n⁻¹ * m⁻¹).2 h1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g.1 g.2).symm
  let φ : ↥L →* ↥L := ((toInducedAutOn L ⟨v, hv⟩ : ↥(inducedAutOn L)) : MulAut ↥L).toMonoidHom
  have hφ : ∀ ℓ : ↥L, (φ ℓ : H) = v * ℓ * v⁻¹ := fun ℓ => toInducedAutOn_apply_coe ⟨v, hv⟩ ℓ
  have hP : ⁅R'.map ψ.rangeRestrict, R'.map ψ.rangeRestrict⁆ = R'.map ψ.rangeRestrict := by
    rw [← Subgroup.map_commutator, hR']
  have hfix := CFSG.ClassicalInvolution.Asc77.eq_of_central_ratio φ hP (fun p hp => by
    obtain ⟨s, hs, rfl⟩ := hp
    have e : φ (ψ.rangeRestrict s) * (ψ.rangeRestrict s)⁻¹ =
        ⟨v * ψ s * v⁻¹ * (ψ s)⁻¹, hmemL s⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hφ, Subgroup.coe_inv]
      rfl
    rw [e]
    exact hcent s hs)
  intro s hs
  have h1 := hfix (ψ.rangeRestrict s) ⟨s, hs, rfl⟩
  have h2 : v * ψ s * v⁻¹ = ψ s := by
    have := congrArg Subtype.val h1
    rw [hφ] at this
    exact this
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2

theorem outer_fix_of_sq_one {S H P : Type} [Group S] [Group H] [Group P] [Group.IsPerfect S]
    (ψ : S →* H) (hψ : ψ.ker ≤ Subgroup.center S) (π : S →* P) (hπ : Function.Surjective π)
    (hπk : π.ker = Subgroup.center S) {R R' : Subgroup S}
    (hvac : ∀ φ : MulAut P, φ * φ = 1 → (∀ r ∈ R, φ (π r) = π r) → ∀ r ∈ R', φ (π r) = π r)
    (v : ↥(inducedAutOn ψ.range)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ R, v * innerHom ψ r = innerHom ψ r * v) :
    ∀ r ∈ R', v * innerHom ψ r = innerHom ψ r * v := by
  have hfix : ∀ r : S, v * innerHom ψ r = innerHom ψ r * v →
      outerAction ψ hψ π hπ hπk v (π r) = π r := by
    intro r hr
    apply (outerEquiv ψ hψ π hπ hπk).injective
    apply Subtype.ext
    rw [outerAction_apply, outerEquiv_apply, hr]
    group
  have hφ2 : outerAction ψ hψ π hπ hπk v * outerAction ψ hψ π hπ hπk v = 1 := by
    rw [← map_mul, hv2, map_one]
  intro r hr
  have h1 := hvac _ hφ2 (fun r hr => hfix r (hvR r hr)) r hr
  have h2 := outerAction_apply ψ hψ π hπ hπk v (π r)
  rw [h1, outerEquiv_apply] at h2
  calc v * innerHom ψ r = (v * innerHom ψ r * v⁻¹) * v := by group
    _ = innerHom ψ r * v := by rw [← h2]

end Bridge

section Sigma

variable (p : ℕ) [Fact p.Prime]

@[expose] def SmallSigma (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ e → StatedLieAdmissible t n p e →
    ∀ {H : Type} [Group H] (ψ : (modelUniv t n p e Fact.out).K →* H),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K →
      ∀ {R R' : Subgroup (modelUniv t n p e Fact.out).K},
        R ∈ ModelFund p t n e → R' ∈ ModelFund p t n e → R ≠ R' → Commutes R R' →
        ∀ {x x' : (modelUniv t n p e Fact.out).K},
          x ∈ R → x * x = 1 → x ≠ 1 → x' ∈ R' → x' * x' = 1 → x' ≠ 1 →
          x * x' ∈ Subgroup.center (modelUniv t n p e Fact.out).K →
          ∀ v : ↥(inducedAutOn ψ.range), v * v = 1 →
            (∀ r ∈ R, v * innerHom ψ r = innerHom ψ r * v) →
              ∀ s ∈ R', v * innerHom ψ s = innerHom ψ s * v

@[expose] def SmallSigmaFacts : Prop :=
  ∀ e : ℕ, SmallSigma p .PSp 2 e ∧ SmallSigma p .POmegaOdd 3 e ∧ SmallSigma p .POmegaMinus 4 e

end Sigma

end CFSG.ClassicalInvolution.Asc77.SCV
