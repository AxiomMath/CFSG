module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.NormalVector
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GramIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.QuadFromBilin

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V'] [Module (ZMod 2) V']
  [Finite V] [Finite V']

theorem mt0b (q : QuadraticForm (ZMod 2) V) (q' : QuadraticForm (ZMod 2) V')
    (hnd : q.polarBilin.Nondegenerate) (hnd' : q'.polarBilin.Nondegenerate)
    (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V'))
    (hS : Swap.StdHyp σ) (hS' : Swap.StdHyp σ') (hq : ∀ g u, q (σ g u) = q u)
    (hq' : ∀ g u, q' (σ' g u) = q' u) :
    ∃ (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5), (∀ u, q' (a u) = q u) ∧
      ∀ g u, a (σ g u) = σ' (ψ g) (a u) := by
  have hF : FormHyp σ q.polarBilin := by
    refine ⟨?_, ?_, hnd⟩
    · intro g u u'
      have h1 : (σ g) (u + u') = (σ g) u + (σ g) u' := map_add _ _ _
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
      rw [← h1, hq g (u + u'), hq g u, hq g u']
    · intro u
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
      have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
      calc (2 : ℕ) • q u = ((2 : ℕ) : ZMod 2) • q u :=
            (Nat.cast_smul_eq_nsmul (R := ZMod 2) 2 (q u)).symm
        _ = 0 := by rw [h2, zero_smul]
  have hF' : FormHyp σ' q'.polarBilin := by
    refine ⟨?_, ?_, hnd'⟩
    · intro g u u'
      have h1 : (σ' g) (u + u') = (σ' g) u + (σ' g) u' := map_add _ _ _
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
      rw [← h1, hq' g (u + u'), hq' g u, hq' g u']
    · intro u
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
      have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
      calc (2 : ℕ) • q' u = ((2 : ℕ) : ZMod 2) • q' u :=
            (Nat.cast_smul_eq_nsmul (R := ZMod 2) 2 (q' u)).symm
        _ = 0 := by rw [h2, zero_smul]
  obtain ⟨β, v, hv0, hv, hgram⟩ := exists_normal_vector σ q.polarBilin hS hF
  obtain ⟨β', v', hv0', hv', hgram'⟩ := exists_normal_vector σ' q'.polarBilin hS' hF'
  obtain ⟨a, hB, hint⟩ := gram_iso (twist σ β) (twist σ' β') q.polarBilin q'.polarBilin
    (Swap.StdHyp.twist hS β) (Swap.StdHyp.twist hS' β') (hF.twist β) (hF'.twist β') v v' hv hv' hv0 hv0'
    (hgram.trans hgram'.symm)
  have hquad : ∀ u, q' (a u) = q u :=
    quad_isometry_of_bilin (twist σ β) (twist σ' β') q q' (Swap.StdHyp.twist hS β)
      (fun g u => by rw [twist_apply]; exact hq (g.1, β g.2) u)
      (fun g u => by rw [twist_apply]; exact hq' (g.1, β' g.2) u)
      a hB hint
  refine ⟨a, MulEquiv.prodCongr (MulEquiv.refl A5) (β.symm.trans β'), hquad, ?_⟩
  intro g u
  obtain ⟨x, y⟩ := g
  have hσ : σ (x, y) = twist σ β (x, β.symm y) := by
    rw [twist_apply, β.apply_symm_apply]
  have hψ : (MulEquiv.prodCongr (MulEquiv.refl A5) (β.symm.trans β')) (x, y)
      = (x, β' (β.symm y)) := rfl
  rw [hψ, hσ, hint (x, β.symm y) u, twist_apply]


end CFSG.EvenSporadicStandard.HNRecog.ML1
