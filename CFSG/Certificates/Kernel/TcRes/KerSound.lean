module

public import CFSG.Certificates.Kernel.TcRes.CompSound
public import CFSG.Certificates.Kernel.TcRes.SurvSound
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDualFrob
public import CFSG.LocalAnalysis.StandardType.ExcPos.ContainingComponent

public section

namespace CFSG.KC.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes

theorem kernelRoots_frob_image {τ : Tag} {p : ℕ} (φ : AddMonoid.End (Fin τ.rank → ℤ))
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : ∀ γ, IsRoot τ γ → ρ γ = φ γ)
    (hφr : ∀ γ, IsRoot τ γ → IsRoot τ (φ γ)) (c : ZMod p) (Q : Set (Fin τ.rank → ZMod p))
    (hfrob : ∀ v ∈ Q, ∀ j : Fin τ.rank,
      ∑ k, (((ρ (Pi.single j 1)) k : ℤ) : ZMod p) * v k = c * v j) :
    kernelRoots (tcChiQ τ p Q) = ρ '' kernelRoots (tcChiQ τ p Q) := by
  have hmaps : ∀ γ ∈ kernelRoots (tcChiQ τ p Q), ρ γ ∈ kernelRoots (tcChiQ τ p Q) := by
    intro γ hγ
    rw [mem_kernelRoots_chiQ] at hγ ⊢
    refine ⟨by rw [hρ _ hγ.1]; exact hφr _ hγ.1, fun v hv => ?_⟩
    rw [tch_frob_root φ ρ hρ c v (hfrob v hv) γ hγ.1, hγ.2 v hv, mul_zero]
  have hfin := CFSG.StandardType.LieKnownR2.ExcPos.kernelRoots_finite (χ := tcChiQ τ p Q)
  exact ((hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 ρ.injective.injOn).image_eq.symm

theorem orbitLength_one_of_rec
    {τ : Tag} {p N : ℕ} {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool}
    {neg : ℕ → ℕ} (hD : DatumRaw τ N vec rt adj neg) (φ : AddMonoid.End (Fin τ.rank → ℤ))
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : ∀ γ, IsRoot τ γ → ρ γ = φ γ)
    (hφr : ∀ γ, IsRoot τ γ → IsRoot τ (φ γ)) (hiso : ∀ x y, iform (φ x) (φ y) = iform x y)
    (c : ZMod p) (P : Submodule (ZMod p) (Fin τ.rank → ZMod p))
    (hfrob : ∀ v ∈ P, ∀ j : Fin τ.rank,
      ∑ k, (((ρ (Pi.single j 1)) k : ℤ) : ZMod p) * v k = c * v j)
    (Φ : Set ℕ) (hΦ : ∀ g, g ∈ Φ ↔ g < N ∧
      ∀ v ∈ (P : Set (Fin τ.rank → ZMod p)), ∑ m, v m * ((vec g m : ℤ) : ZMod p) = 0)
    {ph : ℕ → ℕ} (hph : ∀ g < N, vec (ph g) = φ (vec g))
    (hrec : ∀ g ∈ Φ, ∃ r ∈ Φ,
      Relation.ReflTransGen (fun a b => a ∈ Φ ∧ b ∈ Φ ∧ iform (vec a) (vec b) ≠ 0) r g ∧
      Relation.ReflTransGen (fun a b => a ∈ Φ ∧ b ∈ Φ ∧ iform (vec a) (vec b) ≠ 0) r (ph r))
    (i : KernelComponent (tcChiPl τ p P)) :
    componentOrbitLength ρ (componentRoots (tcChiPl τ p P) i) = 1 := by
  have hker := kernelRoots_frob_image φ ρ hρ hφr c (P : Set (Fin τ.rank → ZMod p)) hfrob
  refine componentOrbitLength_eq_one_of_paths ρ hker ?_
    (image_eq_kernelRoots hD _ Φ hΦ) ?_ hrec i
  · intro α hα β hβ
    rw [hρ _ ((mem_kernelRoots_chiQ p _ α).1 hα).1, hρ _ ((mem_kernelRoots_chiQ p _ β).1 hβ).1,
      hiso]
  · intro g hg
    have hgN := ((hΦ g).1 hg).1
    rw [hph g hgN, hρ _ (hD.isRoot g hgN)]

end CFSG.KC.TcRes

end
