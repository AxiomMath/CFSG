module

public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesFinal
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatRelativeFamily

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

namespace FlatEvery

open CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.FlatComplete CFSG.Wreathed.FlatRelative
  CFSG.Wreathed.ConditionalGlobalDegrees

theorem mem_gen_of_eq_union {ι : Type*} {BB : Finset ι} {m M : ℕ}
    {V : Finset (ZMod m × ZMod m)} {χ₀ χ₁ χ₂ χ₃ χ₄ : ι} {ξ : ℕ → ι} {P Q : ℕ → Fin 2 → ι}
    {ψ : ZMod m × ZMod m → ι}
    (hBB : BB = {χ₀, χ₁, χ₂, χ₃, χ₄} ∪ ((Finset.Ico 1 m).filter Odd).image ξ ∪
      (((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => P x.1 x.2) ∪
        ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Q x.1 x.2)) ∪
      V.image ψ) :
    ∀ I ∈ V, ψ I ∈ BB := fun I hI => by
  rw [hBB]
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem ψ hI)

end FlatEvery

namespace FlatRelative.Support

open CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.FlatComplete CFSG.Wreathed.FlatRelative
  CFSG.Wreathed.ConditionalGlobalDegrees

variable {ι : Type*} {BB : Finset ι} {m M : ℕ} {V : Finset (ZMod m × ZMod m)}
  {X : ZMod m → ι → ℂ} {c : ZMod m → ZMod m → ι → ℂ} {δ₀ δ₁ δ₂ δ₃ δ₄ α γ : ℤ}
  {χ₀ χ₁ χ₂ χ₃ χ₄ : ι} {ξ : ℕ → ι} {P Q : ℕ → Fin 2 → ι} {ψ : ZMod m × ZMod m → ι}
  {er : ℕ → Fin 2}
  (hS : Support BB m M V X c δ₀ δ₁ δ₂ δ₃ δ₄ α γ χ₀ χ₁ χ₂ χ₃ χ₄ ξ P Q ψ er)
include hS

theorem x_gen {I : ZMod m × ZMod m} (hI : I ∈ V) (hψB : ψ I ∈ BB) :
    ∀ j ∈ Finset.Ico 1 m, X j (ψ I) = 0 := by
  obtain ⟨⟨g0, g1, g2, g3, -⟩, gξ, gPQ⟩ := hS.gen_ne hI
  refine x_row_eq (X := fun j => X j (ψ I)) hS.hm (fun _ => 0) (fun h hh => ?_)
    (fun r hr => ?_)
  · rw [hS.Xodd h hh _ hψB]
    simp [g0, g1, g2, g3, gξ h hh]
  · rw [hS.Xeven r hr _ hψB]
    simp [g0, g1, g2, g3, (gPQ r hr 0).1, (gPQ r hr 1).1, (gPQ r hr 0).2, (gPQ r hr 1).2]

theorem c_gen (hVrep : ∀ I, (MulAction.orbit (dualGroup m) I).ncard = 6 →
      ∃! I', I' ∈ V ∧ I' ∈ MulAction.orbit (dualGroup m) I)
    {I : ZMod m × ZMod m} (hI : I ∈ V) (hψB : ψ I ∈ BB) (I' : ZMod m × ZMod m) :
    c I'.1 I'.2 (ψ I) = if I' ∈ MulAction.orbit (dualGroup m) I then (γ : ℂ) else 0 := by
  obtain ⟨⟨g0, g1, g2, g3, g4⟩, -, gPQ⟩ := hS.gen_ne hI
  have h6 := hS.hV6 I hI
  have hdiag : ∀ ρ : ZMod m, ((ρ, ρ) : ZMod m × ZMod m) ∉ MulAction.orbit (dualGroup m) I := by
    intro ρ h
    refine not_mem_orbit_diag_of_six h6 ρ ?_
    rw [MulAction.orbit_eq_iff.mpr h]
    exact MulAction.mem_orbit_self I
  refine pair_eq_of_reps (f := fun I' => c I'.1 I'.2 (ψ I))
    (fun J J' h => hS.inv J J' h _ hψB) (fun J J' h => orbit_indicator_inv I γ h) hS.cov ?_ ?_
    (fun r hr => ?_) (fun r hr => ?_) (fun J hJ => ?_) I'
  · rw [ite_eq_right (hdiag 0)]
    exact hS.c00 _ hψB
  · rw [ite_eq_right (hdiag M)]
    exact (hS.cMM _ hψB).trans (by simp [g0, g1, g2, g3, g4])
  · rw [ite_eq_right (hdiag r)]
    exact ((hS.diag r hr).1 _ hψB).trans (by simp [g0, g1, g4, (gPQ r hr _).1, (gPQ r hr _).2])
  · rw [ite_eq_right (hdiag _)]
    exact ((hS.diag r hr).2 _ hψB).trans (by simp [g0, g1, g4, (gPQ r hr _).1, (gPQ r hr _).2])
  · refine (hS.gen J hJ _ hψB).trans ?_
    by_cases hJI : J = I
    · subst hJI
      rw [ite_eq_left (MulAction.mem_orbit_self _)]
      simp [g0, g1, g4]
    · have hne : ψ I ≠ ψ J := fun h => hJI (hS.ψinj hJ hI h.symm)
      have hJo : J ∉ MulAction.orbit (dualGroup m) I := fun h =>
        hJI ((hVrep I h6).unique ⟨hJ, h⟩ ⟨hI, MulAction.mem_orbit_self _⟩)
      rw [ite_eq_right hJo]
      simp [g0, g1, g4, hne]

theorem values_gen [NeZero m] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (val : ι → ℂ) (lam Φ : ℂ)
    (ε : ℤ)
    (hsec : ∀ χ ∈ BB, 2 * val χ = lam * ((1 - ε * Φ) *
      ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) * X j χ + (1 + ε * Φ) *
        ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) *
          (∑ i : ZMod m, c i (0 - i) χ - ∑ i : ZMod m, c i (-(j : ZMod m) - i) χ)))
    (hVrep : ∀ I, (MulAction.orbit (dualGroup m) I).ncard = 6 →
      ∃! I', I' ∈ V ∧ I' ∈ MulAction.orbit (dualGroup m) I)
    {I : ZMod m × ZMod m} (hI : I ∈ V) (hψB : ψ I ∈ BB) :
    val (ψ I) = -(lam * (1 + ε * Φ) * γ *
      (if Even I.1.val ∧ Even I.2.val then 3 else -1)) := by
  have hval : 2 * val (ψ I) = lam * (1 - ε * Φ) *
      ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) * X j (ψ I) + lam * (1 + ε * Φ) *
        ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * M)) *
          (∑ i : ZMod m, c i (0 - i) (ψ I) - ∑ i : ZMod m, c i (-(j : ZMod m) - i) (ψ I)) := by
    rw [hsec _ hψB]
    ring
  have h := value_six (X := fun j => X (j : ZMod m) (ψ I)) (f := fun i j => c i j (ψ I))
    hS.hm hS.hM hζ (hS.hV6 I hI) (hS.x_gen hI hψB) (fun i j => hS.c_gen hVrep hI hψB (i, j))
    hval
  rw [neg_one_pow_three_sum] at h
  linear_combination h / 2

end FlatRelative.Support

end CFSG.Wreathed
