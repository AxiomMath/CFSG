module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherIntrinsicPoints
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSuborbit

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Module Submodule SymplecticFlag CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type} [Field K]

theorem exists_pointEquiv [Finite K] (hr : 3 ≤ r) (α : MulAut (StatedProj (StatedSp r K))) :
    ∃ f : SpPoint r K ≃ SpPoint r K, ∀ L : SpPoint r K,
      (projStabilizer r K L.line).map α.toMonoidHom = projStabilizer r K (f L).line := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨-, -, hbij, hinv⟩ := intrinsic_points (K := K) p rfl hr
  have hex : ∀ L : SpPoint r K, ∃ L' : SpPoint r K,
      (projStabilizer r K L.line).map α.toMonoidHom = projStabilizer r K L'.line := by
    intro L
    have hmem : (projStabilizer r K L.line).map α.toMonoidHom ∈ spExtremalParabolics r K p := by
      rw [← hinv α]
      exact ⟨_, hbij.mapsTo (Set.mem_univ L), rfl⟩
    obtain ⟨L', -, hL'⟩ := hbij.surjOn hmem
    exact ⟨L', hL'.symm⟩
  choose f₀ hf₀ using hex
  have hinj : Function.Injective f₀ := fun L₁ L₂ h => by
    have h1 : (projStabilizer r K L₁.line).map α.toMonoidHom =
        (projStabilizer r K L₂.line).map α.toMonoidHom := by
      rw [hf₀, hf₀, h]
    exact hbij.injOn (Set.mem_univ _) (Set.mem_univ _)
      (Subgroup.map_injective (f := α.toMonoidHom) α.injective h1)
  exact ⟨Equiv.ofBijective f₀ ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, hf₀⟩

theorem automorphism_orthogonality [Finite K] (hr : 3 ≤ r)
    (α : MulAut (StatedProj (StatedSp r K))) :
    (∃! f : SpPoint r K ≃ SpPoint r K, ∀ L : SpPoint r K,
      (projStabilizer r K L.line).map α.toMonoidHom = projStabilizer r K (f L).line) ∧
    ∀ f : SpPoint r K ≃ SpPoint r K, (∀ L : SpPoint r K,
      (projStabilizer r K L.line).map α.toMonoidHom = projStabilizer r K (f L).line) →
      ∀ L M : SpPoint r K, SpOrth L M ↔ SpOrth (f L) (f M) := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨-, -, hbij, -⟩ := intrinsic_points (K := K) p rfl hr
  obtain ⟨f, hf⟩ := exists_pointEquiv hr α
  refine ⟨⟨f, hf, fun f' hf' => Equiv.ext fun L => hbij.injOn (Set.mem_univ _)
    (Set.mem_univ _) (by rw [← hf', ← hf])⟩, fun f hf L M => ?_⟩
  by_cases hLM : L = M
  · subst hLM
    exact ⟨fun _ => spOrth_self _, fun _ => spOrth_self _⟩
  have hfLM : f L ≠ f M := fun h => hLM (f.injective h)
  obtain ⟨hor, hnor, hlt⟩ := point_suborbit_indices (K := K) rfl (by omega : 2 ≤ r)
  have hidx : (projStabilizer r K (f L).line ⊓ projStabilizer r K (f M).line).relIndex
      (projStabilizer r K (f L).line) =
      (projStabilizer r K L.line ⊓ projStabilizer r K M.line).relIndex
        (projStabilizer r K L.line) := by
    rw [← hf, ← hf, ← Subgroup.map_inf _ _ _ α.injective,
      Subgroup.relIndex_map_map_of_injective _ _ α.injective]
  have hlt' := (hlt (Nat.card K) Finite.one_lt_card).2
  constructor
  · intro h
    by_contra h'
    have e1 := hor L M hLM h
    have e2 := hnor (f L) (f M) hfLM h'
    rw [hidx, e1] at e2
    linarith
  · intro h
    by_contra h'
    have e1 := hor (f L) (f M) hfLM h
    have e2 := hnor L M hLM h'
    rw [hidx, e2] at e1
    linarith

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
