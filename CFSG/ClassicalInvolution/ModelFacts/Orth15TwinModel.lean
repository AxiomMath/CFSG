module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Model

structure TwinPairOn (t : StatedLieTag) (M : LieUniversal) {H : Type} [Group H] (ψ : M.K →* H)
    (R R' : Subgroup M.K) (x x' : M.K) : Prop where
  ker : ψ.ker ≤ Subgroup.center M.K
  mem : R ∈ fundamentalSubgroups t M.D
  mem' : R' ∈ fundamentalSubgroups t M.D
  ne : R ≠ R'
  comm : Commutes R R'
  hx : x ∈ R
  hx2 : x * x = 1
  hx1 : x ≠ 1
  hx' : x' ∈ R'
  hx'2 : x' * x' = 1
  hx'1 : x' ≠ 1
  same : ψ x = ψ x'

@[expose] def TwinInnerAlphaOn (t : StatedLieTag) (M : LieUniversal) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (ψ : M.K →* H) (R R' : Subgroup M.K) (x x' : M.K),
    TwinPairOn t M ψ R R' x x' → ∀ (u : H) (hun : u ∈ Subgroup.normalizer (ψ.range : Set H)),
      u ∈ R.map ψ ⊔ R'.map ψ → u * u = 1 → u ≠ 1 → u ≠ ψ x →
        alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨u, hun⟩,
          toInducedAutOn ψ.range ⟨ψ x, FrameVertex.mem_normalizer_range ψ x⟩} :
            Set ↥(inducedAutOn ψ.range))) = ⊥

@[expose] def TwinOuterAlphaOn (t : StatedLieTag) (M : LieUniversal) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (ψ : M.K →* H) (R R' : Subgroup M.K) (x x' : M.K),
    TwinPairOn t M ψ R R' x x' → ∀ v : ↥(inducedAutOn ψ.range),
      (∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v) →
      (∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v) →
      v * v * (v * v) = 1 → v * v ≠ 1 → v * v ≠ FrameVertex.innerHom ψ x →
        alphaOf (Subgroup.closure ({FrameVertex.innerHom ψ x, v * v} :
          Set ↥(inducedAutOn ψ.range))) = ⊥

variable (p e : ℕ) [Fact p.Prime]

@[expose] def TwinInnerAlpha (t : StatedLieTag) (n : ℕ) : Prop :=
  TwinInnerAlphaOn t (modelUniv t n p e Fact.out)

@[expose] def TwinOuterAlpha (t : StatedLieTag) (n : ℕ) : Prop :=
  TwinOuterAlphaOn t (modelUniv t n p e Fact.out)

end Model

end CFSG.ClassicalInvolution.Asc77
