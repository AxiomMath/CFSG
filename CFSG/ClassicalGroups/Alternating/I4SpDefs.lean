module

public import CFSG.Assembly.Defs
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixed

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)

variable {K N : Type*} [Field K] [AddCommGroup N] [Module K N] {BN : BilinForm K N}

@[expose] noncomputable def lineElt (hBN : BN.IsAlt) (a c : N) : Gsp BN :=
  ⟨siegel BN hBN a c 0, siegel_mem_bilinIsometryGroup hBN a c 0⟩

@[expose] noncomputable def lineGroup (hBN : BN.IsAlt) (a c : N) : Subgroup (Gsp BN) :=
  Subgroup.closure (Set.range fun l : K => lineElt hBN a (l • c))

@[expose] noncomputable def planeGroup (hBN : BN.IsAlt) (π : Submodule K N) : Subgroup (Gsp BN) :=
  Subgroup.closure {g | ∃ a ∈ π, ∃ c ∈ π, g = lineElt hBN a c}

theorem lineElt_app (hBN : BN.IsAlt) {a c : N} (hac : BN a c = 0) (x : N) :
    (lineElt hBN a c).app x = x + BN x a • c + BN x c • a := by
  change (siegel BN hBN a c 0 : N →ₗ[K] N) x = _
  rw [siegel_apply hBN hac, zero_mul, zero_smul, add_zero]

end CFSG.ClassicalGroups.Alternating
