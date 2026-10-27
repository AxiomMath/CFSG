module

public import CFSG.ClassicalInvolution.Asc77.SU4ThreeModel
public import CFSG.ClassicalInvolution.Asc77.SU4Node

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution.RouteD.SU4Pattern
open CFSG.ClassicalInvolution.WeakCT (diagConj2)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

theorem SuLayer.exists_shortNode_centralizer_of_linear [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3) (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {x})
    (Λ : SuLayer p f 2 Ω x) {t : G} (htx : t * x * t⁻¹ = x) (ht2 : t * t = 1)
    {K₂ : Subgroup G} (hK₂ : K₂ ∈ centralizingMembers Ω {x})
    (hK₂i : locImg Ω x K₂ ≤ (Λ.D.hom Λ.i₁).range)
    (θ : SL(2, GaloisField p f) →* locQuot Ω x) (hθr : θ.range = locImg Ω x K₂)
    (hθτ : ∀ s, Gaps.locAut hΩ.conjInvariant htx (θ s) = θ (diagConj2 (-1) 1 s))
    (hlin : LinearLift (Λ.ψ hp2) (Gaps.locAut hΩ.conjInvariant htx)) :
    ∃ Us : Subgroup G, Λ.IsShortNode (minusCoeffs_irr p f) K₂ Us ∧
      Us ≤ Subgroup.centralizer ({t} : Set G) := by
  have hτ : ∀ a, Gaps.locAut hΩ.conjInvariant htx (Gaps.locAut hΩ.conjInvariant htx a) = a :=
    Gaps.locAut_locAut hΩ.conjInvariant htx ht2
  obtain ⟨R, hR, hMR⟩ := Λ.exists_longRoot_of_mem hp2 hΩ hP1 hK₂ hK₂i
  have := fact_shortField (minusCoeffs_irr p f)
  obtain ⟨S, W, hpair, hRS, hfix⟩ := exists_fixed_shortPair_linear hp2 hq hq3
    (spinMinus6Generated_galois hp2) (Λ.ψ hp2) (Λ.ψ_spec hp2).1
    (Gaps.locAut hΩ.conjInvariant htx) hτ hR θ (hθr.trans hMR) hθτ hlin
  obtain ⟨Us, hsn, hUsimg⟩ := Λ.exists_shortNode_of_pair hp2 hq hΩ hP1
    (spinMinus6Generated_galois hp2) (spinMinus6_noCover_galois hp2 hq) hK₂ hK₂i hMR hpair hRS
  refine ⟨Us, hsn, ?_⟩
  obtain ⟨hUsY, hUsperf, -⟩ := hsn
  refine (locAut_fixed_iff_of_perfect hΩ hP1 htx hUsY hUsperf.ge).2 ?_
  intro a ha
  rw [hUsimg] at ha
  obtain ⟨y, hy, rfl⟩ := ha
  exact hfix y hy

end CFSG.ClassicalInvolution.RouteD
