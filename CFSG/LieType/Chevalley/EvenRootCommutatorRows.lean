module

public import CFSG.LieType.Chevalley.EvenRootCommutatorTransport

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley RootOps
open scoped commutatorElement

variable {τ : Tag}

theorem exists_pairTable_commutatorElement_of_two_eq_zero
    {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) :
    ∃ r ∈ pairTable τ, ∃ w : WeylGroup τ,
      w • orbitCertRoot τ r.1 = α ∧ w • orbitCertRoot τ r.2.1 = β ∧
      (∀ f ∈ r.2.2.2, IsRoot τ (f.1 • α + f.2.1 • β)) ∧
      ∀ (R : Type*) [CommRing R], (2 : R) = 0 → ∀ x y : R,
        ⁅pinnedX τ R α x, pinnedX τ R β y⁆ =
          (r.2.2.2.map fun f => pinnedX τ R (f.1 • α + f.2.1 • β)
            ((f.2.2.2 : R) * x ^ f.1 * y ^ f.2.1)).prod := by
  obtain ⟨r, ⟨hr, horb⟩, -⟩ := (rank_two_pair_certificate τ).1 α β hα hβ hne hne'
  obtain ⟨w, hw⟩ := MulAction.mem_orbit_iff.1 horb
  rw [Prod.smul_mk, Prod.mk.injEq] at hw
  have hfac := ((rank_two_pair_certificate τ).2 r hr).2.2.2.2.2.2.2.2.1
  have hγ : ∀ f ∈ r.2.2.2, w • orbitCertRoot τ f.2.2.1 = f.1 • α + f.2.1 • β := fun f hf => by
    rw [((hfac f.1 f.2.1 f.2.2.1).1 ⟨f.2.2.2, hf⟩).2.2.2, smul_add, smul_comm, smul_comm w f.2.1,
      hw.1, hw.2]
  refine ⟨r, hr, w, hw.1, hw.2, fun f hf => ?_, fun R _ h2 x y => ?_⟩
  · rw [← hγ f hf]
    exact IsRoot.smul (isRoot_decodeVec_witness ((hfac f.1 f.2.1 f.2.2.1).1 ⟨f.2.2.2, hf⟩).2.2.1) w
  · rw [commutatorElement_pinnedX_of_two_eq_zero h2 hr w hw.1 hw.2 x y]
    exact congrArg List.prod (List.map_congr_left fun f hf => by rw [hγ f hf])

end CFSG.LieType.Chevalley
