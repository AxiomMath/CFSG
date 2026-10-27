module

public import Certificates.Certificate214108

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.Torality

namespace E7Plane

theorem e7Plane_pair
    (φ ψ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Z3) {w : WeylGroup .E7}
    (hφ : w ∈ charStabilizer φ) (hψ : w ∈ charStabilizer ψ) :
    w ∈ kernelWeylGroup (φ.prod ψ) ∨ CyclicTriple .E7 (kernelRoots (φ.prod ψ)) w :=
  Certificates.certificate214108 φ ψ w hφ hψ

end E7Plane

open E7Plane in
theorem e7ThreeKilledPlaneBlocks_holds :
    E7ThreeKilledPlaneBlocks := by
  intro L _ a h3 _ w hw
  obtain ⟨φ, hstab, hS, hW⟩ := exists_triChar_pair a h3
  rcases e7Plane_pair (φ 0) (φ 1) ((hstab 0 w).1 (hw 0)) ((hstab 1 w).1 (hw 1)) with h | h
  · left
    rw [hW]
    exact h
  · right
    rw [hS]
    exact exists_kernelBlocks_of_cyclicTriple h

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore
