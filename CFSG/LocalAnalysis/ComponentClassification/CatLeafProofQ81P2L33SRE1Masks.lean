module

public import CFSG.LieType.Chevalley.RationalToralSignDiagramE7
public import CFSG.LieType.Chevalley.RationalToralSignDiagramE6

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR.E1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint

section Check

variable {τ : Tag} (C : RootCertificate τ)

@[expose] def kernelPairCheck (m : ℕ) : Bool :=
  (List.range C.roots.length).any fun i => inKernel C m i &&
    (List.range C.roots.length).any fun j =>
      inKernel C m j && decide (cpair (C.root i) (C.root j) = 1)

variable {C}

theorem exists_pair_of_check (hC : C.check = true) (hS : τ.symmetrizedCartan = τ.cartan)
    {m : ℕ} (h : kernelPairCheck C m = true) :
    ∃ β ∈ kernelRoots (signMaskChar τ m), ∃ γ ∈ kernelRoots (signMaskChar τ m),
      iform β γ = 1 := by
  simp only [kernelPairCheck, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨i, hi, hki, j, hj, hkj, hc⟩ := h
  exact ⟨C.root i, (mem_kernelRoots_iff hC).2 ⟨i, hi, rfl, hki⟩, C.root j,
    (mem_kernelRoots_iff hC).2 ⟨j, hj, rfl, hkj⟩, (iform_eq_cpair hS _ _).trans hc⟩

end Check

theorem e7_symmetrizedCartan_eq : Tag.E7.symmetrizedCartan = Tag.E7.cartan := by
  change Tag.E7.symmetrizer * Tag.E7.cartan = Tag.E7.cartan
  rw [show Tag.E7.symmetrizer = 1 from rfl, one_mul]

theorem e6_symmetrizedCartan_eq : Tag.E6.symmetrizedCartan = Tag.E6.cartan := by
  change Tag.E6.symmetrizer * Tag.E6.cartan = Tag.E6.cartan
  rw [show Tag.E6.symmetrizer = 1 from rfl, one_mul]

theorem e7_kernelPairCheck :
    ([0, 1, 2, 3] : List ℕ).all (kernelPairCheck e7Certificate) = true := by
  decide +kernel

theorem e6_kernelPairCheck :
    ([0, 20, 2] : List ℕ).all (kernelPairCheck e6Certificate) = true := by
  decide +kernel

theorem e7_exists_pair : ∀ r ∈ e7SignDiagramReps, ∃ β ∈ kernelRoots (signMaskChar Tag.E7 r.mask),
    ∃ γ ∈ kernelRoots (signMaskChar Tag.E7 r.mask), iform β γ = 1 := by
  intro r hr
  have hm : r.mask ∈ ([0, 1, 2, 3] : List ℕ) := by
    simp only [e7SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  exact exists_pair_of_check e7Certificate_check e7_symmetrizedCartan_eq
    (List.all_eq_true.1 e7_kernelPairCheck _ hm)

theorem e6_exists_pair : ∀ r ∈ e6SignDiagramReps, ∃ β ∈ kernelRoots (signMaskChar Tag.E6 r.mask),
    ∃ γ ∈ kernelRoots (signMaskChar Tag.E6 r.mask), iform β γ = 1 := by
  intro r hr
  have hm : r.mask ∈ ([0, 20, 2] : List ℕ) := by
    simp only [e6SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  exact exists_pair_of_check e6Certificate_check e6_symmetrizedCartan_eq
    (List.all_eq_true.1 e6_kernelPairCheck _ hm)

end CFSG.ComponentClassification.HarrisLit.L33.SR.E1
