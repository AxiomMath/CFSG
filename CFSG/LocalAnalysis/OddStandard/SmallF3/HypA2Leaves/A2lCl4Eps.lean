module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem cl24_polar_e_of_mem_perp (P : HypPair Q) {w : V} (hw : w ∈ P.perp) :
    polar Q P.e w = 0 :=
  (HypPair.mem_perp.1 hw).1

@[expose] noncomputable def cl24_eps (P : HypPair Q) (w : P.perp) : elementaryGroup Q :=
  ⟨eichler Q P.e w, eichler_mem_elementaryGroup Q P.e w⟩

theorem cl24_eps_add (P : HypPair Q) (v w : P.perp) :
    cl24_eps P (v + w) = cl24_eps P v * cl24_eps P w :=
  Subtype.ext (eichler_mul (cl24_polar_e_of_mem_perp P v.2) (cl24_polar_e_of_mem_perp P w.2)).symm

theorem cl24_eps_zero (P : HypPair Q) : cl24_eps P 0 = 1 :=
  Subtype.ext (eichler_zero_right Q P.e)

@[expose] noncomputable def cl24_epsHom (P : HypPair Q) :
    Multiplicative P.perp →* elementaryGroup Q where
  toFun w := cl24_eps P (Multiplicative.toAdd w)
  map_one' := cl24_eps_zero P
  map_mul' v w := cl24_eps_add P (Multiplicative.toAdd v) (Multiplicative.toAdd w)

theorem cl24_eps_neg (P : HypPair Q) (w : P.perp) : cl24_eps P (-w) = (cl24_eps P w)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← cl24_eps_add, neg_add_cancel, cl24_eps_zero])

theorem cl24_mem_rootGroup_iff (P : HypPair Q) {g : V ≃ₗ[K] V} :
    g ∈ rootGroup Q P.e ↔ ∃ w : P.perp, eichler Q P.e w = g := by
  constructor
  · intro hg
    obtain ⟨w, hw, rfl⟩ := mem_rootGroup.1 hg
    have hw' : polar Q w P.e = 0 := by rw [polar_comm, hw]
    have hw_eq : w = P.proj w + polar Q w P.f • P.e := by
      have h := P.eq_add_proj w
      rw [hw', zero_smul, add_zero] at h
      rw [add_comm]
      exact h
    refine ⟨⟨P.proj w, P.proj_mem_perp w⟩, ?_⟩
    calc eichler Q P.e (P.proj w)
        = eichler Q P.e (P.proj w + polar Q w P.f • P.e) :=
          (eichler_add_smul_self P.Q_e _ _).symm
      _ = eichler Q P.e w := by rw [← hw_eq]
  · rintro ⟨w, rfl⟩
    exact eichler_mem_rootGroup (cl24_polar_e_of_mem_perp P w.2)

end CFSG.OddStandard.SmallF3.HypA2Leaves
