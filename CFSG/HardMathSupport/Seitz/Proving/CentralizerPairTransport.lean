module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.PlaneFromCentralizers

namespace CFSG.HardMathSupport.Seitz.Proving

public section

open CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

variable {G H : Type*} [Group G] [Group H]

theorem map_centralizer_singleton (φ : G ≃* H) (z : G) :
    (Subgroup.centralizer {z}).map φ.toMonoidHom = Subgroup.centralizer {φ z} := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := hg z (Set.mem_singleton z)
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]
  · intro hx
    refine ⟨φ.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff] at hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := hx (φ h) (Set.mem_singleton _)
    apply φ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact this

end

end CFSG.HardMathSupport.Seitz.Proving
