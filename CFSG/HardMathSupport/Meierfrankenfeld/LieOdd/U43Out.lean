module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43AutBase

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

theorem e_psi (e : (Nrm : Subgroup Gp) ≃* MulAut X₀)
    (he : ∀ (a : (Nrm : Subgroup Gp)) (x : X₀), psi (e a x) = (a : Gp) * psi x * (a : Gp)⁻¹)
    (g : X₀) (hg : psi g ∈ Nrm) : e ⟨psi g, hg⟩ = MulAut.conj g := by
  ext x
  apply psi_injective
  rw [he]
  simp [map_mul, map_inv]

theorem mem_range_conj_iff (e : (Nrm : Subgroup Gp) ≃* MulAut X₀)
    (he : ∀ (a : (Nrm : Subgroup Gp)) (x : X₀), psi (e a x) = (a : Gp) * psi x * (a : Gp)⁻¹)
    (b : MulAut X₀) :
    b ∈ (MulAut.conj : X₀ →* MulAut X₀).range ↔ ((e.symm b : (Nrm : Subgroup Gp)) : Gp) ∈ Nsub := by
  constructor
  · rintro ⟨g, rfl⟩
    have hg : psi g ∈ Nrm := Nsub_le_Nrm ⟨g, rfl⟩
    have := e_psi e he g hg
    have h2 : e.symm (MulAut.conj g) = ⟨psi g, hg⟩ := by
      rw [← this]; exact e.symm_apply_apply _
    rw [h2]
    exact ⟨g, rfl⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    have hmem : psi g ∈ Nrm := Nsub_le_Nrm ⟨g, rfl⟩
    have h1 := e_psi e he g hmem
    have : e.symm b = ⟨psi g, hmem⟩ := Subtype.ext hg.symm
    rw [← h1, ← this]
    exact e.apply_symm_apply b

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
