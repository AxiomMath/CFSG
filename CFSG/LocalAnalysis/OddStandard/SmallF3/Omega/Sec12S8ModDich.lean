module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDCoord
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDCond
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDFin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDOm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDConclS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDConclOm

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82S8Dich_of : Asc82S8Dich := by
  intro G _ V X V1 V2 Z hV hsup hinf hA5 h1 h2 hZ hZiso
  obtain ⟨K, σ, hK⟩ := s8d_coord hV hsup hinf hA5 h1 h2
  let Z' : Subgroup S8A := Z.map K.s8dKap.toMonoidHom
  have hD : ∀ a : ↥(alternatingGroup (Fin 5)), s8dDiag a ∈ Z' := s8d_kap_autIn K σ hK hZ
  obtain ⟨θ0⟩ := hZiso
  let ιZ : ↥Z ≃* ↥Z' := Z.equivMapOfInjective K.s8dKap.toMonoidHom K.s8dKap.injective
  have hι : ∀ z' : ↥Z', K.s8dKap ((ιZ.symm z' : ↥Z) : MulAut ↥V) = (z' : S8A) := by
    intro z'
    have h := Subgroup.coe_equivMapOfInjective_apply Z K.s8dKap.toMonoidHom
      K.s8dKap.injective (ιZ.symm z')
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  obtain ⟨θ', hθ'⟩ := s8d_diag_param hD (θ0.symm.trans ιZ)
  obtain ⟨hc, h5, hne1, hnec0, hb⟩ := s8d_cond θ' hθ' rfl
  rcases s8d_fin _ hc h5 hne1 hnec0 hb with ⟨T, hT⟩ | hOm
  · left
    have hS := s8d_shapeS θ' hθ' T hT
    refine s8d_concl_S K T (θ'.trans ιZ.symm) fun x => ?_
    rw [MulEquiv.trans_apply, hι, hS x]
  · right
    obtain ⟨ψ, hψ⟩ := s8d_shapeOm θ' hθ' hOm
    refine s8d_concl_Om K (ψ.trans ιZ.symm) fun A B p => ?_
    rw [MulEquiv.trans_apply, hι, hψ]

end CFSG.OddStandard.SmallF3.Omega
