module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsInvolution
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapPair

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus

open QuadraticMap Module

namespace KGD

open CFSG.RankThree.OrthogonalInvolutions CFSG.SeitzReduction.OmegaPilot

theorem exists_totallySingular_le_fixSpace {k W : Type*} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] {Q : QuadraticForm k W}
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 8 ≤ finrank k W) {t : W ≃ₗ[k] W}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) :
    ∃ T : Submodule k W, 2 ≤ finrank k T ∧ (∀ x ∈ T, Q x = 0) ∧ ∀ x ∈ T, t x = x := by
  have hC : ∀ x ∈ commSpace t, ∀ y ∈ commSpace t, polar Q x y = 0 :=
    fun x hx y hy => polar_commSpace_eq_zero ht htt hx hy
  obtain ⟨a, haC, hCa⟩ := exists_le_singularPart_sup (commSpace t) hC
  by_cases h : finrank k (singularPart Q (commSpace t) hC) ≤ 2
  · obtain ⟨T, hW₀T, hTdim, hTsing, hTa⟩ := exists_totallySingular_extension (p := 2) hQ
      (a := a) (r := 2) (by omega) (2 - finrank k (singularPart Q (commSpace t) hC))
      (singularPart Q (commSpace t) hC) (by omega) (fun x hx => (mem_singularPart.mp hx).2)
      (fun x hx => hC x (mem_singularPart.mp hx).1 a haC)
    refine ⟨T, hTdim.ge, hTsing, fun x hx => mem_fixSpace.mp ?_⟩
    rw [fixSpace_eq_orthogonal_commSpace hQ ht htt, LinearMap.BilinForm.mem_orthogonal_iff]
    intro c hc
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hCa hc)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
    change polarBilin Q (y + s • a) x = 0
    rw [polarBilin_apply_apply, polar_add_left, polar_smul_left,
      polar_eq_zero_of_totallySingular hTsing (hW₀T hy) hx, polar_comm, hTa x hx, smul_zero,
      add_zero]
  · exact ⟨singularPart Q (commSpace t) hC, by omega, fun x hx => (mem_singularPart.mp hx).2,
      fun x hx => mem_fixSpace.mp (commSpace_le_fixSpace htt (mem_singularPart.mp hx).1)⟩

theorem exists_pair_of_two_le_finrank {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    {T : Submodule k W} (hT : 2 ≤ finrank k T) :
    ∃ u ∈ T, ∃ w ∈ T, LinearIndependent k ![u, w] := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hT
  refine ⟨f 0, (f 0).2, f 1, (f 1).2, ?_⟩
  convert hf.map' T.subtype T.ker_subtype using 1
  funext i
  fin_cases i <;> rfl

end KGD

theorem exists_singular_plane_of_involution {k W : Type*} [Field k] [Finite k] [CharP k 2]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] {Q : QuadraticForm k W}
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 8 ≤ finrank k W) {t : W ≃ₗ[k] W}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) :
    ∃ u w : W, LinearIndependent k ![u, w] ∧ Q u = 0 ∧ Q w = 0 ∧ polar Q u w = 0 ∧
      t u = u ∧ t w = w := by
  obtain ⟨T, hT2, hTsing, hTfix⟩ := KGD.exists_totallySingular_le_fixSpace hQ hdim ht htt
  obtain ⟨u, hu, w, hw, huw⟩ := KGD.exists_pair_of_two_le_finrank hT2
  exact ⟨u, w, huw, hTsing u hu, hTsing w hw,
    CFSG.SeitzReduction.OmegaPilot.polar_eq_zero_of_totallySingular hTsing hu hw, hTfix u hu,
    hTfix w hw⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus
