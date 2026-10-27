module

public import CFSG.ClassicalInvolution.ModelFacts.MF15Conj
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenGenB

public noncomputable section

open QuadraticMap Matrix
open scoped MatrixGroups

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.SeitzGeneration

variable {K V : Type} [Field K] [CharP K 2] [Finite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_isometry_conj_charTwo (hQ : (polarBilin Q).Nondegenerate)
    (F F' : Frame Q) :
    ∃ g : V ≃ₗ[K] V, ∃ hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      F.map hg = F' ∧ (∀ X, g (F.incl X) = F'.incl X) ∧
      ∀ A : SL(2, K), F'.La A = g * F.La A * g⁻¹ := by
  obtain ⟨a, ha, hae, haf⟩ :=
    CFSG.Timmesfeld.ClassicalOrders.exists_mem_orthogonalGroup_apply_pair
      hQ CharTwo.two_eq_zero F.P F'.P
  let U := F'.P.perp
  let S := (F.map ha).P'
  have hSe : S.e ∈ U := by
    rw [HypPair.mem_perp]
    change polar Q F'.P.e (a F.P'.e) = 0 ∧ polar Q F'.P.f (a F.P'.e) = 0
    rw [← hae, ← haf, polar_map_of_mem ha, polar_map_of_mem ha]
    exact ⟨F.orth.ee, F.orth.fe⟩
  have hSf : S.f ∈ U := by
    rw [HypPair.mem_perp]
    change polar Q F'.P.e (a F.P'.f) = 0 ∧ polar Q F'.P.f (a F.P'.f) = 0
    rw [← hae, ← haf, polar_map_of_mem ha, polar_map_of_mem ha]
    exact ⟨F.orth.ef, F.orth.ff⟩
  have hTe : F'.P'.e ∈ U := HypPair.mem_perp.mpr ⟨F'.orth.ee, F'.orth.fe⟩
  have hTf : F'.P'.f ∈ U := HypPair.mem_perp.mpr ⟨F'.orth.ef, F'.orth.ff⟩
  have hU : PolarNondegOn Q U := HypPair.polarNondegOn_perp hQ F'.P
  let R : HypPair (Q.restrict U) :=
    { e := ⟨S.e, hSe⟩
      f := ⟨S.f, hSf⟩
      Q_e := S.Q_e
      Q_f := S.Q_f
      polar_ef := by rw [polar_restrict]; exact S.polar_ef }
  let R' : HypPair (Q.restrict U) :=
    { e := ⟨F'.P'.e, hTe⟩
      f := ⟨F'.P'.f, hTf⟩
      Q_e := F'.P'.Q_e
      Q_f := F'.P'.Q_f
      polar_ef := by rw [polar_restrict]; exact F'.P'.polar_ef }
  obtain ⟨b, hb, hbe, hbf⟩ :=
    CFSG.Timmesfeld.ClassicalOrders.exists_mem_orthogonalGroup_apply_pair
      (nondegenerate_polarBilin_restrict hU) CharTwo.two_eq_zero R R'
  let c := OrthNS.extU hU b
  have hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.StandardType.OmNsRootGen.extU_mem_orthogonalGroup hU hb
  have hep : F'.P.e ∈ OrthBlk.perp Q U := by
    rw [OrthBlk.mem_perp]
    intro u hu
    rw [polar_comm]
    exact (HypPair.mem_perp.mp hu).1
  have hfp : F'.P.f ∈ OrthBlk.perp Q U := by
    rw [OrthBlk.mem_perp]
    intro u hu
    rw [polar_comm]
    exact (HypPair.mem_perp.mp hu).2
  have h1 : (c * a) F.e₁ = F'.e₁ := by
    rw [LinearEquiv.mul_apply, hae]
    exact OrthNS.extU_apply_perp hU b hep
  have h2 : (c * a) F.f₁ = F'.f₁ := by
    rw [LinearEquiv.mul_apply, haf]
    exact OrthNS.extU_apply_perp hU b hfp
  have h3 : (c * a) F.e₂ = F'.e₂ := by
    change OrthNS.extU hU b S.e = F'.P'.e
    rw [OrthNS.extU_apply_mem hU b hSe]
    exact congrArg Subtype.val hbe
  have h4 : (c * a) F.f₂ = F'.f₂ := by
    change OrthNS.extU hU b S.f = F'.P'.f
    rw [OrthNS.extU_apply_mem hU b hSf]
    exact congrArg Subtype.val hbf
  have hca : c * a ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem hc ha
  have hmap : F.map hca = F' :=
    CFSG.ClassicalInvolution.ModelFacts.MF15.frame_map_eq_of_apply F F' hca h1 h2 h3 h4
  refine ⟨c * a, hca, hmap, ?_, ?_⟩
  · intro X
    simp only [Frame.incl_apply, map_add, map_smul, h1, h2, h3, h4]
  · intro A
    rw [← hmap, Frame.map_La]

end CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

end
