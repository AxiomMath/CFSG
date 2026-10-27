module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.MW3Fixed
public import CFSG.Monster.Visible.Faithful

public section

namespace CFSG.EvenSporadicStandard.TwoB.MW3

open CFSG.Monster CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.VisCert
  CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel CFSG.Monster.Spin

noncomputable def psiVis : VisMod ≃* Multiplicative L2 :=
  visModEquivQuot.trans phi

theorem psiVis_mk (t : Q) :
    psiVis (QuotientGroup.mk (rhoN t)) = phi (QuotientGroup.mk t) :=
  congrArg phi (visModEquivQuot_mk t)

theorem psiVis_conjVis (g : Gvis) (v : VisMod) :
    Multiplicative.toAdd (psiVis (conjVis g v)) =
      ((opQHom (piVis g) : GLV) : L2 →ₗ[ZMod 2] L2) (Multiplicative.toAdd (psiVis v)) := by
  obtain ⟨p, rfl⟩ := eq_thetaEquiv g
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  obtain ⟨t, rfl⟩ := rhoN_surjective x
  have h2 : opQHom (piVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩) = modTwoUnit p.1.2 :=
    (congrArg opQHom (piVis_thetaEquiv p)).trans (opQHom_op_mk _)
  have h3 : ((opQHom (piVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩) : GLV) :
      L2 →ₗ[ZMod 2] L2) = modTwoEnd p.1.2 :=
    congrArg (fun u : GLV => (u : L2 →ₗ[ZMod 2] L2)) h2
  have h4 : Multiplicative.toAdd (psiVis (QuotientGroup.mk (rhoN t))) =
      Multiplicative.toAdd (phi (QuotientGroup.mk t)) :=
    congrArg Multiplicative.toAdd (psiVis_mk t)
  have h5 : Multiplicative.toAdd (psiVis (conjVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩
        (QuotientGroup.mk (rhoN t)))) = Multiplicative.toAdd (phi (QuotientGroup.mk (conjQ p t))) :=
    (congrArg (fun w => Multiplicative.toAdd (psiVis w)) (conjVis_thetaEquiv_mk p t)).trans
      (congrArg Multiplicative.toAdd (psiVis_mk _))
  exact h5.trans ((phi_conjQ p t).trans
    (congrArg₂ (fun (f : L2 →ₗ[ZMod 2] L2) (w : L2) => f w) h3.symm h4.symm))

theorem mem_zRho_of_fixed
    (S : Subgroup Gvis) (hcard : Nat.card (S.map piVis) = 2 ^ 21 * 3 ^ 5 * 5 ^ 2 * 7)
    {q : rhoQvis}
    (hq : ∀ s ∈ S, conjVis s (QuotientGroup.mk q) = QuotientGroup.mk q) : q ∈ zRho := by
  set P : Subgroup GLV := (S.map piVis).map opQHom with hP
  have hPle : P ≤ Hvis := by
    rw [← range_opQHom]
    exact (Subgroup.map_le_range _ _)
  have hPcard : Nat.card P = 2 ^ 21 * 3 ^ 5 * 5 ^ 2 * 7 := by
    rw [hP, Subgroup.card_map_of_injective opQHom_injective, hcard]
  have hfix : ∀ g ∈ P, (g : L2 →ₗ[ZMod 2] L2) (Multiplicative.toAdd (psiVis (QuotientGroup.mk q))) =
      Multiplicative.toAdd (psiVis (QuotientGroup.mk q)) := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← psiVis_conjVis, hq s hs]
  have h0 := eq_zero_of_fixed P hPle hPcard hfix
  have h1 : psiVis (QuotientGroup.mk q) = 1 := by
    have : Multiplicative.toAdd (psiVis (QuotientGroup.mk q)) = 0 := h0
    exact Multiplicative.toAdd.injective this
  have h2 : (QuotientGroup.mk q : VisMod) = 1 := psiVis.injective (h1.trans (map_one psiVis).symm)
  exact (QuotientGroup.eq_one_iff q).1 h2

end CFSG.EvenSporadicStandard.TwoB.MW3
