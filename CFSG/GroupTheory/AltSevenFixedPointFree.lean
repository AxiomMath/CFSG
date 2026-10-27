module

public import CFSG.Quasithin.Background.Module
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Facts
import CFSG.Quasithin.Background.HA7
import CFSG.GroupTheory.AltSevenModule.Faithful

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (fixV commV)
open CFSG.CGT.PushingUpLit.CGT6

private theorem exists_not_commute_rp {W : Type} [CommGroup W]
    {K : Subgroup (MulAut W)} (φ : ↥K ≃* alternatingGroup (Fin 7)) :
    ∃ a b : ↥K, a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact CFSG.Quasithin.H.A7.not_comm_A7 fun σ τ => by
    simpa using congrArg φ (h (φ.symm σ) (φ.symm τ))

private theorem eq_one_of_fix_threeCycle_a7f {U : Type} [CommGroup U]
    (hcard : Nat.card U = 16) (ρ : ↥(alternatingGroup (Fin 7)) →* MulAut U)
    (hinj : Function.Injective ρ) {g : ↥(alternatingGroup (Fin 7))}
    (hg : ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).IsThreeCycle) {u : U}
    (hu : ρ g u = u) : u = 1 := by
  obtain ⟨c, hc⟩ := alternatingGroup.isThreeCycle_isConj (α := Fin 7) (by simp)
    (σ := ⟨CFSG.RankThree.PartTwo.KFacts.KP2.cOne,
      CFSG.LocalAnalysis.RankThreeTheoremC.a7m_cOne_mem⟩) (τ := g)
    (by simpa using CFSG.LocalAnalysis.RankThreeTheoremC.a7m_isThreeCycle_cOne) hg
  have hconj : (↑c : ↥(alternatingGroup (Fin 7))) *
      ⟨CFSG.RankThree.PartTwo.KFacts.KP2.cOne,
        CFSG.LocalAnalysis.RankThreeTheoremC.a7m_cOne_mem⟩ * (↑c)⁻¹ = g := by
    have h1 := congrArg (fun z : ↥(alternatingGroup (Fin 7)) => z * (↑c)⁻¹) hc.eq
    simpa [mul_assoc] using h1
  have hfixc : ρ (⟨CFSG.RankThree.PartTwo.KFacts.KP2.cOne,
        CFSG.LocalAnalysis.RankThreeTheoremC.a7m_cOne_mem⟩) ((ρ (↑c))⁻¹ u) =
      (ρ (↑c))⁻¹ u := by
    apply (ρ (↑c)).injective
    have h1 : ρ ((↑c : ↥(alternatingGroup (Fin 7))) *
        ⟨CFSG.RankThree.PartTwo.KFacts.KP2.cOne,
          CFSG.LocalAnalysis.RankThreeTheoremC.a7m_cOne_mem⟩ * (↑c)⁻¹) u = u := by
      rw [hconj]
      exact hu
    simp only [map_mul, map_inv, MulAut.mul_apply] at h1
    rw [h1, MulAut.apply_inv_self]
  have hzero : (ρ (↑c))⁻¹ u = 1 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.a7m_eq_one_of_fix_cOne hcard ρ hinj hfixc
  have h1 := congrArg (ρ (↑c)) hzero
  rw [MulAut.apply_inv_self, map_one] at h1
  exact h1

theorem fixV_zpowers_inf_commV_eq_bot {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    (φ : ↥K ≃* alternatingGroup (Fin 7)) (hK : Nat.card (commV K) = 16) {x : MulAut W}
    (hx : x ∈ K) (h3 : ((φ ⟨x, hx⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).IsThreeCycle) :
    fixV (Subgroup.zpowers x) ⊓ commV K = ⊥ := by
  classical
  have : IsSimpleGroup ↥K := φ.isSimpleGroup
  let r : ↥K →* MulAut ↥(commV K) :=
    (restrictW (commV K)).comp (Subgroup.inclusion (AltSevenModule.le_stabW_commV K))
  have hr : Function.Injective r :=
    AltSevenModule.injective_restrictW_commV (exists_not_commute_rp φ)
  let ρ' : ↥(alternatingGroup (Fin 7)) →* MulAut ↥(commV K) :=
    r.comp φ.symm.toMonoidHom
  have hinj : Function.Injective ρ' := hr.comp φ.symm.injective
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have hu1 : u ∈ fixV (Subgroup.zpowers x) := (Subgroup.mem_inf.mp hu).1
  have hu2 : u ∈ commV K := (Subgroup.mem_inf.mp hu).2
  have hxu : x u = u := CFSG.Quasithin.mem_fixV.mp hu1 x (Subgroup.mem_zpowers x)
  let g : ↥(alternatingGroup (Fin 7)) := φ ⟨x, hx⟩
  have hg3 : ((g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)).IsThreeCycle := h3
  have hfixg : ρ' g ⟨u, hu2⟩ = ⟨u, hu2⟩ := by
    apply Subtype.ext
    have h1 : ((ρ' g ⟨u, hu2⟩ : ↥(commV K)) : W) = x u := by
      have hg : φ.symm g = ⟨x, hx⟩ := by simp [g]
      simpa [ρ', r, MonoidHom.comp_apply, hg] using
        coe_restrictW (commV K) (Subgroup.inclusion (AltSevenModule.le_stabW_commV K) ⟨x, hx⟩)
          ⟨u, hu2⟩
    rw [h1, hxu]
  have hzero : (⟨u, hu2⟩ : ↥(commV K)) = 1 :=
    eq_one_of_fix_threeCycle_a7f hK ρ' hinj hg3 hfixg
  exact Subtype.ext_iff.mp hzero

end CFSG.GroupTheory
