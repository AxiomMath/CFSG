module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Frame
public import CFSG.HardMathSupport.Dickson.Bal207.SU38D4
import CFSG.HardMathSupport.Dickson.Bal207.D4Eight
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open QuadraticMap CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.Bal207.Uni
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem su38FrameD4_of_torus (hTor : OrthFix.OrthSU38ToralInput)
    (hFix : OrthFix.OrthUniAutFixInput) (hGA : GriessAllModelsStatement) :
    SU38FrameD4 NonSemilinD4Eight := by
  refine su38FrameD4_of_inner fun Y _ _ _ K B A ctx hK hN _ a haA ha1 ha s hs J hJ hsu hBJ => ?_
  obtain ⟨F₀, _, _, hF₀, ⟨e₀⟩⟩ := exists_d4Eight_model hK
  haveI : CharP F₀ 2 := by
    haveI := Fintype.ofFinite F₀
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := 3) (by rw [Fintype.card_eq_nat_card, hF₀]; norm_num)
  have hd : 0 < 2 * 4 := by norm_num
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 F₀ (by norm_num)
  let ψ := coordinatePlusWitnessEquiv F₀ e₀
  let e := ψ.trans (coordBridge (coordinateQuadPlus 4 F₀) hd)
  have hKq : CFSG.Open.IsQuasisimple ↥K := ctx.comp.2.2
  have hZ := d4Eight_coprime_center hGA hKq hK
  have hβ3 : uniAut e ⟨a, ha⟩ ^ 3 = 1 := by
    have h3 : (⟨a, ha⟩ : ↥(Subgroup.normalizer (K : Set Y))) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact ctx.scp.2.1.2 a (ctx.le haA))
    rw [← map_pow, h3, map_one]
  have hβ1 : uniAut e ⟨a, ha⟩ ≠ 1 := fun h1 =>
    not_mem_centralizer_of_inf_eq_bot ctx.disj haA ha1
      (mem_centralizer_of_uniAut_eq_one e hKq.1 ha h1)
  have hat : uniAut e ⟨a, ha⟩ = MulAut.conj (e s) := by
    show MulAut.congr e (actHom K ⟨a, ha⟩) = _
    rw [← hs, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  have hS := KCOrthogonalD4.conj_injective_projOrthDerived (coordinateQuadPlus 4 F₀) hQ hT
  have ht3 : e s ^ 3 = 1 := hS (by rw [map_pow, map_one, ← hat]; exact hβ3)
  have ht1 : e s ≠ 1 := fun h => hβ1 (by rw [hat, h, map_one])
  haveI : Nontrivial (Fin (2 * 4) → F₀) := by
    obtain ⟨U, hU3, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := F₀)
      (lt_of_lt_of_le (by norm_num : 0 < 3) (hU3 ▸ Submodule.finrank_le U))
  obtain ⟨x, hxs, hx3⟩ := OrthFix.exists_lift_orderOf_three hQ (orderOf_eq_prime ht3 ht1)
  have hax : uniAut e ⟨a, ha⟩ = MulAut.conj (piOrth (coordinateQuadPlus 4 F₀) x) := by
    rw [hat, hxs]
  have hM : StatedClassicalModel (ProjOrthDerived (coordinateQuadPlus 4 F₀)) .POmegaPlus 4 2 3 :=
    ⟨⟨Nat.prime_two, by norm_num, show 4 ≤ 4 from le_rfl⟩, F₀, inferInstance, inferInstance,
      by rw [hF₀]; norm_num, ⟨e.symm.trans e₀⟩⟩
  have hlay : PerfectInLayer (MulAut.conj (piOrth (coordinateQuadPlus 4 F₀) x)) :=
    LieSemisimple.perfectInLayer_conj_omega (Or.inr (Or.inl rfl)) hM Nat.prime_three
      (by norm_num) (by norm_num) _ (by rw [hxs, ht3])
  obtain ⟨hcomp, -, hΦ, hm, hJx⟩ :=
    OrthFix.su38_image_eq_componentImage (Or.inr hF₀) hQ hKq hZ e ha x hx3 hax hlay hJ hsu
  have hE : ∀ b : ↥B, MulAut.congr (coordBridge (coordinateQuadPlus 4 F₀) hd).symm
      (uniAut e ⟨b, ctx.norm b.2⟩) ∈ matrixProjectiveImage (coordinateQuadPlus 4 F₀) := by
    intro b
    have h : MulAut.congr (coordBridge (coordinateQuadPlus 4 F₀) hd).symm
        (uniAut e ⟨b, ctx.norm b.2⟩) = MulAut.congr ψ (actHom K ⟨b, ctx.norm b.2⟩) :=
      MulEquiv.ext fun g => by simp [e, uniAut_apply, MulAut.congr_apply]
    rw [h]
    exact mulAut_congr_mem_image_of_noTrialityOn hN (fun b hb => ctx.scp.2.1.2 b hb) hF₀ ψ
      (mem_autImage.2 ⟨b, ctx.norm b.2, b.2, rfl⟩)
  exact Or.inr (hTor ctx.scp ctx.norm hZ hF₀ hd hQ hT
    (fun g => (CFSG.RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _
      hQ hT (coordinate_plus_point_action_properties 4 F₀ (by norm_num)) g).mp)
    e hE hcomp.2.2 (hJ.1.trans inf_le_left) hBJ x hx3 hΦ hm hJx
    (hFix ctx.scp ctx.norm hd hQ hT e (ctx.le haA) hax))

end CFSG.HardMathSupport.Dickson.Bal207

end
