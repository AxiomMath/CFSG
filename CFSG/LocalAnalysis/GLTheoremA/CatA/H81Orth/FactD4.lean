module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.ChoiceModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.AutFamilies
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81ChoiceTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
import CFSG.Adapters.TauCetiLieModels
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthOmega

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81Orth

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.Yardstones.Md0ec50421ce4

theorem h81Choice_plus_four_model {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (Q : TauCeti.PrimePower) (hQ2 : Q.p ≠ 2) (hFcard : Nat.card F = Q.p ^ Q.exponent)
    (hdiv : p ∣ Q.card ^ 2 - 1) [Finite (ProjOrthDerived (quadPlus 4 F))]
    {P : Subgroup (ProjOrthDerived (quadPlus 4 F))} (hP : IsElemAbelian p P)
    (hPc : Nat.card P = p ^ 4) : H81Choice p P (IsOmegaType p Q.p) := by
  classical
  obtain ⟨hK, hK3, hpK, hFQ⟩ := field_facts hp hp2 hQ2 hFcard hdiv
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  have hpQ := ne_char_of_dvd_sq_sub_one hdiv
  have hQnd : (polarBilin (quadPlus 4 F)).Nondegenerate := nondegenerate_polarBilin_quadPlus 4 F
  have hT : ∃ T : Submodule F (Fin 4 ⊕ Fin 4 → F), finrank F T = 3 ∧
      ∀ x ∈ T, quadPlus 4 F x = 0 :=
    CFSG.ComponentClassification.RankTwoClassical.exists_totallySingular_quadPlus (by norm_num) F
  have hV : finrank F (Fin 4 ⊕ Fin 4 → F) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]; simp
  have hadm : StatedLieAdmissible .POmegaPlus 4 Q.p Q.exponent :=
    ⟨Q.prime_p, Q.exponent_pos, le_rfl⟩
  refine h81Choice_of_lift hQnd hT hK hK3 hp hp2 hpK hP (fun Pt hPt hPtc => ?_)
    (fun yy hy hR hW hpJ => ?_) (fun yy hy hR hW α hα hαJ => ?_)
  ·
    haveI := hPt.1
    letI : CommGroup ↥Pt :=
      { (inferInstance : Group ↥Pt) with mul_comm := fun a b => mul_comm' a b }
    haveI : Finite (Fin 4 ⊕ Fin 4 → F) := Module.finite_of_finite F
    haveI : Finite ((Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) :=
      Finite.of_injective (fun e : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] _ => (e : _ → _))
        fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    let ρ : Representation F ↥Pt (Fin 4 ⊕ Fin 4 → F) :=
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp
        ((orthDerived (quadPlus 4 F)).subtype.comp Pt.subtype)
    have hρinj : Function.Injective ρ := fun a b h => Subtype.ext (Subtype.ext
      (LinearEquiv.ext fun v => congrArg (fun f => f v) h))
    have hA : ∀ a : ↥Pt, a ^ p = 1 := fun a => Subtype.ext (hPt.2 a a.2)
    have hρQ : ∀ (a : ↥Pt) (v : Fin 4 ⊕ Fin 4 → F), quadPlus 4 F (ρ a v) = quadPlus 4 F v :=
      fun a v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup' _ (a : ↥(orthDerived (quadPlus 4 F))).2) v
    have hcard : Nat.card ↥Pt = p ^ 4 := by rw [hPtc, hPc]
    obtain ⟨yy, zz, h1, h2', h3, h4, h5, h6⟩ :=
      Wt.exists_planes_eight_four ρ hp hA hpK _ hQnd h2 hρQ hp2 hρinj hcard hV
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hd0, -⟩ :=
      Wt.exists_config_eight_four ρ hp hA hpK _ hQnd h2 hρQ hp2 hρinj hcard hV
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ :=
      conf_of_wt hQnd hpK Pt.subtype Pt.subtype_injective
        (fun a => by rw [← map_pow, hA a, map_one]) ρ (fun _ _ => rfl) (dW := 6) (by rw [hV])
        h1 h2' h3 (by rw [h4]) h5 h6 (by rw [hd0, finrank_bot, h4]; norm_num)
    rw [Subgroup.range_subtype] at c6 c8
    exact ⟨Pt.subtype yy, yy.2, Pt.subtype zz, zz.2, c1, c2, c3, c4.ge.trans' (by norm_num),
      Or.inr (by omega), c6, c7, c8⟩
  ·
    have hRne : othersSpace (yy : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] _).toLinearMap (X - 1) ≠ ⊥ :=
      fun h => by rw [h, finrank_bot] at hR; exact absurd hR (by norm_num)
    have hc : finrank F (fixedSpace (yy : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] _)) +
        finrank F (othersSpace (yy : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] _).toLinearMap (X - 1)) =
          finrank F (Fin 4 ⊕ Fin 4 → F) :=
      Submodule.finrank_add_eq_of_isCompl hy.fixed_others.1
    have hW6 : finrank F (fixedSpace (yy : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] _)) = 6 := by
      omega
    have he := fixedComponentImageEquiv hy hRne
    have hnd := hy.polarBilin_fixed_nondegenerate
    exact isOmegaType_of_mulEquiv_six (G := ProjOrthDerived (quadPlus 4 F)) (K := F)
      (W := ↥(fixedSpace (yy : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F))))
      hp _ Q hQ2 hpQ hFQ _ hnd hW6 he hpJ
  · exact exists_eq_conj_plus_four hadm hFcard hK hp hp2 hy hR hW α hα hαJ

theorem h81FactD4_holds : H81FactD4 := by
  intro p Q hp hp2 hQ2 hdiv H _ _ hcat P hPel hPcard
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  change d = .D 4 Q at hi
  subst hi
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 Q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hFcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 Q, hv⟩) = Q.p ^ Q.exponent :=
    CFSG.Models.card_fixedField_of (TauCeti.LieTypeIndex.characteristic_D 4 Q)
      (TauCeti.LieTypeIndex.fieldExponent_D 4 Q)
  let e : H ≃* ProjOrthDerived (quadPlus 4 ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 Q, hv⟩)) :=
    e₀.trans ((CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 Q
      hv).trans (CFSG.RankThree.PartOne.statedProjOrthEquiv (coe_quadPlus 4 _)))
  haveI : Finite (ProjOrthDerived (quadPlus 4 ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 Q, hv⟩))) :=
    Finite.of_equiv H e.toEquiv
  have hch := h81Choice_plus_four_model hp hp2 Q hQ2 hFcard hdiv
    ((CFSG.LocalAnalysis.GLTheoremA.T123C.isElemAbelian_map_iff (f := e.toMonoidHom) e.injective p
      P).2 hPel)
    (by rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hPcard])
  have h := CFSG.LocalAnalysis.GLTheoremA.H81.h81Choice_map_mulEquiv hp e.symm
    (fun J hJ => CFSG.LocalAnalysis.GLTheoremA.H81.isOmegaType_map_mulEquiv e.symm hJ) hch
  rwa [map_map_symm_mulEquiv] at h

end CFSG.LocalAnalysis.GLTheoremA.H81Orth
