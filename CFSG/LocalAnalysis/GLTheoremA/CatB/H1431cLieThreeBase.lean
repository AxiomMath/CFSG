module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutBase
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem lieS3_exists_field {X : Type} [Group X] (h : catalogIs X isL2three6) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 729 ∧
      Nonempty (X ≃* StatedProj (StatedSL 2 F)) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | A r q =>
    rcases r with _ | _ | r
    · exact hP.elim
    · have hm : CFSG.Models.LieModel X .PSL 2 q.p q.exponent := CFSG.Models.lieModel_A 1 q hv e
      obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hm.2.resolve_right (fun h => absurd h.1 (by norm_num))
      refine ⟨K, inferInstance, inferInstance, ?_, ⟨eK⟩⟩
      rw [hK, ← TauCeti.PrimePower.card_def]
      exact hP
    · exact hP.elim
  | _ => exact hP.elim

theorem lieS3_isTypeL2 {S : Type} [Group S] {J : Subgroup S}
    (h : catalogIs (PSimple 3 J) isL2three6) : IsTypeL2 729 (barOf 3 J) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := lieS3_exists_field h
  exact ⟨F, hF, hFin, hcard, ⟨e⟩⟩

theorem lieS3_false_of_noL2Layer {S : Type} [Group S] {α : MulAut S} (h : NoL2Layer α)
    (hc : CompOfType S α isL2three6) : False := by
  obtain ⟨J, hJ, hT⟩ := hc
  exact h J hJ 729 (by norm_num) (lieS3_isTypeL2 hT)

theorem lieS3_noL2Layer_of_famOK {S P : Type} [Group S] [Finite S] [Group P] (e : S ≃* P)
    (hP : FamOK P) {α : MulAut S} (hα3 : α ^ 3 = 1) (hα : α ∉ inner S) : NoL2Layer α := by
  haveI : Finite P := Finite.of_equiv S e.toEquiv
  refine noL2Layer_congr e ?_
  have h3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  obtain ⟨γ, f, hγ, hf⟩ := hP (MulAut.congr e α) h3 fun hin =>
    hα ((congr_mem_inner_iff_of_equiv e α).mp hin)
  rw [hγ]
  exact noL2Layer_conj γ hf

theorem lieS3_card_of_catalog {F₀ : Type} [Field F₀] [Finite F₀] (h4 : 4 ≤ Nat.card F₀)
    (h : catalogIs (StatedProj (StatedSL 2 F₀)) isL2three6) : Nat.card F₀ = 729 := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := lieS3_exists_field h
  obtain ⟨-, hZ⟩ := CFSG.HardMathSupport.Solomon.Coordinator.l2fld_isQuasisimple_psl2 h4
  let e0 : (StatedProj (StatedSL 2 F₀) ⧸ Subgroup.center (StatedProj (StatedSL 2 F₀))) ≃*
      StatedProj (StatedSL 2 F₀) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hs : IsTypeL2 (Nat.card F₀) (StatedProj (StatedSL 2 F₀)) :=
    ⟨F₀, inferInstance, inferInstance, rfl, ⟨e0⟩⟩
  have ht : IsTypeL2 729 (StatedProj (StatedSL 2 F₀)) :=
    ⟨F, hF, hFin, hcard, ⟨e0.trans e⟩⟩
  rcases CFSG.HardMathSupport.Solomon.Proving.l2OrderUnique_holds _ _ _ hs ht with
    h1 | ⟨-, h2⟩ | ⟨-, h2⟩
  · exact h1
  · omega
  · omega

theorem lieS3_typeLayer_psl2 {K : Type} [Field K] [Finite K]
    {β : MulAut (StatedProj (StatedSL 2 K))} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    TypeLayer isL2three6 β (Nat.card K = 3 ^ 18) := by
  have hfx : Lemma510Ns.fixSub β = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β :=
    Subgroup.ext fun _ => Iff.rfl
  rcases CFSG.HardMathSupport.Solomon.Coordinator.l2Aut3Classification_holds K β hβ3 with
    h1 | hsol | ⟨σ, φ, γ, hφ, hβ⟩
  · exact absurd h1 hβ1
  · exact typeLayer_of_solvable_fixed (by rwa [← hfx])
  · obtain ⟨F₀, _, _, hcard, ⟨ψ0⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds K β hβ3 hβ1 σ φ γ hφ hβ
    have ψ1 : ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) ≃*
        StatedProj (StatedSL 2 F₀) :=
      (MulEquiv.subgroupCongr hfx.symm).trans ψ0
    by_cases h4 : 4 ≤ Nat.card F₀
    · obtain ⟨hQ₀, hZ₀⟩ := CFSG.HardMathSupport.Solomon.Coordinator.l2fld_isQuasisimple_psl2 h4
      have hsimple : IsSimpleGroup (StatedProj (StatedSL 2 F₀)) := by
        haveI := hQ₀.2
        exact ((QuotientGroup.quotientMulEquivOfEq hZ₀).trans
          QuotientGroup.quotientBot).symm.isSimpleGroup
      haveI := hsimple
      refine typeLayer_of_fixed_equiv β ψ1 hsimple (exists_noncomm_of_center_bot hZ₀) fun hT => ?_
      rw [hcard, lieS3_card_of_catalog h4 hT]
      norm_num
    · haveI : Group.IsSolvable (StatedProj (StatedSL 2 F₀)) :=
        CFSG.HardMathSupport.Solomon.Coordinator.l2fld_isSolvable_psl2_of_card_le_three
          (F := F₀) (by omega)
      exact typeLayer_of_solvable_fixed
        (Group.isSolvable_of_isSolvable_injective (f := ψ1.toMonoidHom) ψ1.injective)

theorem lieS3_A1 {S K : Type} [Group S] [Finite S] [Field K] [Finite K]
    (eK : S ≃* StatedProj (StatedSL 2 K)) {α : MulAut S} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hc : CompOfType S α isL2three6) : Nat.card K = 3 ^ 18 := by
  haveI : Finite (StatedProj (StatedSL 2 K)) := Finite.of_equiv S eK.toEquiv
  have hβ3 : MulAut.congr eK α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβ1 : MulAut.congr eK α ≠ 1 := fun h =>
    hα1 ((MulAut.congr eK).injective (h.trans (map_one _).symm))
  obtain ⟨J, hJ, hT⟩ := hc
  exact typeLayer_congr eK (lieS3_typeLayer_psl2 hβ3 hβ1) J hJ hT

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
