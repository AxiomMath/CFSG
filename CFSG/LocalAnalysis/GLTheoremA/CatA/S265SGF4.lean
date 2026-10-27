module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGF4Comp
import CFSG.HardMathSupport.Dickson.Bal207.CompShape
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem SG.lieModel_of_tyF {X : Type} [Group X] (h : catalogIs X (tyF 3)) :
    IsSimpleGroup X ∧ ∃ (t : StatedLieTag) (m : ℕ), (t = .PSL ∨ t = .PSU) ∧
      CFSG.Blueprint.LieModel X t 3 2 m := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases i with _ | _ | ⟨⟨l, hv⟩⟩ | _ <;> try exact (hi : False).elim
  cases l
  case A r q =>
    obtain ⟨hr, hp, -⟩ : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card - 1 := hi
    have h1 := CFSG.Models.lieModel_A r q hv e
    rw [hr, hp] at h1
    exact ⟨(CFSG.LieType.Simplicity.fam_PSL_simplicity X _ _ _
      (h1.statedClassicalModel (by decide))).2, .PSL, _, .inl rfl,
      CFSG.Models.LieModel.toBlueprint (by decide) h1⟩
  case twistedA r q =>
    obtain ⟨hr, hp, -⟩ : r + 1 = 3 ∧ q.p = 2 ∧ 3 ∣ q.card + 1 := hi
    have h1 := CFSG.Models.lieModel_twistedA r q hv e
    have hc : TauCeti.ValidLieTypeIndex.characteristic
        ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩ = 2 :=
      (TauCeti.LieTypeIndex.characteristic_twistedA r q).trans hp
    rw [hc, hr] at h1
    exact ⟨(CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X _ _ _
      (h1.statedClassicalModel (by decide))).2, .PSU, _, .inr rfl,
      CFSG.Models.LieModel.toBlueprint (by decide) h1⟩
  all_goals exact (hi : False).elim

section Glue


theorem SG.exists_f4_conj_of_innLabelOf {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) {lab : GLALabel}
    (hlab : InnLabelOf B S lab) (hF4 : lab.tag = .F4) {d : Ω} (hdD : d ∈ D)
    (hdx : d ∉ Subgroup.zpowers x) (hdN : d ∈ Subgroup.normalizer (S : Set Ω)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (Φ : PSimple 3 S ≃* ↥(adjointGroup Tag.F4 F))
      (g : ↥(adjointGroup Tag.F4 F)), Nat.card F = 2 ^ lab.n ∧ orderOf g = 3 ∧
        MulAut.congr Φ (chevAut 3 S ⟨d, hdN⟩) = MulAut.conj g := by
  classical
  have hc := h.cfg
  obtain ⟨hDB, -⟩ := hc.std
  have hdB : d⁻¹ ∈ B := B.inv_mem (hDB hdD)
  obtain ⟨-, lab', -, hraw⟩ := hlab
  obtain ⟨-, -, -, -, -, -, -, heq, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst heq
  obtain ⟨t, r, n⟩ := lab'
  obtain rfl : t = .F4 := hF4
  obtain ⟨F, _, _, hF, -, -, θ, -, -, hact⟩ := hraw
  obtain ⟨φ, hφI, hφ⟩ := hact d⁻¹ hdB
  obtain ⟨r0, rfl⟩ := CFSG.StandardType.TableBF4.idImage_subset_inn F hφI
  have hker := S171.ker_chevQuotHom_eq_center' hc.prime hc.comp hc.quasi
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : PSimple 3 S ≃* ↥(adjointGroup Tag.F4 F), ∀ l : ↥S,
      Φ (chevQuotHom 3 S l) =
        CFSG.StandardType.TableBF4.recipeEquiv F (θ (l : ↥S ⧸ Subgroup.center ↥S)) := by
    let e₀ : ↥S ⧸ Subgroup.center ↥S ≃* PSimple 3 S :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ (chevQuotHom_surjective 3 S))
    refine ⟨(e₀.symm.trans θ).trans (CFSG.StandardType.TableBF4.recipeEquiv F), fun l => ?_⟩
    have he : e₀.symm (chevQuotHom 3 S l) = (l : ↥S ⧸ Subgroup.center ↥S) :=
      (MulEquiv.symm_apply_eq e₀).2 rfl
    simp only [MulEquiv.trans_apply, he]
  have hconj : MulAut.congr Φ (chevAut 3 S ⟨d, hdN⟩) =
      MulAut.conj (CFSG.StandardType.TableBF4.recipeEquiv F r0) := by
    ext y
    obtain ⟨l, rfl⟩ : ∃ l : ↥S, Φ (chevQuotHom 3 S l) = y := by
      obtain ⟨z, rfl⟩ := Φ.surjective y
      obtain ⟨l, rfl⟩ := chevQuotHom_surjective 3 S z
      exact ⟨l, rfl⟩
    have hl := hφ l (S.normalizerMonoidHom ⟨d, hdN⟩ l) (by rw [inv_inv] <;> rfl)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [chevAut_chevQuotHom, hΦ, hΦ, ← hl, MulAut.conj_apply, MulAut.conj_apply, map_mul,
      map_mul, map_inv]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd3 : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (S : Set Ω))) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hc.elem.2 d (hDB hdD))
  have hα1 : chevAut 3 S ⟨d, hdN⟩ ≠ 1 := fun h1 =>
    hdx ((hc.centB d (hDB hdD)).1 ((chevAut_eq_one_iff hc.prime hc.comp hdN).1 h1))
  refine ⟨F, inferInstance, inferInstance, Φ, _, hF, orderOf_eq_prime ?_ ?_, hconj⟩
  · have hz : CFSG.StandardType.TableBF4.recipeEquiv F r0 ^ 3 ∈
        Subgroup.center ↥(adjointGroup Tag.F4 F) := by
      have h3 : MulAut.conj (CFSG.StandardType.TableBF4.recipeEquiv F r0 ^ 3) = 1 := by
        rw [map_pow, ← hconj, ← map_pow, ← map_pow, hd3, map_one, map_one]
      refine Subgroup.mem_center_iff.2 fun y => ?_
      have hy := congrArg (fun ψ : MulAut ↥(adjointGroup Tag.F4 F) => ψ y) h3
      simp only [MulAut.conj_apply, MulAut.one_apply] at hy
      calc y * CFSG.StandardType.TableBF4.recipeEquiv F r0 ^ 3 =
          CFSG.StandardType.TableBF4.recipeEquiv F r0 ^ 3 * y *
            (CFSG.StandardType.TableBF4.recipeEquiv F r0 ^ 3)⁻¹ *
              CFSG.StandardType.TableBF4.recipeEquiv F r0 ^ 3 := by rw [hy]
        _ = _ := inv_mul_cancel_right _ _
    rwa [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
  · intro h1
    rw [h1, map_one] at hconj
    exact hα1 ((map_eq_one_iff _ (MulAut.congr Φ).injective).1 hconj)

end Glue

section Main


theorem qsF3ResF4_holds : QSF3ResF4 := by
  intro Ω _ _ S B T x D K lab h hcat _ hlab _ _ ⟨hF4, h3⟩
  have hc := h.cfg
  obtain ⟨-, -, -, -, -, hKc, -⟩ := hc.std
  have hKS : K ≤ S := hKc.1.trans inf_le_left
  obtain ⟨d, hdD, hdx⟩ := S171.exists_y hc.prime hc.x1 hc.std
  have hdN : d ∈ Subgroup.normalizer (S : Set Ω) :=
    (Subgroup.normalizer_eq_top_iff.2 hc.normal) ▸ Subgroup.mem_top d
  obtain ⟨F, _, _, Φ, g, hF, hg, hΦ⟩ := SG.exists_f4_conj_of_innLabelOf h hlab hF4 hdD hdx hdN
  obtain ⟨hall, hKc'⟩ := SG.isComponentOf_fixSubgroup_chevAut h hdD hdx hdN
  let f : ↥K →* ↥(adjointGroup Tag.F4 F) :=
    (Φ : PSimple 3 S →* ↥(adjointGroup Tag.F4 F)).comp
      ((chevQuotHom 3 S).comp (Subgroup.inclusion hKS))
  have hrange : f.range = ((K.subgroupOf S).map (chevQuotHom 3 S)).map
      (Φ : PSimple 3 S →* ↥(adjointGroup Tag.F4 F)) := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hα : MulAut.congr Φ.symm (MulAut.conj g) = chevAut 3 S ⟨d, hdN⟩ := by
    rw [← hΦ]
    ext z
    simp
  have hJ : IsComponentOf f.range (fixSubgroup (MulAut.conj g)) := by
    rw [hrange, ← hΦ, CFSG.HardMathSupport.Dickson.Bal207.fixSubgroup_mulAutCongr]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map Φ hKc'
  have hle : ∀ J' : Subgroup ↥(adjointGroup Tag.F4 F),
      IsComponentOf J' (fixSubgroup (MulAut.conj g)) → J' ≤ f.range := by
    intro J' hJ'
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map Φ.symm hJ'
    rw [← CFSG.HardMathSupport.Dickson.Bal207.fixSubgroup_mulAutCongr, hα] at h1
    rw [hrange, Subgroup.map_equiv_eq_comap_symm, ← Subgroup.map_le_iff_le_comap]
    exact hall _ h1
  obtain ⟨hadm, F', hF'1, hF'2, hF', ⟨θ⟩⟩ := SG.model_of_le_component_F4 hF h3 g hg hJ hle
  have hfk : f.ker ≤ Subgroup.center ↥K := fun k hk => by
    have hk1 : chevQuotHom 3 S (Subgroup.inclusion hKS k) = 1 :=
      (map_eq_one_iff Φ Φ.injective).1 hk
    have hk' : Subgroup.inclusion hKS k ∈ Subgroup.center ↥S := by
      rw [← S171.ker_chevQuotHom_eq_center' hc.prime hc.comp hc.quasi]
      exact hk1
    refine Subgroup.mem_center_iff.2 fun k' => Subtype.ext ?_
    exact congrArg (fun s : ↥S => (s : Ω))
      (Subgroup.mem_center_iff.1 hk' (Subgroup.inclusion hKS k'))
  obtain ⟨hsimp, t, m, ht, hLie⟩ := SG.lieModel_of_tyF hcat
  haveI : Nontrivial (PSimple 3 K) := hsimp.toNontrivial
  obtain ⟨eK⟩ := SF.nonempty_centerQuot_equiv_pSimple (p := 3) hKc.2.2
  obtain ⟨eR⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hKc.2.2.1 f.rangeRestrict f.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hfk)
  have hPSp : CFSG.Blueprint.LieModel (PSimple 3 K) .PSp 3 2 lab.n :=
    .inl ⟨by decide, hadm, F', hF'1, hF'2, hF', ⟨(eK.symm.trans eR).trans θ⟩⟩
  obtain ⟨htp, -, -⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique_classicalOrSuzuki hPSp
      (.inl (by rcases ht with rfl | rfl <;> decide)) hLie
  rcases ht with rfl | rfl <;> cases htp

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265

end
