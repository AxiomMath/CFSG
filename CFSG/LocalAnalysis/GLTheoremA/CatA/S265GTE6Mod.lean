module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107LFrob
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

private theorem twE6_of_markTag {lab : GLALabel} {f : ℕ}
    (hlt : CFSG.StandardType.markTag lab = .twistedE6) (hdeg : CFSG.StandardType.markDeg lab = f) :
    lab.tag = .twE6 ∧ lab.n = f := by
  obtain ⟨tg, r, n⟩ := lab
  unfold CFSG.StandardType.markTag at hlt
  unfold CFSG.StandardType.markDeg at hdeg
  cases tg <;> simp only at hlt hdeg ⊢ <;> (try split_ifs at hlt hdeg) <;> simp_all

private theorem congr_symm_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) (φ : MulAut A) :
    MulAut.congr e.symm (MulAut.congr e φ) = φ := by
  ext a
  simp [MulAut.congr_apply]

private theorem congr_trans_congr {A B P : Type*} [Group A] [Group B] [Group P] (ψ : MulAut A)
    (ε : A ≃* B) (θ : P ≃* B) (y : MulAut A) :
    MulAut.congr (MulEquiv.trans ψ (ε.trans θ.symm)).symm
      (MulAut.congr θ.symm (MulAut.congr ε y)) =
      ψ⁻¹ * y * ψ := by
  ext a
  simp [MulAut.congr_apply, MulAut.mul_apply, MulAut.inv_def]


theorem exists_model_fieldActor_of_fieldOn {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {b : Ω}
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 S)) (hF : FieldOn 3 b S)
    (hL : CFSG.Blueprint.LieModel (PSimple 3 S) .twistedE6 0 2 3) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ δ : K ≃+* K), Nat.card K = (2 ^ 3) ^ 2 ∧
      (∀ c, σ c = c ^ 2 ^ 3) ∧ orderOf δ = 3 ∧
      Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ ∧
      ∃ ε : ↥(twistedE6RootGroup K σ) ≃* PSimple 3 S,
        MulAut.congr ε.symm (chevAut 3 S ⟨b, hF.1⟩) = fieldActor σ δ := by
  obtain ⟨hX, lab, hlam, hraw⟩ := hF.2
  haveI : Group.IsPerfect (PQuot 3 S) := ⟨hq.1⟩
  have hZ : Subgroup.center (PSimple 3 S) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot (PQuot 3 S)
  haveI hsimp : IsSimpleGroup (PSimple 3 S) := hq.2
  have hnab : ∀ (R : Type) [Group R], (PSimple 3 S ≃* R) → ∃ a c : R, a * c ≠ c * a := by
    intro R _ e
    obtain ⟨a, ha⟩ := exists_ne (1 : PSimple 3 S)
    by_contra h
    apply ha
    have hmem : a ∈ Subgroup.center (PSimple 3 S) := Subgroup.mem_center_iff.2 fun g =>
      e.injective (by
        rw [map_mul, map_mul]
        exact not_not.1 fun hne => h ⟨e g, e a, hne⟩)
    rw [hZ] at hmem
    exact Subgroup.mem_bot.1 hmem
  obtain ⟨labm, hlamm, ht, -, -, hdeg, hrawm⟩ :=
    CFSG.StandardType.Canonical.exists_label_rawDatum_of_lieModel hZ hL
  have hlabm : Y10F.HasLabel (PQuot 3 S) (· = labm) :=
    ⟨hX, labm, hlamm, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ _ _ ⟨e⟩ => ⟨e.symm.isSimpleGroup, hnab R e, e, rfl⟩) hrawm⟩
  have hlab : Y10F.HasLabel (PQuot 3 S) (· = lab) :=
    ⟨hX, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  have hE : K1419E.ExcGLATag labm :=
    K1419E.excGLATag_of_markTag (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) ht
  obtain ⟨hlamm', -, hGlamm⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hlabm
  obtain ⟨hlam', -, hGlab⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hlab
  have heq : lab = labm := K1419E.eq_of_ggLabelIso_exc
    (CFSG.StandardType.ggLabelRigidInput_holds labm lab (PQuot 3 S ⧸ Subgroup.center (PQuot 3 S))
      hlamm' hlam' hGlamm hGlab) hE
  obtain ⟨htag, hn⟩ := twE6_of_markTag ht hdeg
  subst heq
  clear hlab hlabm hE hGlamm hGlab hrawm hlamm hlamm' hlam'
  obtain ⟨tg, r, n⟩ := lab
  simp only at htag hn
  subst htag hn
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  obtain ⟨K, _, _, hK, -, -, θ, -, f, hf, u, hu, hord, hind⟩ := hraw
  haveI : CharP K 2 := I107L.charP_two_of_card_sq hK
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 ^ 3 :=
    ⟨iterateFrobeniusEquiv K 2 3, fun c => by
      rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]⟩
  obtain ⟨ε, hεI, hεF⟩ :=
    CFSG.StandardType.TwE6FieldCore.exists_recipeConj_field (n := 3) (by norm_num) hK σ hσ
  obtain ⟨δ, hδ⟩ := hεF f hf
  obtain ⟨w, hw⟩ := (hεI u).2 hu
  have hfa3 : orderOf (fieldActor (t := CFSG.Blueprint.Chevalley.TwistTag.E6) σ δ) = 3 := by
    rw [← hord, hδ]
    exact (orderOf_injective (MulAut.congr ε).toMonoidHom (MulAut.congr ε).injective _).symm
  have hδ3 : orderOf δ = 3 := by
    rw [← CFSG.StandardType.TwE6FieldCore.orderOf_fieldActor (n := 3) (by norm_num) hK hσ δ, hfa3]
  have e1 : u * f * u⁻¹ = MulAut.congr θ (indAut 3 S b hF.1) := (induces_indRel_iff hF.1 θ).1 hind
  rw [OutCyc.indAut_eq_inv_chevAut, ← hw, CFSG.StandardType.TwE6Transport.recipeConj_eq, hδ,
    ← map_inv (MulAut.congr ε), ← map_mul (MulAut.congr ε), ← map_mul (MulAut.congr ε)] at e1
  have hc : (chevAut 3 S ⟨b, hF.1⟩)⁻¹ = MulAut.congr θ.symm (MulAut.congr ε
      (CFSG.StandardType.RecipeExcLang.twConj K σ w * fieldActor σ δ *
        (CFSG.StandardType.RecipeExcLang.twConj K σ w)⁻¹)) := by
    rw [e1, congr_symm_congr]
  have hZC : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (ε.trans θ.symm) x ∈ Subgroup.center (PSimple 3 S) :=
      Subgroup.mem_center_iff.2 fun g => by
        obtain ⟨y, rfl⟩ := (ε.trans θ.symm).surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
    rw [hZ, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 ((ε.trans θ.symm).injective (h1.trans (map_one _).symm))
  refine ⟨K, inferInstance, inferInstance, σ, δ⁻¹, hK, hσ, by rw [orderOf_inv, hδ3], hZC,
    MulEquiv.trans (CFSG.StandardType.RecipeExcLang.twConj K σ w) (ε.trans θ.symm), ?_⟩
  have hinv :
      fieldActor σ δ⁻¹ = (fieldActor (t := CFSG.Blueprint.Chevalley.TwistTag.E6) σ δ)⁻¹ := by
    rw [← fieldActorHom_apply σ δ⁻¹, map_inv, fieldActorHom_apply]
  rw [hinv, ← inv_inv (chevAut 3 S ⟨b, hF.1⟩), map_inv (MulAut.congr _), hc, congr_trans_congr]
  group

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
