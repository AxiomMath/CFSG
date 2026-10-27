module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianStatements
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearLayerCore
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearFlag GL3TwoFixedModel
open LinearMap (BilinForm)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem SteinbergBM.exists_mul_ne_mul_GL_three_two :
    ∃ a b : GL (Fin 3) (ZMod 2), a * b ≠ b * a := by
  have := isSimpleGroup_GL_three_two
  by_contra h
  have h' : ∀ a b : GL (Fin 3) (ZMod 2), a * b = b * a := fun a b => by
    by_contra hab
    exact h ⟨a, b, hab⟩
  let _ : CommGroup (GL (Fin 3) (ZMod 2)) := { mul_comm := h' }
  have hp := IsSimpleGroup.prime_card (α := GL (Fin 3) (ZMod 2))
  rw [GL3TwoFixedModel.card_GL_three_two] at hp
  norm_num at hp

section Sector

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) (z : G)

@[expose] def Sp6EvenLinearPSLSector : Prop :=
  CFSG.Blueprint.Catalog (sp6Dstar φ he z) ∧
  ∀ (n f : ℕ), 2 ≤ n → 1 ≤ f → ∀ (K : Type) [Field K], Nat.card K = 2 ^ f →
  ∀ η : sp6Dstar φ he z ≃* projectiveSL n K,
    n = 3 ∧ f = 2 ∧ sp6JLBar φ he z = sp6Dstar φ he z ⊓ centralizer {sp6aBar φ he z} ∧
    Nat.card (sp6Dstar φ he z) = 20160 ∧ ordProj[2] (Nat.card (sp6Dstar φ he z)) = 64 ∧
    (∀ x ∈ sp6Dstar φ he z, ∃ d ∈ sp6Dstar φ he z,
      (sp6aBar φ he z)⁻¹ * d * sp6aBar φ he z ≠ x * d * x⁻¹) ∧
    sp6aBar φ he z ∉ sp6Dstar φ he z ∧
    ∃ (hn3 : n = 3) (_ : CharP K 2) (σ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c),
      (∀ c, σ c = c ^ 2) ∧
      ∃ (B : GL (Fin n) K) (e : ℕ) (χ : sp6Dstar φ he z ≃* projectiveSL n K), e ≤ 1 ∧
        (∀ d, χ d = (conjAut n K B * dualAut n K ^ e) (η d)) ∧
        (∀ (d : Sp6Y φ he z) (hd : d ∈ sp6Dstar φ he z)
            (hda : (sp6aBar φ he z)⁻¹ * d * sp6aBar φ he z ∈ sp6Dstar φ he z),
          χ ⟨_, hda⟩ = fieldAut n K σ (χ ⟨d, hd⟩)) ∧
        (∀ (g : GL (Fin 3) (ZMod 2)) (h : sp6θ φ he z (sp6Levi φ he z g) ∈ sp6Dstar φ he z),
          χ ⟨_, h⟩ = binaryEmbed K hn3 g) ∧
        (∃ ψ : ↥(sp6Dstar φ he z ⊔ zpowers (sp6aBar φ he z)) ≃*
            projectiveSL n K ⋊[SteinbergBM.fieldInvolHom σ hσσ] Multiplicative (ZMod 2),
          (∀ d : sp6Dstar φ he z,
            ψ ⟨d, le_sup_left (a := sp6Dstar φ he z) d.2⟩ = SemidirectProduct.inl (χ d)) ∧
          ψ ⟨sp6aBar φ he z, le_sup_right (a := sp6Dstar φ he z) (mem_zpowers _)⟩ =
            SemidirectProduct.inr (Multiplicative.ofAdd 1)) ∧
        ∃ (hQ : ∀ q : sp6Qstar φ he z, sp6θ φ he z q ∈ sp6Dstar φ he z)
          (ε : sp6Qstar φ he z →* projectiveSL n K),
          (∀ q, ε q = χ ⟨_, hQ q⟩) ∧ Function.Surjective ε ∧
          ε.ker = (sp6Ro φ he z).subgroupOf (sp6Qstar φ he z)

theorem sp6_even_linear_psl_sector [Finite G] {V₁ : Subgroup G}
    (hconc : Sp6LagrangianLayerConclusion φ he z V₁) (hsimple : Sp6LayerSimple φ he z) :
    Sp6EvenLinearPSLSector φ he z := by
  set D := sp6Dstar φ he z
  set S := sp6JLBar φ he z
  set ā := sp6aBar φ he z
  obtain ⟨-, -, -, -, ⟨ι, hιdef, hιinj, hιrange⟩, -, hYK, -, -, -, -, hθJL, -, -, -, -, -, -,
    haBar2, hJCa, -, hCa, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨eQ, heQ⟩, -⟩ := hconc
  obtain ⟨hDs, -, hJD, hact⟩ := hsimple
  have hDn : D.Normal := Subgroup.normalClosure_normal
  have hā2 : ā * ā = 1 := by
    have h := pow_orderOf_eq_one ā
    rwa [haBar2, pow_two] at h
  have hāinv : ā⁻¹ = ā := inv_eq_of_mul_eq_one_right hā2
  have hψinj : Function.Injective ((sp6θ φ he z).comp ι) := by
    intro g g' hgg
    apply hιinj
    refine hθJL ?_ ?_ hgg
    · rw [← hιrange]
      exact ⟨g, rfl⟩
    · rw [← hιrange]
      exact ⟨g', rfl⟩
  have hψrange : ((sp6θ φ he z).comp ι).range = S := by
    rw [MonoidHom.range_comp, hιrange]
    rfl
  set κ : S ≃* GL (Fin 3) (ZMod 2) :=
    ((MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange)).symm with hκ
  have hκsymm : ∀ g, ((κ.symm g : S) : Sp6Y φ he z) = sp6θ φ he z (ι g) := fun _ => rfl
  have : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := isSimpleGroup_GL_three_two
  have : IsSimpleGroup S := κ.isSimpleGroup
  have hSnab : ∃ x y : S, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := SteinbergBM.exists_mul_ne_mul_GL_three_two
    refine ⟨κ.symm x, κ.symm y, fun h => hxy (κ.symm.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have hSn : (S.subgroupOf (centralizer {ā})).Normal := by
    have haN : ā ∈ normalizer (S : Set (Sp6Y φ he z)) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.2 fun j hj =>
        mem_centralizer_singleton_iff.1 (hJCa hj))
    rw [normal_subgroupOf_iff_le_normalizer hJCa, ← hCa]
    exact sup_le (zpowers_le.2 haN) le_normalizer
  have hact' : ∃ d ∈ D, ā * d * ā⁻¹ ≠ d := by
    obtain ⟨d, hd, hne⟩ := hact
    refine ⟨d, hd, ?_⟩
    rw [hāinv] at hne ⊢
    exact hne
  have hcatalog : CFSG.Blueprint.Catalog D :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hYK D (MonoidHom.id D)
      Function.surjective_id
  refine ⟨hcatalog, fun n f hn hf K _ hK η => ?_⟩
  obtain ⟨h3, h2, hfix, hcard, hord, hout, haD, hn3, hchar, σ, hσ, -, -, B, e, he1, hint, hlab⟩ :=
    SteinbergBM.even_linear_simple_layer_core haBar2 hact' hJD.le hJCa hSn hSnab κ hn hf hK η
  have hσσ : ∀ c, σ (σ c) = c := by
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have : Fintype K := Fintype.ofFinite K
    have hK4 : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK, h2]; norm_num
    intro c
    rw [hσ, hσ, ← pow_mul]
    have h := FiniteField.pow_card c
    rwa [hK4] at h
  set χ : D ≃* projectiveSL n K := η.trans (conjAut n K B * dualAut n K ^ e) with hχ
  have hχapp : ∀ d, χ d = (conjAut n K B * dualAut n K ^ e) (η d) := fun _ => rfl
  have hconj : ∀ (d : Sp6Y φ he z) (hd : d ∈ D) (hda : ā⁻¹ * d * ā ∈ D),
      MulAut.conjNormal ā (⟨d, hd⟩ : D) = ⟨_, hda⟩ := fun d hd hda => by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    change ā * d * ā⁻¹ = ā⁻¹ * d * ā
    rw [hāinv]
  have hint' : ∀ d : D, χ (MulAut.conjNormal ā d) = fieldAut n K σ (χ d) := hint
  obtain ⟨ψ, hψD, hψa⟩ := SteinbergBM.exists_layer_semidirect_equiv haBar2 haD χ σ hσσ hint'
  refine ⟨h3, h2, hfix, hcard, hord, fun x hx => ?_, haD, hn3, hchar, σ, hσσ, hσ, B, e, χ, he1,
    hχapp, fun d hd hda => ?_, fun g h => ?_, ⟨ψ, hψD, hψa⟩, ?_⟩
  ·
    by_contra hcon
    push Not at hcon
    apply hout
    refine ⟨⟨x, hx⟩, MulEquiv.ext fun d => Subtype.ext ?_⟩
    rw [MulAut.conjNormal_apply, MulAut.conj_apply]
    change x * (d : Sp6Y φ he z) * x⁻¹ = ā * d * ā⁻¹
    rw [← hcon d d.2, hāinv]
  ·
    rw [← hconj d hd hda]
    exact hint' ⟨d, hd⟩
  ·
    have hs : ((κ.symm g : S) : Sp6Y φ he z) = sp6θ φ he z (sp6Levi φ he z g) := by
      rw [hκsymm, hιdef]
    have h1 : (⟨_, h⟩ : D) = ⟨(κ.symm g : S), hJD.le (κ.symm g).2⟩ := Subtype.ext hs.symm
    rw [h1, hχapp, hlab, MulEquiv.apply_symm_apply]
  ·
    have hQ : ∀ q : sp6Qstar φ he z, sp6θ φ he z q ∈ D := fun q => by
      rw [← heQ q]
      exact (eQ (QuotientGroup.mk q)).2
    have heQq : ∀ q : sp6Qstar φ he z, eQ (QuotientGroup.mk q) = ⟨_, hQ q⟩ :=
      fun q => Subtype.ext (heQ q)
    refine ⟨hQ, (χ.toMonoidHom.comp eQ.toMonoidHom).comp (QuotientGroup.mk' _), fun q => ?_,
      χ.surjective.comp (eQ.surjective.comp (QuotientGroup.mk'_surjective _)), ?_⟩
    · change χ (eQ (QuotientGroup.mk q)) = _
      rw [heQq]
    · ext q
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
        MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

end Sector

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
