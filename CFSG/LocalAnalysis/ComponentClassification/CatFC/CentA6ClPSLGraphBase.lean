module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBGraphForm (glGraphAut glTranspose slGraphAut
  pureGraphAction)
open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_iff_isComponent_subgroupOf
  isComponentOf_map_of_injective)
open CFSG.ComponentClassification.CatLeafProof (exists_component_of_quotientFixed)

section Transfer

variable {n : ℕ} {K : Type} [Field K] [Finite K] (A : GL (Fin n) K)

noncomputable def pgPsi : MulAut (SpecialLinearGroup (Fin n) K) :=
  slConjugation n K A * slGraphAut n K

theorem pgPsi_inv :
    (center (SpecialLinearGroup (Fin n) K)).map (pgPsi A).toMonoidHom =
      center (SpecialLinearGroup (Fin n) K) :=
  Subgroup.map_center_eq (pgPsi A)

theorem pureGraphAction_eq_onQuotient :
    pureGraphAction n K A = CatalogueBFixedCentralQuotient.onQuotient
      (center (SpecialLinearGroup (Fin n) K)) (pgPsi A) (pgPsi_inv A) := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [show ((g : SpecialLinearGroup (Fin n) K ⧸ center (SpecialLinearGroup (Fin n) K)) :
        SpecialLinearGroup (Fin n) K ⧸ center (SpecialLinearGroup (Fin n) K)) =
        QuotientGroup.mk' (center (SpecialLinearGroup (Fin n) K)) g from rfl,
      CatalogueBFixedCentralQuotient.onQuotient_mk]
    exact CatalogueBGraphForm.pureGraphAction_mk n K A g

theorem pgFix_iff (x : GL (Fin n) K) :
    A * glGraphAut n K x * A⁻¹ = x ↔ glTranspose n K x * A⁻¹ * x = A⁻¹ := by
  have hT : glGraphAut n K x = (glTranspose n K x)⁻¹ := (inv_inv _).symm
  rw [hT]
  constructor
  · intro h
    calc glTranspose n K x * A⁻¹ * x =
        glTranspose n K x * A⁻¹ * (A * (glTranspose n K x)⁻¹ * A⁻¹) := by rw [h]
      _ = A⁻¹ := by group
  · intro h
    calc A * (glTranspose n K x)⁻¹ * A⁻¹ =
        A * (glTranspose n K x)⁻¹ * (glTranspose n K x * A⁻¹ * x) := by rw [h]
      _ = x := by group

theorem fixedSL_map_eq :
    (fixedSubgroup (pgPsi A)).map SpecialLinearGroup.toGL =
      CatalogueBGraphForm.isometryGroup n K A⁻¹ ⊓
        CatalogueBGeneralLinear.specialLinearRange n K := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
    have h1 : SpecialLinearGroup.toGL (pgPsi A g) = SpecialLinearGroup.toGL g :=
      congrArg _ (show pgPsi A g = g from hg)
    rw [pgPsi, MulAut.mul_apply, toGL_slConjugation, CatalogueBGraphForm.toGL_slGraphAut] at h1
    exact (pgFix_iff A _).mp h1
  · intro hy
    obtain ⟨hyI, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
    refine ⟨g, ?_, rfl⟩
    change pgPsi A g = g
    apply SpecialLinearGroup.toGL_injective
    rw [pgPsi, MulAut.mul_apply, toGL_slConjugation, CatalogueBGraphForm.toGL_slGraphAut]
    exact (pgFix_iff A _).mpr hyI

theorem pureGraph_component_transfer
    {L : Subgroup (fixedSubgroup (pureGraphAction n K A))} (hL : IsComponent L) :
    ∃ N : Subgroup ↥(CatalogueBGraphForm.isometryGroup n K A⁻¹), IsComponent N ∧
      Nonempty (L ⧸ center L ≃* N ⧸ center N) := by
  set Z := center (SpecialLinearGroup (Fin n) K) with hZ
  let eF := MulEquiv.subgroupCongr (congrArg fixedSubgroup (pureGraphAction_eq_onQuotient A))
  have hL' := LocalCores.isComponent_map_mulEquiv eF hL
  obtain ⟨M, hM, ⟨eLM⟩⟩ := exists_component_of_quotientFixed Z le_rfl (pgPsi A) (pgPsi_inv A) hL'
  have hMF : Assembly.IsComponentOf (M.map (fixedSubgroup (pgPsi A)).subtype)
      (fixedSubgroup (pgPsi A)) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le M)).2 ?_
    have hMM : (M.map (fixedSubgroup (pgPsi A)).subtype).subgroupOf (fixedSubgroup (pgPsi A)) =
        M := Subgroup.comap_map_eq_self_of_injective (subtype_injective _) M
    rw [hMM]
    exact hM
  have h1 := isComponentOf_map_of_injective hMF SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective
  rw [fixedSL_map_eq] at h1
  have hnormal : ((CatalogueBGraphForm.isometryGroup n K A⁻¹ ⊓
      CatalogueBGeneralLinear.specialLinearRange n K).subgroupOf
        (CatalogueBGraphForm.isometryGroup n K A⁻¹)).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨-, hxS⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(g * x * g⁻¹).2, ?_⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (CatalogueBGeneralLinear.specialLinearRangeNormal n K).conj_mem _ hxS (g : GL (Fin n) K)
  have h2 := OddClassSelector.isComponentOf_of_normal_le h1 inf_le_left hnormal
  have h3 := (isComponentOf_iff_isComponent_subgroupOf h2.1).1 h2
  refine ⟨_, h3, ⟨?_⟩⟩
  let eMN : M ≃* (((M.map (fixedSubgroup (pgPsi A)).subtype).map
      SpecialLinearGroup.toGL).subgroupOf (CatalogueBGraphForm.isometryGroup n K A⁻¹)) :=
    ((M.equivMapOfInjective (fixedSubgroup (pgPsi A)).subtype (subtype_injective _)).trans
      ((M.map (fixedSubgroup (pgPsi A)).subtype).equivMapOfInjective SpecialLinearGroup.toGL
        SpecialLinearGroup.toGL_injective)).trans
      (Subgroup.subgroupOfEquivOfLe h2.1).symm
  let eL : L ≃* L.map eF.toMonoidHom := L.equivMapOfInjective eF.toMonoidHom eF.injective
  exact (QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans
    (eLM.trans (QuotientGroup.congr _ _ eMN (Subgroup.map_center_eq eMN)))

noncomputable def pgTheta :
    ↥(fixedSubgroup (pgPsi A)) →* ↥(fixedSubgroup (pureGraphAction n K A)) :=
  ((QuotientGroup.mk' (center (SpecialLinearGroup (Fin n) K))).comp
      (fixedSubgroup (pgPsi A)).subtype).codRestrict (fixedSubgroup (pureGraphAction n K A))
    (fun x => by
      have hx : pgPsi A x.1 = x.1 := x.2
      change pureGraphAction n K A (QuotientGroup.mk' _ x.1) = QuotientGroup.mk' _ x.1
      rw [pureGraphAction_eq_onQuotient A, CatalogueBFixedCentralQuotient.onQuotient_mk, hx])

theorem pgTheta_eq_one_iff (b : ↥(fixedSubgroup (pgPsi A))) :
    pgTheta A b = 1 ↔ b.1 ∈ center (SpecialLinearGroup (Fin n) K) := by
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 h)

noncomputable def pgFixEquiv : ↥(fixedSubgroup (pgPsi A)) ≃*
    ↥(CatalogueBGraphForm.isometryGroup n K A⁻¹ ⊓
      CatalogueBGeneralLinear.specialLinearRange n K) :=
  ((fixedSubgroup (pgPsi A)).equivMapOfInjective SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr (fixedSL_map_eq A))

variable {X : Type} [Group X] (j : X →* ↥(CatalogueBGraphForm.isometryGroup n K A⁻¹))
  (hdet : ∀ x, Matrix.GeneralLinearGroup.det ((j x : GL (Fin n) K)) = 1)

noncomputable def pgJ : X →* ↥(CatalogueBGraphForm.isometryGroup n K A⁻¹ ⊓
    CatalogueBGeneralLinear.specialLinearRange n K) :=
  ((CatalogueBGraphForm.isometryGroup n K A⁻¹).subtype.comp j).codRestrict _
    (fun x => Subgroup.mem_inf.2 ⟨(j x).2, by
      rw [CatalogueBGeneralLinear.specialLinearRange_eq_detKernel]
      exact MonoidHom.mem_ker.2 (hdet x)⟩)

noncomputable def pgPhi : X →* ↥(fixedSubgroup (pureGraphAction n K A)) :=
  (pgTheta A).comp ((pgFixEquiv A).symm.toMonoidHom.comp (pgJ A j hdet))

theorem pgJ_injective (hj : Function.Injective j) : Function.Injective (pgJ A j hdet) := by
  intro a b h
  have h' : (pgJ A j hdet a).1 = (pgJ A j hdet b).1 := congrArg Subtype.val h
  exact hj (Subtype.ext h')

theorem pgPhi_ker_le_center (hj : Function.Injective j) : (pgPhi A j hdet).ker ≤ center X := by
  intro x hx
  have hxc : ((pgFixEquiv A).symm (pgJ A j hdet x)).1 ∈ center (SpecialLinearGroup (Fin n) K) :=
    (pgTheta_eq_one_iff A _).1 (MonoidHom.mem_ker.1 hx)
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 := Subgroup.mem_center_iff.1 hxc ((pgFixEquiv A).symm (pgJ A j hdet y)).1
  have h2 : (pgFixEquiv A).symm (pgJ A j hdet (y * x)) =
      (pgFixEquiv A).symm (pgJ A j hdet (x * y)) := by
    rw [map_mul, map_mul, map_mul, map_mul]
    exact Subtype.ext h1
  exact pgJ_injective A j hdet hj ((pgFixEquiv A).symm.injective h2)

end Transfer

section Kill

variable {S : Type} [Group S] [Finite S] {σ : MulAut S} {D : Subgroup ↥(fixedSubgroup σ)}

theorem A6Hyp.center_eq_bot (h : A6Hyp σ D) : center ↥D = ⊥ := by
  obtain ⟨-, ⟨eD⟩, -⟩ := h
  have h1 := Subgroup.map_center_eq eD
  rw [a6sq_center] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ eD.injective).1 h1

theorem A6Hyp.false_of_commuting_pair (h : A6Hyp σ D) {G : Type} [Group G]
    (φ : G →* ↥(fixedSubgroup σ)) (hker : φ.ker ≤ center G) {L₁ L₂ : Subgroup G}
    (h₁ : ⁅L₁, L₁⁆ = L₁) (h₂ : ⁅L₂, L₂⁆ = L₂) (hc : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    (hL₁ : 360 ≤ Nat.card (L₁ ⧸ center L₁)) (hL₂ : ¬ L₂ ≤ center G) : False := by
  have hP₁perf : ⁅L₁.map φ, L₁.map φ⁆ = L₁.map φ := by rw [← Subgroup.map_commutator, h₁]
  have hP₁D : L₁.map φ ≤ D := h.2.2 _ hP₁perf
  have hcard : 360 ≤ Nat.card (L₁.map φ) := by
    set ρ : L₁ →* ↥(fixedSubgroup σ) := φ.comp L₁.subtype with hρ
    have hker' : ρ.ker ≤ center L₁ := by
      intro x hx
      have hx1 : (x : G) ∈ center G := hker (MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hx))
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.1 hx1 y.1)
    have hrange : ρ.range = L₁.map φ := by rw [hρ, MonoidHom.range_comp, Subgroup.range_subtype]
    have h3 : Nat.card (L₁ ⧸ center L₁) ∣ Nat.card (L₁.map φ) := by
      have := Subgroup.index_dvd_of_le hker'
      rwa [Subgroup.index_ker, hrange, Subgroup.index_eq_card] at this
    exact hL₁.trans (Nat.le_of_dvd Nat.card_pos h3)
  have hP₁ : L₁.map φ = D :=
    Subgroup.eq_of_le_of_card_ge hP₁D (by rw [h.card_D]; exact hcard)
  have hP₂perf : ⁅L₂.map φ, L₂.map φ⁆ = L₂.map φ := by rw [← Subgroup.map_commutator, h₂]
  have hP₂D : L₂.map φ ≤ D := h.2.2 _ hP₂perf
  have hbot : ∀ y ∈ L₂, φ y = 1 := by
    intro y hy
    have hyD : φ y ∈ D := hP₂D (Subgroup.mem_map_of_mem φ hy)
    have hcen : (⟨φ y, hyD⟩ : ↥D) ∈ center ↥D := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz : (z : ↥(fixedSubgroup σ)) ∈ L₁.map φ := hP₁ ▸ z.2
      obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.1 hz
      apply Subtype.ext
      change (z : ↥(fixedSubgroup σ)) * φ y = φ y * (z : ↥(fixedSubgroup σ))
      rw [← hxz, ← map_mul, ← map_mul, hc x hx y hy]
    rw [h.center_eq_bot] at hcen
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hcen)
  exact hL₂ fun y hy => hker (MonoidHom.mem_ker.2 (hbot y hy))

end Kill

end CFSG.ComponentClassification.CatFC
