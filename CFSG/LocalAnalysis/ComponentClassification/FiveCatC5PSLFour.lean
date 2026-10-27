module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5PSLBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLGraphBase

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.C5PSL

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf Matrix
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction isometryGroup glGraphAut)
open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.ComponentClassification.CatFC
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_iff_isComponent_subgroupOf
  isComponentOf_map_fixed commutator_comap_map_eq)

section Lift

variable {n : ℕ} {K : Type} [Field K] [Finite K] (A : GL (Fin n) K)

@[expose] noncomputable def psi : MulAut (SpecialLinearGroup (Fin n) K) :=
  CatalogueBHigherLinearAction.slConjugation n K A * CatalogueBGraphForm.slGraphAut n K

theorem psi_inv : (center (SpecialLinearGroup (Fin n) K)).map (psi A).toMonoidHom =
    center (SpecialLinearGroup (Fin n) K) :=
  Subgroup.map_center_eq (psi A)

theorem toGL_psi (y : SpecialLinearGroup (Fin n) K) :
    SpecialLinearGroup.toGL (psi A y) = A * glGraphAut n K (SpecialLinearGroup.toGL y) * A⁻¹ := by
  change SpecialLinearGroup.toGL (CatalogueBHigherLinearAction.slConjugation n K A
    (CatalogueBGraphForm.slGraphAut n K y)) = _
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, CatalogueBGraphForm.toGL_slGraphAut]

theorem pureGraphAction_eq_onQuotient' :
    pureGraphAction n K A = CatalogueBFixedCentralQuotient.onQuotient
      (center (SpecialLinearGroup (Fin n) K)) (psi A) (psi_inv A) := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [show ((g : SpecialLinearGroup (Fin n) K ⧸ center (SpecialLinearGroup (Fin n) K)) :
        SpecialLinearGroup (Fin n) K ⧸ center (SpecialLinearGroup (Fin n) K)) =
        QuotientGroup.mk' (center (SpecialLinearGroup (Fin n) K)) g from rfl,
      CatalogueBFixedCentralQuotient.onQuotient_mk]
    exact CatalogueBGraphForm.pureGraphAction_mk n K A g

theorem fixed_psi_map_eq :
    (fixedSubgroup (psi A)).map SpecialLinearGroup.toGL =
      isometryGroup n K A⁻¹ ⊓ CatalogueBGeneralLinear.specialLinearRange n K := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
    have h1 : SpecialLinearGroup.toGL (psi A g) = SpecialLinearGroup.toGL g :=
      congrArg _ (show psi A g = g from hg)
    rw [toGL_psi] at h1
    exact (pgFix_iff A _).mp h1
  · intro hy
    obtain ⟨hyI, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
    refine ⟨g, ?_, rfl⟩
    change psi A g = g
    apply SpecialLinearGroup.toGL_injective
    rw [toGL_psi]
    exact (pgFix_iff A _).mpr hyI

noncomputable def psiFixEquiv : ↥(fixedSubgroup (psi A)) ≃*
    ↥(isometryGroup n K A⁻¹ ⊓ CatalogueBGeneralLinear.specialLinearRange n K) :=
  ((fixedSubgroup (psi A)).equivMapOfInjective SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr (fixed_psi_map_eq A))

theorem psi_involutive (hn : 3 ≤ n) (hsq : pureGraphAction n K A ^ 2 = 1) :
    ∀ x, psi A (psi A x) = x := by
  obtain ⟨lam, hlam⟩ := CatalogueBGraphForm.pureGraph_involution_scalar n K hn A hsq
  intro x
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_psi, toGL_psi, map_mul, map_mul, map_inv,
    Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose]
  generalize SpecialLinearGroup.toGL x = g
  calc A * (glGraphAut n K A * g * (glGraphAut n K A)⁻¹) * A⁻¹
      = (A * glGraphAut n K A) * g * (A * glGraphAut n K A)⁻¹ := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin n) lam * g *
          (Matrix.GeneralLinearGroup.scalar (Fin n) lam)⁻¹ := by rw [hlam]
    _ = g := by
      rw [Matrix.GeneralLinearGroup.scalar_commute]
      group

end Lift

theorem isComponent_comap_of_le {G H : Type} [Group G] [Group H] (ι : H →* G)
    (hι : Function.Injective ι) {F : Subgroup G} (hF : IsComponent F) (hle : F ≤ ι.range) :
    IsComponent (F.comap ι) := by
  refine ⟨?_, hF.2.comap ι⟩
  have hmap : (F.comap ι).map ι = F := by
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hle]
  exact LocalCores.isQuasisimple_of_mulEquiv
    ((MulEquiv.subgroupCongr hmap.symm).trans ((F.comap ι).equivMapOfInjective ι hι).symm) hF.1

theorem pg_two_components {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n)
    (A : GL (Fin n) K) (hsq : pureGraphAction n K A ^ 2 = 1) {G₀ : Type} [Group G₀]
    (e₁ : ↥(isometryGroup n K A⁻¹) ≃* G₀) {F₁ F₂ : Subgroup G₀} (h₁ : IsComponent F₁)
    (h₂ : IsComponent F₂) (hne : F₁ ≠ F₂) (hΩ₁ : F₁ ≤ commutator G₀) (hΩ₂ : F₂ ≤ commutator G₀) :
    ∃ L₁ L₂ : Subgroup ↥(fixedSubgroup (pureGraphAction n K A)),
      IsComponent L₁ ∧ IsComponent L₂ ∧ L₁ ≠ L₂ := by
  set B := fixedSubgroup (psi A) with hB
  let incl : ↥(isometryGroup n K A⁻¹ ⊓ CatalogueBGeneralLinear.specialLinearRange n K) →*
      ↥(isometryGroup n K A⁻¹) := Subgroup.inclusion inf_le_left
  have hincl : Function.Injective incl := Subgroup.inclusion_injective _
  let Θ : ↥B →* G₀ := e₁.toMonoidHom.comp (incl.comp (psiFixEquiv A).toMonoidHom)
  have hΘ : Function.Injective Θ := fun a b hab =>
    (psiFixEquiv A).injective (hincl (e₁.injective hab))
  have hrange : ∀ {F : Subgroup G₀}, F ≤ commutator G₀ → F ≤ Θ.range := by
    intro F hF g hg
    let D : G₀ →* Kˣ := (Matrix.GeneralLinearGroup.det (n := Fin n) (R := K)).comp
      ((isometryGroup n K A⁻¹).subtype.comp e₁.symm.toMonoidHom)
    have hdet : D g = 1 := MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker D (hF hg))
    have hmem : ((e₁.symm g : ↥(isometryGroup n K A⁻¹)) : GL (Fin n) K) ∈
        isometryGroup n K A⁻¹ ⊓ CatalogueBGeneralLinear.specialLinearRange n K :=
      Subgroup.mem_inf.2 ⟨(e₁.symm g).2, by
        rw [CatalogueBGeneralLinear.specialLinearRange_eq_detKernel]
        exact hdet⟩
    refine ⟨(psiFixEquiv A).symm ⟨_, hmem⟩, ?_⟩
    change e₁ (incl ((psiFixEquiv A) ((psiFixEquiv A).symm ⟨_, hmem⟩))) = g
    rw [MulEquiv.apply_symm_apply]
    exact (congrArg e₁ (Subtype.ext rfl)).trans (e₁.apply_symm_apply g)
  set π := QuotientGroup.mk' (center (SpecialLinearGroup (Fin n) K)) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ center (SpecialLinearGroup (Fin n) K) := by
    rw [hπdef, QuotientGroup.ker_mk']
  have ha := psi_involutive A hn hsq
  have hcomm : ∀ x, π (psi A x) = pureGraphAction n K A (π x) := fun x => by
    rw [pureGraphAction_eq_onQuotient' A, CatalogueBFixedCentralQuotient.onQuotient_mk]
  have hQB : ∀ {F : Subgroup G₀}, IsComponent F → F ≤ commutator G₀ →
      CFSG.Assembly.IsComponentOf ((F.comap Θ).map B.subtype) B := by
    intro F hF hle
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le _)).2 ?_
    have hQQ : ((F.comap Θ).map B.subtype).subgroupOf B = F.comap Θ :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) _
    rw [hQQ]
    exact isComponent_comap_of_le Θ hΘ hF (hrange hle)
  have himg : ∀ {F : Subgroup G₀}, IsComponent F → F ≤ commutator G₀ →
      CFSG.Assembly.IsComponentOf (((F.comap Θ).map B.subtype).map π)
        (fixedSubgroup (pureGraphAction n K A)) := fun hF hle =>
    isComponentOf_map_fixed hπ hker ha hcomm (hQB hF hle)
  have hF₁ := himg h₁ hΩ₁
  have hF₂ := himg h₂ hΩ₂
  refine ⟨_, _, (isComponentOf_iff_isComponent_subgroupOf hF₁.1).1 hF₁,
    (isComponentOf_iff_isComponent_subgroupOf hF₂.1).1 hF₂, fun heq => hne ?_⟩
  have hR : ((F₁.comap Θ).map B.subtype).map π = ((F₂.comap Θ).map B.subtype).map π := by
    have := (Subgroup.subgroupOf_inj).1 heq
    rwa [inf_eq_left.2 hF₁.1, inf_eq_left.2 hF₂.1] at this
  have hQ : (F₁.comap Θ).map B.subtype = (F₂.comap Θ).map B.subtype :=
    calc (F₁.comap Θ).map B.subtype
        = ⁅((F₁.comap Θ).map B.subtype).map π |>.comap π,
            ((F₁.comap Θ).map B.subtype).map π |>.comap π⁆ :=
          (commutator_comap_map_eq hker (hQB h₁ hΩ₁).2.2).symm
      _ = ⁅((F₂.comap Θ).map B.subtype).map π |>.comap π,
            ((F₂.comap Θ).map B.subtype).map π |>.comap π⁆ := by rw [hR]
      _ = (F₂.comap Θ).map B.subtype := commutator_comap_map_eq hker (hQB h₂ hΩ₂).2.2
  have hcomap : F₁.comap Θ = F₂.comap Θ := Subgroup.map_injective (subtype_injective B) hQ
  calc F₁ = (F₁.comap Θ).map Θ := by rw [Subgroup.map_comap_eq, inf_eq_right.2 (hrange hΩ₁)]
    _ = (F₂.comap Θ).map Θ := by rw [hcomap]
    _ = F₂ := by rw [Subgroup.map_comap_eq, inf_eq_right.2 (hrange hΩ₂)]

theorem two_components_of_split {G₀ : Type} [Group G₀] {F₁ F₂ : Subgroup G₀}
    (hsup : commutator G₀ = F₁ ⊔ F₂) (hq₁ : IsQuasisimple F₁) (hq₂ : IsQuasisimple F₂)
    (hn₁ : (F₁.subgroupOf (commutator G₀)).Normal) (hn₂ : (F₂.subgroupOf (commutator G₀)).Normal)
    (hc : ∀ x ∈ F₁, ∀ y ∈ F₂, x * y = y * x) :
    IsComponent F₁ ∧ IsComponent F₂ ∧ F₁ ≠ F₂ ∧ F₁ ≤ commutator G₀ ∧ F₂ ≤ commutator G₀ := by
  have hle₁ : F₁ ≤ commutator G₀ := hsup ▸ le_sup_left
  have hle₂ : F₂ ≤ commutator G₀ := hsup ▸ le_sup_right
  have hD : (commutator G₀).IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
  refine ⟨⟨hq₁, Subgroup.IsSubnormal.step _ _ hle₁ hD hn₁⟩,
    ⟨hq₂, Subgroup.IsSubnormal.step _ _ hle₂ hD hn₂⟩, fun heq => ?_, hle₁, hle₂⟩
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_isQuasisimple hq₁ (MulEquiv.refl ↥F₁)
  exact hab (Subtype.ext (hc a a.2 b (heq ▸ b.2)))

theorem centerQuotient_map_equiv' {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (N : Subgroup G) :
    Nonempty (↥N ⧸ center ↥N ≃* ↥(N.map e.toMonoidHom) ⧸ center ↥(N.map e.toMonoidHom)) :=
  ⟨QuotientGroup.congr _ _ (N.equivMapOfInjective e.toMonoidHom e.injective)
    (Subgroup.map_center_eq _)⟩

theorem a5_pureGraph_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5)
    (A : GL (Fin 4) K) (hord : orderOf (pureGraphAction 4 K A) = 2)
    {L : Subgroup ↥(fixedSubgroup (pureGraphAction 4 K A))} (hL : IsComponent L)
    (hA5 : Nonempty (↥L ⧸ center ↥L ≃* alternatingGroup (Fin 5)))
    (hu : ∀ L' : Subgroup ↥(fixedSubgroup (pureGraphAction 4 K A)), IsComponent L' → L' = L) :
    False := by
  have hK1 : Nat.card K = 5 ^ 1 := by simpa using hK
  have hcharP : CharP K 5 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_five
      le_rfl hK1
  have hodd : ringChar K ≠ 2 := by
    rw [ringChar.eq K 5]
    norm_num
  have hsq2 : pureGraphAction 4 K A ^ 2 = 1 := by rw [← hord, pow_orderOf_eq_one]
  have hform := CatalogueBGraphForm.pureGraph_involution_form_data 4 K (by norm_num) hodd A hsq2
  obtain ⟨N, hN, ⟨eLN⟩⟩ := pureGraph_component_transfer A hL
  have hNA : Nonempty (↥N ⧸ center ↥N ≃* alternatingGroup (Fin 5)) := ⟨eLN.symm.trans hA5.some⟩
  have hdim : Module.finrank K (Fin 4 → K) = 4 := by rw [Module.finrank_fin_fun]
  rcases hform with hsymm | ⟨halt, -⟩
  ·
    have hR := transpose_inv_of_transpose_eq A hsymm
    have hQ₀ : (matrixQuadraticForm A⁻¹).polarBilin.Nondegenerate :=
      polarBilin_matrixQuadraticForm_nondegenerate hodd A⁻¹ hR
    let e₁ : ↥(isometryGroup 4 K A⁻¹) ≃*
        ↥(TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹)) :=
      (isometryGroupEquiv A⁻¹).symm.trans
        (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd A⁻¹ hR).symm)
    have hN₀ : IsComponent (N.map e₁.toMonoidHom) := LocalCores.isComponent_map_mulEquiv e₁ hN
    have hNA₀ : Nonempty (↥(N.map e₁.toMonoidHom) ⧸ center ↥(N.map e₁.toMonoidHom) ≃*
        alternatingGroup (Fin 5)) := ⟨(centerQuotient_map_equiv' e₁ N).some.symm.trans hNA.some⟩
    by_cases hS : ∃ S : Submodule K (Fin 4 → K), Module.finrank K S = 2 ∧
        ∀ x ∈ S, matrixQuadraticForm A⁻¹ x = 0
    ·
      have hK2 : Nat.card K ≠ 2 := by rw [hK]; norm_num
      have hK3 : Nat.card K ≠ 3 := by rw [hK]; norm_num
      obtain ⟨ψ, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, hcomm, -, -⟩ :=
        LocalAnalysis.ComponentInitial.orthogonal_split_four_derived hK2 hK3
          (matrixQuadraticForm A⁻¹) hQ₀ hdim hS
      obtain ⟨hc₁, hc₂, hne, hle₁, hle₂⟩ := two_components_of_split hsup hq₁ hq₂ hn₁ hn₂ hcomm
      obtain ⟨L₁, L₂, hL₁, hL₂, hne'⟩ := pg_two_components (by norm_num) A hsq2 e₁ hc₁ hc₂ hne hle₁
        hle₂
      exact hne' ((hu L₁ hL₁).trans (hu L₂ hL₂).symm)
    ·
      have hmodel := X10Lin.centralModel_orthogonal_nonsplit_four Nat.prime_five
        (by norm_num : (5 : ℕ) ≠ 2) (by norm_num : 1 ≤ 1) hK1 (matrixQuadraticForm A⁻¹) hQ₀ hdim hS
        hN₀
      obtain ⟨-, -, he⟩ := eq_psl_two_one_of_a5 (Or.inl rfl) hmodel.1 hmodel.2 hNA₀
      omega
  ·
    have hR := transpose_inv_of_transpose_eq_neg A halt
    let eI := isometryGroupEquiv A⁻¹
    have hN' : IsComponent (N.map eI.symm.toMonoidHom) :=
      LocalCores.isComponent_map_mulEquiv eI.symm hN
    have hNA' : Nonempty (↥(N.map eI.symm.toMonoidHom) ⧸ center ↥(N.map eI.symm.toMonoidHom) ≃*
        alternatingGroup (Fin 5)) :=
      ⟨(centerQuotient_map_equiv' eI.symm N).some.symm.trans hNA.some⟩
    have hmodel := X10Sp.centralModel_isometryGroup_component (ℓ := 5) (j := 1) (m := 2)
      Nat.prime_five (by norm_num : (5 : ℕ) ≠ 2) (by norm_num : 1 ≤ 1) hK1 (matrixForm A⁻¹)
      (matrixForm_isAlt hodd A⁻¹ hR) (matrixForm_nondegenerate A⁻¹)
      (by rw [Module.finrank_fin_fun]) le_rfl hN'
    obtain ⟨h, -⟩ := eq_psl_two_one_of_a5 (Or.inr (Or.inr (Or.inl rfl))) hmodel.1 hmodel.2 hNA'
    exact absurd h (by decide)

end CFSG.ComponentClassification.SolMax.FiveCat.C5PSL
