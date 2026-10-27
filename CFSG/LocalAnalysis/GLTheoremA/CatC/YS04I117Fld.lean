module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117F
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D4FCore

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.RankThree.PartOne (SubfieldConclusion)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (IsExtension fieldAutT fieldPair
  subfieldDerivedImage coordinateQuadPlus_fieldAut coordinateQuadPlus_isExtension incl fieldAutT_fixes_J)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Timmesfeld.DFour
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance (isElemAbelian_of_forall)
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem isElemAbelian_map_inj {A B : Type} [Group A] [Group B] {p : ℕ} (f : A →* B)
    {E : Subgroup A} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine isElemAbelian_of_forall ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, isElemAbelian_commute hE hx hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]

theorem d4FieldFour_of (h2 : D4FourRank) : D4FieldFour := by
  intro K _ _ r f hr hr2 hr3 hK y hyE hyI hy3
  have hf : 1 ≤ f := one_le_of_card_field hK
  let e0 : D4Model K ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm
  have hm : StatedClassicalModel (D4Model K) .POmegaPlus 4 r f :=
    ⟨⟨hr, hf, le_refl 4⟩, K, inferInstance, inferInstance, hK, ⟨e0⟩⟩
  obtain ⟨hQ, hab, hidx⟩ := coordinate_facts_four hm K hK e0
  have hQv := exists_nonzero_value (coordinateQuadPlus 4 K) hQ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy1 : y ≠ 1 := fun h => hyI (h ▸ (Inn (D4Model K)).one_mem)
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hnotlin : y ∉ (linearConjugationHom (coordinateQuadPlus 4 K)).range := fun hL =>
    hyI (mem_inner_of_mem_linearRange (coordinateQuadPlus 4 K) hQv hab Nat.prime_three
      (by norm_num) hL hy3)
  have hφ : coordinatePlusWitnessEquiv K e0 = MulEquiv.refl (D4Model K) := by
    ext x
    exact MulEquiv.apply_symm_apply _ x
  have hcy : MulAut.congr (coordinatePlusWitnessEquiv K e0) y = y := by
    rw [hφ]
    ext x
    rfl
  have hdesc := CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
    (D4Model K) .POmegaPlus (Or.inr (Or.inl rfl)) 4 r f 3 hm Nat.prime_three (by norm_num) K hK e0
    (MulAut.congr (coordinatePlusWitnessEquiv K e0) y) (by rw [hcy]; exact hyE)
    (by rw [hcy]; exact hnotlin) (by rw [hcy]; exact hord)
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨g, hg⟩ : y ∈ D4Img K := hyE
  have hrr := hrest g.val.right ⟨g, by rw [hcy]; exact hg, rfl⟩
  obtain ⟨hord', hcardσ, U, _, _, hUκ, hUr, _, hDisp⟩ := hrr
  obtain ⟨ν, S₀, -, -, hT⟩ := hDisp
  obtain ⟨S', ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hordσ : orderOf U.val.right = 3 := by rw [hUr]; exact hord'
  have hcardk : Nat.card (semilinearFixedSubfield U.val.right) = r ^ (f / 3) := by
    rw [hUr]; exact hcardσ
  have hK' : Nat.card K = r ^ (f / 3 * 3) := by rw [Nat.div_mul_cancel hpf]; exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  have hadm : StatedLieAdmissible .POmegaPlus 4 r (f / 3) :=
    ⟨hr, Nat.div_pos (Nat.le_of_dvd hf hpf) (by norm_num), le_rfl⟩
  obtain ⟨⟨hinj, -, -⟩, -⟩ := (orthPlus_subfield_any hadm Nat.prime_three (by norm_num) K
    (semilinearFixedSubfield U.val.right) hcardk hK' U.val.right hordσ hσk).2
  have hΘy := d4_congr_eq_fieldAutT (coordinatePlusWitnessEquiv K e0) Θ y U hUκ g' hg'l hg'r hΘ
    (coordinateQuadPlus_fieldAut 4 U.val.right)
  set k := semilinearFixedSubfield U.val.right with hk
  set ψ : D4Model K ≃* D4Model K := (coordinatePlusWitnessEquiv K e0).trans Θ with hψ
  set χ := fieldAutT (coordinateQuadPlus 4 K) U.val.right
    (coordinateQuadPlus_fieldAut 4 U.val.right) with hχ
  have hψy : ∀ s : D4Model K, ψ (y s) = χ (ψ s) := by
    intro s
    rw [← hΘy]
    change ψ (y s) = ψ (y (ψ.symm (ψ s)))
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨F₀, z₀, hF₀, hF₀c, hz₀2, hz₀1, hFz₀⟩ := h2 ↥k r (f / 3) hr hr2 hr3 hcardk
  have hext := coordinateQuadPlus_isExtension k 4
  set ι₁ := incl k hext with hι₁
  have hfixJ : ∀ t ∈ (incl k hext).range, χ t = t := fun t ht =>
    fieldAutT_fixes_J k (coordinateQuadPlus 4 K) U.val.right (coordinateQuadPlus_fieldAut 4 U.val.right)
      hext hσk ht
  have hz₁ : χ (ι₁ z₀) = ι₁ z₀ := hfixJ _ ⟨z₀, rfl⟩
  refine ⟨(F₀.map ι₁).map ψ.symm.toMonoidHom, ψ.symm (ι₁ z₀),
    isElemAbelian_map_equiv ψ.symm (isElemAbelian_map_inj ι₁ hF₀), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective ψ.symm.injective, Subgroup.card_map_of_injective hinj]
    exact hF₀c
  · rw [← map_pow, ← map_pow, hz₀2, map_one, map_one]
  · intro h
    apply hz₀1
    apply hinj
    apply ψ.symm.injective
    rw [h, map_one, map_one]
  · rintro _ ⟨_, ⟨s₀, hs₀, rfl⟩, rfl⟩
    change ψ.symm (ι₁ s₀) * ψ.symm (ι₁ z₀) = ψ.symm (ι₁ z₀) * ψ.symm (ι₁ s₀)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hFz₀ s₀ hs₀]
  · apply ψ.injective
    rw [hψy, MulEquiv.apply_symm_apply, hz₁]
  · rintro _ ⟨_, ⟨s₀, hs₀, rfl⟩, rfl⟩
    change y (ψ.symm (ι₁ s₀)) = ψ.symm (ι₁ s₀)
    apply ψ.injective
    rw [hψy, MulEquiv.apply_symm_apply]
    exact hfixJ _ ⟨s₀, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA
