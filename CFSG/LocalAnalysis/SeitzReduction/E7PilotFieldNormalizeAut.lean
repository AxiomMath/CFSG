module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp

public section

namespace CFSG.SeitzReduction.E7Pilot

open Matrix QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

section Form

variable {K : Type} [Field K] (n : ℕ)

theorem isExtension_coordinateQuadPlus (k : Subfield K) :
    IsExtension k (coordinateQuadPlus n k) (coordinateQuadPlus n K) := by
  intro v
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply]
  simp [vecIncl]

theorem coordinateQuadPlus_fieldMap (ρ : K ≃+* K) (v : Fin (2 * n) → K) :
    coordinateQuadPlus n K (coordinateFieldMap (2 * n) ρ v) = ρ (coordinateQuadPlus n K v) := by
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply, map_sum]
  simp only [coordinateFieldMap_apply, map_mul]

end Form

theorem commutator_top_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ with
    h1 | h1
  · obtain ⟨a, b, hab⟩ := h
    exfalso
    apply hab
    have h2 : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h1, Subgroup.mem_bot] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  · exact h1

theorem commutator_range_of_commutator_top {G H : Type*} [Group G] [Group H] (f : G →* H)
    (h : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) : ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]

section Fixed

open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (matrixLinearEquiv_scalar)

variable {K : Type} [Field K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

theorem commutator_subfieldFixedGroup_le (hext : IsExtension k Q₀ Q) :
    ⁅subfieldFixedGroup k Q₀ Q, subfieldFixedGroup k Q₀ Q⁆ ≤ subfieldDerivedImage k hext := by
  rw [Subgroup.commutator_le]
  rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
  obtain ⟨a, ha, hay⟩ : ∃ a ∈ matrixIsometries Q₀, glIncl k a = y.val := hy
  obtain ⟨b, hb, hbz⟩ : ∃ b ∈ matrixIsometries Q₀, glIncl k b = z.val := hz
  have hab : ⁅a, b⁆ ∈ matrixDerived Q₀ := Subgroup.commutator_mem_commutator ha hb
  refine ⟨matrixProjectiveProjection Q₀ ⟨_, hab⟩, ?_⟩
  rw [incl_mk, ← map_commutatorElement]
  congr 1
  apply Subtype.ext
  rw [inclHom_val]
  change glIncl k ⁅a, b⁆ = ⁅y.val, z.val⁆
  rw [map_commutatorElement, hay, hbz]

variable [CharP K 2] {σ : K ≃+* K} (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))

theorem fixedSubgroup_fieldAutT_le (hσk : ∀ x, x ∈ k ↔ σ x = x) (hext : IsExtension k Q₀ Q)
    (hQne : ∃ v, Q v ≠ 0) :
    fixedSubgroup (fieldAutT Q σ hQσ) ≤ subfieldFixedGroup k Q₀ Q := by
  intro t ht
  have h : fieldAutT Q σ hQσ t = t := ht
  obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective Q t
  rw [fieldAutT_mk] at h
  set w := matrixDerivedConjugation Q (fieldPair Q σ hQσ) y with hw
  have hwv : (w : GL (Fin d) K) = glFieldAut (Fin d) K σ y.val :=
    matrixDerivedConjugation_fieldPair_val Q σ hQσ y
  have h1 : y⁻¹ * w ∈ matrixDerivedScalars Q := by
    rw [matrixProjectiveProjection, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h
    exact QuotientGroup.eq.mp h.symm
  obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q _).mp h1
  have hc' : (GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) = y.val⁻¹ * w.val := hc
  have hiso : GeneralLinearGroup.scalar (Fin d) c ∈ matrixIsometries Q := by
    rw [hc']
    exact mul_mem (inv_mem (matrixDerived_le_isometries Q y.2))
      (matrixDerived_le_isometries Q w.2)
  obtain ⟨v, hv⟩ := hQne
  have hc2 : (c : K) * c = 1 := by
    have h2 := (mem_matrixIsometries_iff Q _).mp hiso v
    rw [matrixLinearEquiv_scalar, QuadraticMap.map_smul, smul_eq_mul] at h2
    exact mul_right_cancel₀ hv (by rw [one_mul]; exact h2)
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc1 : (c : K) = 1 := by
    have h3 : ((c : K) + 1) * ((c : K) + 1) = 0 := by
      linear_combination hc2 + ((c : K) + 1) * h22
    have h4 : (c : K) + 1 = 0 := mul_self_eq_zero.mp h3
    linear_combination h4 - h22
  have hcu : c = 1 := Units.ext hc1
  have hfix : glFieldAut (Fin d) K σ y.val = y.val := by
    rw [← hwv]
    rw [hcu, map_one] at hc'
    exact (inv_mul_eq_one.mp hc'.symm).symm
  obtain ⟨x, hx⟩ := exists_glIncl_of_fixed k hσk hfix
  exact ⟨y, ⟨x, mem_isometries_of_glIncl k hext (hx ▸ matrixDerived_le_isometries Q y.2), hx⟩,
    rfl⟩

theorem perfectCore_fixedSubgroup_fieldAutT (hσk : ∀ x, x ∈ k ↔ σ x = x)
    (hext : IsExtension k Q₀ Q) (hQne : ∃ v, Q v ≠ 0)
    (hJ : ⁅subfieldDerivedImage k hext, subfieldDerivedImage k hext⁆ =
      subfieldDerivedImage k hext) :
    perfectCore (fixedSubgroup (fieldAutT Q σ hQσ)) = subfieldDerivedImage k hext := by
  apply le_antisymm
  · calc perfectCore (fixedSubgroup (fieldAutT Q σ hQσ))
        ≤ perfectCore (subfieldFixedGroup k Q₀ Q) :=
          CFSG.Quasithin.perfectCore_mono (fixedSubgroup_fieldAutT_le hQσ hσk hext hQne)
      _ ≤ CFSG.Quasithin.derivedSeriesOf (subfieldFixedGroup k Q₀ Q) 1 :=
          CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1
      _ ≤ subfieldDerivedImage k hext := commutator_subfieldFixedGroup_le hext
  · exact CFSG.Quasithin.le_perfectCore_of_perfect
      (fun t ht => fieldAutT_fixes_J k Q σ hQσ hext hσk ht) hJ

end Fixed

section Extension

variable {K : Type} [Field K] {k : Subfield K} {n : ℕ}

theorem coordinateQuadPlus_glIncl {A : GL (Fin (2 * n)) k} {μ : k}
    (hA : ∀ u, coordinateQuadPlus n k (A.val *ᵥ u) = μ * coordinateQuadPlus n k u)
    (w : Fin (2 * n) → K) :
    coordinateQuadPlus n K ((glIncl k A).val *ᵥ w) = (μ : K) * coordinateQuadPlus n K w := by
  have hext := isExtension_coordinateQuadPlus n k
  have h := eq_of_agree k
    ((coordinateQuadPlus n K).comp (matrixLinearEquiv (glIncl k A)).toLinearMap)
    ((μ : K) • coordinateQuadPlus n K) (fun v => by
      rw [QuadraticMap.comp_apply, _root_.smul_apply]
      change coordinateQuadPlus n K (matrixLinearEquiv (glIncl k A) (vecIncl k v)) = _
      rw [matrixLinearEquiv_apply, mulVec_vecIncl, hext, hext, hA, smul_eq_mul,
        Subfield.coe_mul])
  have h1 := congrArg (fun F : QuadraticForm K (Fin (2 * n) → K) => F w) h
  simp only [QuadraticMap.comp_apply, _root_.smul_apply, smul_eq_mul] at h1
  exact h1

variable [Finite K] [CharP K 2]

theorem exists_mulAut_incl_comm (hn : 5 ≤ n)
    (δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n k))) :
    ∃ δ' : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)),
      ∀ x, δ' (incl k (isExtension_coordinateQuadPlus n k) x) =
        incl k (isExtension_coordinateQuadPlus n k) (δ x) := by
  have himage := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus k n hn
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff _ δ).mp (himage ▸ Subgroup.mem_top δ)
  obtain ⟨ρ', hρ'⟩ := F4Pilot.exists_ringEquiv_comp_eq k.subtype g.val.right
  obtain ⟨μ, hμ⟩ := g.property
  have hA : ∀ u, coordinateQuadPlus n k (g.val.left.val *ᵥ u) =
      (μ : k) * coordinateQuadPlus n k u := by
    intro u
    have h1 := hμ (coordinateFieldMap (2 * n) g.val.right.symm u)
    rw [coordinateSemilinearMap_apply, ← coordinateQuadPlus_fieldMap] at h1
    have hu : coordinateFieldMap (2 * n) g.val.right
        (coordinateFieldMap (2 * n) g.val.right.symm u) = u := by
      funext i
      simp only [coordinateFieldMap_apply, RingEquiv.apply_symm_apply]
    have hu' : (fun i => g.val.right (coordinateFieldMap (2 * n) g.val.right.symm u i)) = u := by
      funext i
      simp only [coordinateFieldMap_apply, RingEquiv.apply_symm_apply]
    rw [hu, hu'] at h1
    exact h1
  let g' : coordinateSemilinearGroup (2 * n) K := ⟨glIncl k g.val.left, ρ'⟩
  have hg' : g' ∈ similarityPairs (coordinateQuadPlus n K) := by
    refine ⟨Units.map k.subtype.toMonoidHom μ, fun w => ?_⟩
    rw [coordinateSemilinearMap_apply]
    change coordinateQuadPlus n K ((glIncl k g.val.left).val *ᵥ fun i => ρ' (w i)) =
      ((μ : k) : K) * ρ' (coordinateQuadPlus n K w)
    rw [coordinateQuadPlus_glIncl hA, ← coordinateQuadPlus_fieldMap]
    rfl
  refine ⟨matrixProjectiveConjugation _ ⟨g', hg'⟩, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective _ x
  rw [← hg, matrixProjectiveConjugation_mk, incl_mk, incl_mk, matrixProjectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  rw [matrixDerivedConjugation_val, inclHom_val, inclHom_val, matrixDerivedConjugation_val]
  have hent : glFieldAut (Fin (2 * n)) K ρ' (glIncl k y.val) =
      glIncl k (glFieldAut (Fin (2 * n)) k g.val.right y.val) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change ρ' (k.subtype (y.val.val i j)) = k.subtype (g.val.right (y.val.val i j))
    exact hρ' _
  change glIncl k g.val.left * glFieldAut (Fin (2 * n)) K ρ' (glIncl k y.val) *
      (glIncl k g.val.left)⁻¹ = _
  rw [hent, map_mul, map_mul, map_inv]

end Extension

end CFSG.SeitzReduction.E7Pilot
