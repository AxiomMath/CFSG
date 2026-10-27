module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9Core
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9InnerTransfer
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescProof

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD
open CFSG.StandardType.Line63.H5 CFSG.SectionRank.OddCover
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K] {n d : ℕ}

private theorem map_ggFix_conjProj_eq (h : UnitaryFieldData 2 n K) {P M D : GL (Fin d) K}
    (hP : P ∈ primeFormUnitary h (idGram K d))
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hMP : P⁻¹ * M * P = D) :
    (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨M, hM⟩)).map
        (conjProj h P hP).toMonoidHom =
      ggFix (TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩) := by
  have hM' : P⁻¹ * M * P ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := hMP ▸ hD
  have hσ : conjProj h P hP * TableB.projConj (unitarySU 2 n K d) ⟨M, hM⟩ *
        (conjProj h P hP)⁻¹ =
      TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩ := by
    ext r
    have h := conjProj_projConj (d := d) h P hP ⟨M, hM⟩ hM' ((conjProj h P hP)⁻¹ r)
    have hsub : (⟨P⁻¹ * M * P, hM'⟩ :
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) = ⟨D, hD⟩ :=
      Subtype.ext hMP
    rw [hsub] at h
    simpa using h
  have h := map_ggFix_conj (conjProj h P hP)⁻¹
    (TableB.projConj (unitarySU 2 n K d) ⟨M, hM⟩)
  rw [inv_inv, hσ] at h
  exact h

private theorem largeEvenLayer_ggFix_conjProj_eq (h : UnitaryFieldData 2 n K)
    {P M D : GL (Fin d) K} (hP : P ∈ primeFormUnitary h (idGram K d))
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (hMP : P⁻¹ * M * P = D) :
    LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩)) =
      (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨M, hM⟩))).map
        (conjProj h P hP).toMonoidHom := by
  rw [← map_ggFix_conjProj_eq h hP hM hD hMP]
  exact largeEvenLayer_map_of_injective _ (conjProj h P hP).injective _

private theorem pow_three_of_diagHom_pow_three {τ : Fin d → Kˣ}
    (h : diagHom d τ ^ 3 = 1) : ∀ i, τ i ^ 3 = 1 := by
  have hpow : τ ^ 3 = 1 := by
    apply diagHom_injective d
    rwa [map_pow, h, map_one]
  exact fun i => congrFun hpow i

private theorem conj_commutator_mem_scalars {P M N D : GL (Fin d) K}
    (hMP : P⁻¹ * M * P = D)
    (hcomm : N * M * N⁻¹ * M⁻¹ ∈ LargeEvenScalars (Fin d) K) :
    (P⁻¹ * N * P) * D * (P⁻¹ * N * P)⁻¹ * D⁻¹ ∈ LargeEvenScalars (Fin d) K := by
  have hconj : P⁻¹ * (N * M * N⁻¹ * M⁻¹) * P ∈ LargeEvenScalars (Fin d) K :=
    (LargeEvenScalars.normal (ι := Fin d) (K := K)).conj_mem _ hcomm P⁻¹
  have heq : (P⁻¹ * N * P) * D * (P⁻¹ * N * P)⁻¹ * D⁻¹ =
      P⁻¹ * (N * M * N⁻¹ * M⁻¹) * P := by
    rw [← hMP]
    group
  rwa [heq]

theorem u6Type9LayerInner_holds : U6Type9LayerInner := by
  intro n K _ _ h hpq M N hMgu hNgu hMN hNN hM3 hMscal hcomm hcomp
  classical
  obtain ⟨P, hP, τ, hMP, v, hv⟩ :=
    exists_level_four_or_five_of_isComponent h hpq hMgu hMN hM3 hMscal hcomp
  set D : GL (Fin 6) K := diagHom 6 τ with hDdef
  have hPN : P ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    SUTorus.mem_normalizer_of_mem_primeFormUnitary h hP
  have hD : D ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) := by
    rw [← hMP]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) hMN) hPN
  have hD3 : D ^ 3 = 1 := by
    rw [← hMP]
    have hconj : (P⁻¹ * M * P) ^ 3 = P⁻¹ * M ^ 3 * P := by
      simpa using (conj_pow (a := P⁻¹) (b := M) (i := 3))
    rw [hconj, hM3]
    simp
  have hτ3 : ∀ i : Fin 6, τ i ^ 3 = 1 := by
    apply pow_three_of_diagHom_pow_three
    rwa [hDdef] at hD3
  have hNgu' : P⁻¹ * N * P ∈ LargeEvenGUSet (Fin 6) K (2 ^ n) :=
    conj_mem_guSet_of_mem_primeFormUnitary h hP hNgu
  have hN'N : P⁻¹ * N * P ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) hNN) hPN
  have hcomm' : (P⁻¹ * N * P) * D * (P⁻¹ * N * P)⁻¹ * D⁻¹ ∈
      LargeEvenScalars (Fin 6) K :=
    conj_commutator_mem_scalars (d := 6) hMP hcomm
  have hcompD : IsComponentOf
      (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨D, hD⟩)))
      (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨D, hD⟩)) := by
    by_contra hcon
    exact (not_isComponentOf_layer_ggFix_of_conj h hMN hP hMP hD hcon) hcomp
  have hS : ∀ i : Fin 6, i ∈ fiber τ v ↔ τ i = v := fun i => by simp [fiber]
  obtain ⟨g', hg'SU, hg'layer, hg'act⟩ :=
    u6Type9LayerInner_diag h hpq hτ3 hD hS hv hNgu' hN'N hcomm' hcompD
  let g'SU : ↥(unitarySU 2 n K 6) := ⟨g', hg'SU⟩
  have hPinv : P⁻¹ ∈ primeFormUnitary h (idGram K 6) :=
    (primeFormUnitary h (idGram K 6)).inv_mem hP
  have hg : (P * (g' : GL (Fin 6) K) * P⁻¹) ∈ unitarySU 2 n K 6 := by
    have h := (conjSU h P⁻¹ hPinv g'SU).2
    rwa [coe_conjSU, inv_inv] at h
  have hlayer := largeEvenLayer_ggFix_conjProj_eq (d := 6) h hP hMN hD hMP
  have hσg : conjProj h P hP
      (LargeEvenProjMk (unitarySU 2 n K 6)
        ⟨P * (g' : GL (Fin 6) K) * P⁻¹, hg⟩) =
      LargeEvenProjMk (unitarySU 2 n K 6) g'SU := by
    rw [conjProj_mk]
    congr 1
    apply Subtype.ext
    rw [coe_conjSU]
    show P⁻¹ * (P * (g' : GL (Fin 6) K) * P⁻¹) * P = (g' : GL (Fin 6) K)
    group
  have hgmem : LargeEvenProjMk (unitarySU 2 n K 6)
      ⟨P * (g' : GL (Fin 6) K) * P⁻¹, hg⟩ ∈
      LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩)) := by
    have hmem : LargeEvenProjMk (unitarySU 2 n K 6) g'SU ∈
        LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨D, hD⟩)) :=
      hg'layer
    rw [hlayer] at hmem
    obtain ⟨y, hy, hyσ⟩ := Subgroup.mem_map.mp hmem
    have hyσ' : (conjProj h P hP) y =
        LargeEvenProjMk (unitarySU 2 n K 6) g'SU := hyσ
    have hyx : y = LargeEvenProjMk (unitarySU 2 n K 6)
        ⟨P * (g' : GL (Fin 6) K) * P⁻¹, hg⟩ := by
      apply (conjProj h P hP).injective
      rw [hyσ', hσg]
    rwa [hyx] at hy
  refine ⟨P * (g' : GL (Fin 6) K) * P⁻¹, hg, hgmem, ?_⟩
  intro t ht
  apply (conjProj h P hP).injective
  have hNapply := conjProj_projConj (d := 6) h P hP ⟨N, hNN⟩ hN'N t
  have hGapply : conjProj h P hP
      (TableB.projConj (unitarySU 2 n K 6)
        ⟨P * (g' : GL (Fin 6) K) * P⁻¹, Subgroup.le_normalizer hg⟩ t) =
      TableB.projConj (unitarySU 2 n K 6)
        ⟨(g' : GL (Fin 6) K), Subgroup.le_normalizer hg'SU⟩
        (conjProj h P hP t) := by
    have heq : P⁻¹ * (P * (g' : GL (Fin 6) K) * P⁻¹) * P = (g' : GL (Fin 6) K) := by
      group
    have hM' : P⁻¹ * (P * (g' : GL (Fin 6) K) * P⁻¹) * P ∈
        Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) := by
      rw [heq]
      exact Subgroup.le_normalizer hg'SU
    have h := conjProj_projConj (d := 6) h P hP
      ⟨P * (g' : GL (Fin 6) K) * P⁻¹, Subgroup.le_normalizer hg⟩ hM' t
    have hsub : (⟨P⁻¹ * (P * (g' : GL (Fin 6) K) * P⁻¹) * P, hM'⟩ :
        Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) =
        ⟨(g' : GL (Fin 6) K), Subgroup.le_normalizer hg'SU⟩ :=
      Subtype.ext heq
    rwa [hsub] at h
  rw [hNapply, hGapply]
  refine hg'act (conjProj h P hP t) ?_
  rw [hlayer]
  exact Subgroup.mem_map_of_mem _ ht

section Certificates


theorem u6Type9_holds : U6Type9 :=
  u6Type9_of_descent_of_layerInner componentDescent_holds u6Type9LayerInner_holds

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
