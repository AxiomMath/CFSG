module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClLinCore
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRow
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClBarIso

public section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (gramSU)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormP primeFormUnitary
  primeFormConjHom primeFormConjAut primeFormConjSU primeFormConjAut_mk mem_gramSU_iff_unitary)

theorem primeFormConjHom_gramSU_apply {n p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {C : Matrix (Fin n) (Fin n) K} (g : gramSU h C)
    (x : primeFormP h C) :
    primeFormConjHom h C ⟨(g : GL (Fin n) K), ((mem_gramSU_iff_unitary h).1 g.2).1⟩ x =
      (g : primeFormP h C) * x * (g : primeFormP h C)⁻¹ := by
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective x
  have hconj : primeFormConjSU h C ⟨(g : GL (Fin n) K), ((mem_gramSU_iff_unitary h).1 g.2).1⟩
      g' = g * g' * g⁻¹ := Subtype.ext rfl
  change primeFormConjAut h C _ (g' : primeFormP h C) = _
  rw [primeFormConjAut_mk, hconj, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv]

theorem false_of_barConfig_psu {P : Type} [Group P] [Finite P] {n p f f₀ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (_h5 : 5 ≤ p ^ f)
    (hP : StatedClassicalModel P .PSU n p f₀) (h : BarConfig P p f p f) : False := by
  have hadm : StatedLieAdmissible .PSU n p f₀ := hP.1
  have hn : 3 ≤ n := hadm.2.2.1
  have hf₀ : 1 ≤ f₀ := hadm.2.1
  have hLM : LieModel P .PSU n p f₀ := Or.inl ⟨by decide, hP⟩
  have : IsSimpleGroup P := (ClassicalGroups.Unitary.fam_PSU_simplicity P n p f₀ hP).2
  have h4 := four_mul_le_factorization_of_barConfig hp2 h
  have hfac := (CatLeafProof.X10Lin.lieOrder_of_lieModel_classical (Or.inr (Or.inl rfl)) hp2
    (by omega) hLM).2
  obtain ⟨K, _, hU, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel' hadm hLM
  have : Finite (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv _ e.toEquiv
  have : IsSimpleGroup (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    e.symm.isSimpleGroup
  have h' := BarConfig.of_mulEquiv e h
  have hQ : FixedTwoComponentsQuasisimple
      (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    FixedTwoComponentsQuasisimple.of_mulEquiv e.symm
      (CatLeafProof.X10Lin.fixedTwoComponentsQuasisimple_lin hp2 (Or.inr rfl) hadm hLM)
  obtain ⟨t, -, -, hJ⟩ := exists_component_of_barConfig hQ (center_eq_bot_of_barConfig h') h'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
  obtain ⟨hA, J', hJ'c, hJ'z, hJ'm⟩ := hJ _ (primeFormConjHom_gramSU_apply hU g)
  rcases CatLeafProof.X10Lin.inner_psu_component_cases hU hp2 hadm _ hA hJ'c with
    ⟨z, hz, hzc, hzz, hz1⟩ | ⟨t', k, e', hT, hcm⟩
  · exact hz1 (hJ'z z hz hzc hzz)
  · rcases hT with ⟨k', hk3, -, hk⟩ | ⟨⟨r, hr⟩, hk⟩
    ·
      simp only [Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      obtain ⟨ht, -, -⟩ :=
        eq_of_centralModel_of_lieModel hp hp2 hf hJ'm (Or.inr (Or.inl rfl)) hcm
      exact absurd ht (by decide)
    ·
      simp only [Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      obtain ⟨-, hk2, he⟩ := eq_of_centralModel_of_lieModel hp hp2 hf hJ'm (Or.inl rfl) hcm
      have hn4 : n = 4 := by omega
      subst hn4
      have hS : lieSylowExponent .PSU 4 = 6 := rfl
      rw [hfac, hS] at h4
      omega

end CFSG.ComponentClassification.GSThmB.QPUCl
