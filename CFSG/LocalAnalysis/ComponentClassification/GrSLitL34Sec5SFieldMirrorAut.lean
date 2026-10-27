module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInvolutionCentralizerSolvable
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSL
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.StandardType.AutPSL in
private theorem compl_comm {F : Type} [Field F] [Finite F] [CharP F 2]
    {c c' : MulAut (projectiveSL 3 F)}
    (hc : c ∈ compl (n := 3) (K := F)) (hc' : c' ∈ compl (n := 3) (K := F)) :
    c * c' = c' * c := by
  obtain ⟨σ, hσ⟩ := mem_compl.mp hc
  obtain ⟨τ, hτ⟩ := mem_compl.mp hc'
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
  · rw [← map_mul, ← map_mul,
      CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm F σ τ]
  · calc
      fieldAut 3 F σ * (fieldAut 3 F τ * graphAut) =
          (fieldAut 3 F σ * fieldAut 3 F τ) * graphAut := by group
      _ = (fieldAut 3 F τ * fieldAut 3 F σ) * graphAut := by
            rw [← map_mul, ← map_mul,
              CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm F σ τ]
      _ = fieldAut 3 F τ * (fieldAut 3 F σ * graphAut) := by group
      _ = fieldAut 3 F τ * (graphAut * fieldAut 3 F σ) := by
            rw [fieldAut_mul_graphAut σ]
      _ = (fieldAut 3 F τ * graphAut) * fieldAut 3 F σ := by group
  · calc
      (fieldAut 3 F σ * graphAut) * fieldAut 3 F τ =
          fieldAut 3 F σ * (graphAut * fieldAut 3 F τ) := by group
      _ = fieldAut 3 F σ * (fieldAut 3 F τ * graphAut) := by
            rw [← fieldAut_mul_graphAut τ]
      _ = (fieldAut 3 F σ * fieldAut 3 F τ) * graphAut := by group
      _ = (fieldAut 3 F τ * fieldAut 3 F σ) * graphAut := by
            rw [← map_mul, ← map_mul,
              CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm F σ τ]
      _ = fieldAut 3 F τ * (fieldAut 3 F σ * graphAut) := by group
  · calc
      (fieldAut 3 F σ * graphAut) * (fieldAut 3 F τ * graphAut) =
          fieldAut 3 F σ * (graphAut * fieldAut 3 F τ) * graphAut := by group
      _ = fieldAut 3 F σ * (fieldAut 3 F τ * graphAut) * graphAut := by
            rw [← fieldAut_mul_graphAut τ]
      _ = fieldAut 3 F σ * fieldAut 3 F τ * (graphAut * graphAut) := by group
      _ = fieldAut 3 F σ * fieldAut 3 F τ * 1 := by rw [graphAut_mul_self]
      _ = fieldAut 3 F σ * fieldAut 3 F τ := by rw [mul_one]
      _ = fieldAut 3 F τ * fieldAut 3 F σ := by
            rw [← map_mul, ← map_mul,
              CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm F σ τ]
      _ = fieldAut 3 F τ * (graphAut * graphAut) * fieldAut 3 F σ := by
            rw [graphAut_mul_self, mul_one]
      _ = fieldAut 3 F τ * graphAut * (graphAut * fieldAut 3 F σ) := by group
      _ = fieldAut 3 F τ * graphAut * (fieldAut 3 F σ * graphAut) := by
            rw [← fieldAut_mul_graphAut σ]
      _ = (fieldAut 3 F τ * graphAut) * (fieldAut 3 F σ * graphAut) := by group

open CFSG.StandardType.AutPSL in
private theorem commutator_le_inndiag {F : Type} [Field F] [Finite F] [CharP F 2] :
    commutator (MulAut (projectiveSL 3 F)) ≤ inndiag (n := 3) (K := F) := by
  let I : Subgroup (MulAut (projectiveSL 3 F)) := inndiag (n := 3) (K := F)
  haveI : I.Normal := inndiag_normal (n := 3) (K := F) le_rfl
  have hquot : IsMulCommutative (MulAut (projectiveSL 3 F) ⧸ I) := by
    apply IsMulCommutative.of_comm
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective I x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective I y
    obtain ⟨i, hi, c, hc, rfl⟩ := exists_mul_compl (n := 3) (K := F) le_rfl a
    obtain ⟨i', hi', c', hc', rfl⟩ := exists_mul_compl (n := 3) (K := F) le_rfl b
    have hi1 : QuotientGroup.mk' I i = 1 :=
      (QuotientGroup.eq_one_iff (N := I) i).mpr hi
    have hi1' : QuotientGroup.mk' I i' = 1 :=
      (QuotientGroup.eq_one_iff (N := I) i').mpr hi'
    simp only [map_mul, hi1, hi1', one_mul]
    rw [← map_mul, ← map_mul, compl_comm hc hc']
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hquot

theorem exists_hom_ne_one_of_properFixedComponent {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 4 ≤ m) (hme : Even m) (hF : Nat.card F = 2 ^ (2 * m)) :
    ∃ (B : Type) (_ : CommGroup B) (φ : MulAut (projectiveSL 3 F) →* B),
      ∀ (σ : MulAut (projectiveSL 3 F)) (Q : Subgroup (projectiveSL 3 F)),
        CatLeaf.ProperFixedComponent σ Q →
        Blueprint.LieModel (↥Q ⧸ Open.fusionZStar ↥Q) .PSL 3 2 m → φ σ ≠ 1 := by
  let P := projectiveSL 3 F
  let A := MulAut P
  let I : Subgroup A := CFSG.StandardType.AutPSL.inndiag (n := 3) (K := F)
  let Inn : Subgroup A := (MulAut.conj : P →* A).range
  refine ⟨Abelianization A, inferInstance, Abelianization.of, ?_⟩
  intro σ Q hσ _ hφ
  haveI : Finite P := inferInstance
  haveI : IsSimpleGroup P :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL
      (n := 3) (K := F) le_rfl
  have hσ2 : σ ^ 2 = 1 := by
    ext y
    simpa [pow_two, MulAut.mul_apply] using hσ.1 y
  have hσcomm : σ ∈ commutator A := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact hφ
  haveI : I.Normal :=
    CFSG.StandardType.AutPSL.inndiag_normal (n := 3) (K := F) le_rfl
  have hcomm_le : commutator A ≤ I := by
    dsimp [A, I, P]
    exact commutator_le_inndiag (F := F)
  have hσI : σ ∈ I := hcomm_le hσcomm
  haveI : Inn.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal P
  have hoddrel : Odd (Inn.relIndex I) := by
    dsimp [Inn, I, A, P]
    exact CFSG.StandardType.AutPSL.odd_relIndex_inn_inndiag (n := 3) (K := F)
  let q : I →* I ⧸ Inn.subgroupOf I := QuotientGroup.mk' (Inn.subgroupOf I)
  have hq2 : q ⟨σ, hσI⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have hpair : (⟨σ, hσI⟩ : I) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hσ2
    rw [hpair, map_one]
  have hcard : Nat.card (I ⧸ Inn.subgroupOf I) = Inn.relIndex I := by
    rw [← Subgroup.index_eq_card]
    rfl
  have hoddQ : Odd (Nat.card (I ⧸ Inn.subgroupOf I)) := by
    rw [hcard]
    exact hoddrel
  have hcop : Nat.Coprime 2 (Nat.card (I ⧸ Inn.subgroupOf I)) :=
    hoddQ.coprime_two_left
  have hordvd2 : orderOf (q ⟨σ, hσI⟩) ∣ 2 :=
    (orderOf_dvd_iff_pow_eq_one (x := q ⟨σ, hσI⟩) (n := 2)).mpr hq2
  have hordvdN : orderOf (q ⟨σ, hσI⟩) ∣ Nat.card (I ⧸ Inn.subgroupOf I) :=
    orderOf_dvd_natCard (q ⟨σ, hσI⟩)
  have hord1 : orderOf (q ⟨σ, hσI⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hordvd2 hordvdN
  have hq1 : q ⟨σ, hσI⟩ = 1 := orderOf_eq_one_iff.mp hord1
  have hσInn : σ ∈ Inn := by
    have hq1' : QuotientGroup.mk' (Inn.subgroupOf I) ⟨σ, hσI⟩ = 1 := hq1
    have hmem : (⟨σ, hσI⟩ : I) ∈ Inn.subgroupOf I :=
      (QuotientGroup.eq_one_iff (N := Inn.subgroupOf I) (⟨σ, hσI⟩ : I)).mp hq1'
    exact Subgroup.mem_subgroupOf.mp hmem
  have hσInn' : σ ∈ (MulAut.conj : P →* A).range := hσInn
  obtain ⟨b, hb⟩ := hσInn'
  have hnab : ∃ x y : P, x * y ≠ y * x := by
    by_contra h
    apply CFSG.RankThree.PartOne.KCLinearSubfield.not_commutative_projectiveSL
      (n := 3) (K := F) le_rfl
    intro x y
    by_contra hxy
    exact h ⟨x, y, hxy⟩
  have hinner :=
    CatLeaf.ProperFixedComponent.inner (S := P) hnab hσ (t := b) hb.symm
  have hCsol : Group.IsSolvable ↥(Subgroup.centralizer ({b} : Set P)) :=
    centralizer_proj_involution_solvable F hinner.1
  haveI : Group.IsSolvable ↥(Subgroup.centralizer ({b} : Set P)) := hCsol
  exact CFSG.ComponentClassification.GrSLit.not_isPComponent_of_isSolvable
    (Q.subgroupOf (Subgroup.centralizer ({b} : Set P))) hinner.2.2.1

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
