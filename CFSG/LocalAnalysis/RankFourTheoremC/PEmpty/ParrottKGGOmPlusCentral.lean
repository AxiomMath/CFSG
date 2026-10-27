module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightResidualStable
public import CFSG.RankThree.PartOne.KLC.D4OutCentral

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus

open Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n f : ℕ}

namespace KGB

theorem eq_one_of_mem_of_mem_range_conj {P : Type*} [Group P] {S : Subgroup (MulAut P)}
    (hSI : S ⊓ (MulAut.conj : P →* MulAut P).range = ⊥) {x : MulAut P} (hxS : x ∈ S)
    (hxI : x ∈ (MulAut.conj : P →* MulAut P).range) : x = 1 := by
  have h : x ∈ S ⊓ (MulAut.conj : P →* MulAut P).range := Subgroup.mem_inf.2 ⟨hxS, hxI⟩
  rw [hSI] at h
  exact (Subgroup.mem_bot).1 h

theorem commutator_mem_range_conj (hn : 4 ≤ n) (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {a b : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))}
    (ha : a ∈ matrixProjectiveImage (coordinateQuadPlus n F))
    (hb : b ∈ matrixProjectiveImage (coordinateQuadPlus n F)) :
    a * b * a⁻¹ * b⁻¹ ∈ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n F) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))).range := by
  have hreg := regular_coordinateQuadPlus n F (by omega)
  have hQ : ∃ v, coordinateQuadPlus n F v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hreg.1 hreg.2
  have h := CFSG.RankThree.PartOne.KLC.matrixProjectiveImage_commutator_mem_inner _ hQ
    (CFSG.SeitzReduction.OmegaPilot.card_abelianization_isometries_plus_le_two hf hF hn) ha hb
  rw [commutatorElement_def] at h
  exact h

section Four

open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit (plusCX plusCXstar)
open CFSG.SeitzReduction.OmegaPilot (mem_image_iff_smul_pointFamily plusCX_ne_plusCXstar
  smul_plusCX_of_mem_image smul_mem_plusFourTripleSet plusFourTripleSet plusImageFieldPart
  eq_conj_of_smul_plusCX_of_fp_eq_one)
open scoped Pointwise

theorem smul_plusCX_of_mem_normalizer
    {S : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)))}
    (hSE : S ≤ matrixProjectiveImage (coordinateQuadPlus 4 F))
    {b : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))}
    (hb : b ∈ normalizer (S : Set (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)))))
    (hbE : b ∉ matrixProjectiveImage (coordinateQuadPlus 4 F))
    {s : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))} (hs : s ∈ S) :
    s • plusCX 4 F = plusCX 4 F := by
  have hmemE := mem_image_iff_smul_pointFamily (k := F) (n := 4) le_rfl
  have hXX := plusCX_ne_plusCXstar 4 F (by norm_num)
  have hbF : b • projectivePointFamily (coordinateQuadPlus 4 F) ≠
      projectivePointFamily (coordinateQuadPlus 4 F) := fun h => hbE ((hmemE b).2 h)
  have hconj : b⁻¹ * s * b ∈ S := (Subgroup.mem_normalizer_iff''.1 hb s).1 hs
  have hsb : s • (b • projectivePointFamily (coordinateQuadPlus 4 F)) =
      b • projectivePointFamily (coordinateQuadPlus 4 F) := by
    have h1 := (hmemE _).1 (hSE hconj)
    rw [mul_smul, mul_smul, inv_smul_eq_iff] at h1
    exact h1
  rcases smul_plusCX_of_mem_image (hSE hs) with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    rcases smul_mem_plusFourTripleSet b
      (Or.inl rfl : projectivePointFamily (coordinateQuadPlus 4 F) ∈ plusFourTripleSet F) with
      h | h | h
    · exact hbF h
    · rw [h, h1] at hsb
      exact hXX hsb.symm
    · rw [h, h2] at hsb
      exact hXX hsb

theorem isCyclic_of_smul_plusCX (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {S : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)))}
    (hSE : S ≤ matrixProjectiveImage (coordinateQuadPlus 4 F))
    (hSI : S ⊓ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 F) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))).range = ⊥)
    (hSX : ∀ s ∈ S, s • plusCX 4 F = plusCX 4 F) : IsCyclic ↥S := by
  have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
  refine isCyclic_of_injective
    ((plusImageFieldPart hf hF (by norm_num)).comp (Subgroup.inclusion hSE)) ?_
  rw [injective_iff_map_eq_one]
  rintro ⟨s, hs⟩ h1
  obtain ⟨x, hx⟩ := eq_conj_of_smul_plusCX_of_fp_eq_one hf hF (hSE hs) (hSX s hs) h1
  exact Subtype.ext (eq_one_of_mem_of_mem_range_conj hSI hs (MonoidHom.mem_range.2 ⟨x, hx.symm⟩))

end Four

end KGB

theorem commute_of_mem_image (hn : 4 ≤ n) (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {S : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus n F)))}
    (hSE : S ≤ matrixProjectiveImage (coordinateQuadPlus n F))
    (hSI : S ⊓ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n F) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))).range = ⊥)
    {s t : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))} (hs : s ∈ S) (ht : t ∈ S) :
    s * t = t * s := by
  have h1 := KGB.eq_one_of_mem_of_mem_range_conj hSI
    (S.mul_mem (S.mul_mem (S.mul_mem hs ht) (S.inv_mem hs)) (S.inv_mem ht))
    (KGB.commutator_mem_range_conj hn hf hF (hSE hs) (hSE ht))
  calc s * t = s * t * s⁻¹ * t⁻¹ * (t * s) := by group
    _ = t * s := by rw [h1, one_mul]

theorem mem_image_of_mem_normalizer (hn : 4 ≤ n) (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {S : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus n F)))}
    (hSE : S ≤ matrixProjectiveImage (coordinateQuadPlus n F))
    (hSI : S ⊓ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n F) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))).range = ⊥)
    (hnc : ¬ IsCyclic ↥S) {b : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))}
    (hb : b ∈ normalizer (S : Set (MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))))) :
    b ∈ matrixProjectiveImage (coordinateQuadPlus n F) := by
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · obtain rfl : n = 4 := by omega
    by_contra hbE
    exact hnc (KGB.isCyclic_of_smul_plusCX hf hF hSE hSI
      fun s hs => KGB.smul_plusCX_of_mem_normalizer hSE hb hbE hs)
  · rw [CFSG.SeitzReduction.OmegaPilot.plusImage_eq_top h5]
    exact Subgroup.mem_top b

theorem commute_of_mem_normalizer (hn : 4 ≤ n) (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {S : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus n F)))}
    (hSE : S ≤ matrixProjectiveImage (coordinateQuadPlus n F))
    (hSI : S ⊓ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n F) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))).range = ⊥)
    (hnc : ¬ IsCyclic ↥S) {b s : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))}
    (hb : b ∈ normalizer (S : Set (MulAut (matrixProjectiveDerived (coordinateQuadPlus n F)))))
    (hs : s ∈ S) : b * s = s * b := by
  have hbs : b * s * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hb s).1 hs
  have h1 := KGB.eq_one_of_mem_of_mem_range_conj hSI (S.mul_mem hbs (S.inv_mem hs))
    (KGB.commutator_mem_range_conj hn hf hF
      (mem_image_of_mem_normalizer hn hf hF hSE hSI hnc hb) (hSE hs))
  calc b * s = b * s * b⁻¹ * s⁻¹ * (s * b) := by group
    _ = s * b := by rw [h1, one_mul]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus
