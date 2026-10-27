module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three15
public import CFSG.RankThree.PartOne.KE.E7ThreeFrame

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KE6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec weylMatrix_mul weylMatrix_injective)
open CFSG.HardMathSupport.Foote.Coordinator
  (blockP extJ' extJ'_apply_mem extJ'_apply_notMem weylMatrix_mulVec_extJ')
open scoped Matrix MatrixGroups


section A2Layer

variable {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP K ℓ] [CharP L ℓ] {ε : ℤ}

private def e7T3ConjMat : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  !![ -2, 0, 1, 0, 0, 0, 0;
      -2, 0, 1, -1, 1, 0, 0;
      -3, 0, 1, 0, 0, 0, 0;
      -4, 1, 1, -1, 1, 0, 0;
      -3, 0, 0, 0, 1, 0, 0;
      -2, 0, 0, 0, 1, -1, 1;
      -1, 0, 0, 0, 1, -1, 0]

private theorem e7T3A5Transport_mat {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) :
    weylMatrix (e7T3A5Transport⁻¹ * e7T3Elt δ * e7T3A5Transport) =
      wordMat Tag.E7 e7T3CertA5.w.reverse * (δ • e7T3W) *
        wordMat Tag.E7 e7T3CertA5.w := by
  have hvinv : e7T3A5Transport⁻¹ = (coxeterSystem Tag.E7).wordProd e7T3CertA5.w.reverse := by
    simp only [e7T3A5Transport]
    rw [← CoxeterSystem.wordProd_reverse]
  simp only [e7T3A5Transport] at *
  rw [weylMatrix_mul, weylMatrix_mul, hvinv, weylMatrix_e7T3Elt hδ,
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.I102UniqAux.weylMatrix_wordProd,
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.I102UniqAux.weylMatrix_wordProd]

private theorem e7T3A5Transport_row0 :
    ∀ j : Fin Tag.E7.rank,
      weylMatrix (e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport) 0 j =
        e7T3ConjMat 0 j := by
  rw [e7T3A5Transport_mat (by left; rfl)]
  intro j
  fin_cases j <;> decide +kernel

private theorem e7T3A5Transport_row1 :
    ∀ j : Fin Tag.E7.rank,
      weylMatrix (e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport) 1 j =
        e7T3ConjMat 1 j := by
  rw [e7T3A5Transport_mat (by left; rfl)]
  intro j
  fin_cases j <;> decide +kernel

private theorem e7T3A5Transport_row2 :
    ∀ j : Fin Tag.E7.rank,
      weylMatrix (e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport) 2 j =
        e7T3ConjMat 2 j := by
  rw [e7T3A5Transport_mat (by left; rfl)]
  intro j
  fin_cases j <;> decide +kernel

private theorem e7T3A5Transport_row3 :
    ∀ j : Fin Tag.E7.rank,
      weylMatrix (e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport) 3 j =
        e7T3ConjMat 3 j := by
  rw [e7T3A5Transport_mat (by left; rfl)]
  intro j
  fin_cases j <;> decide +kernel

private theorem e7T3A5Transport_row4 :
    ∀ j : Fin Tag.E7.rank,
      weylMatrix (e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport) 4 j =
        e7T3ConjMat 4 j := by
  rw [e7T3A5Transport_mat (by left; rfl)]
  intro j
  fin_cases j <;> decide +kernel

private theorem e7T3A5Transport_row5 :
    ∀ j : Fin Tag.E7.rank,
      weylMatrix (e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport) 5 j =
        e7T3ConjMat 5 j := by
  rw [e7T3A5Transport_mat (by left; rfl)]
  intro j
  fin_cases j <;> decide +kernel

private theorem e7T3A5Transport_row6 :
    ∀ j : Fin Tag.E7.rank,
      weylMatrix (e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport) 6 j =
        e7T3ConjMat 6 j := by
  rw [e7T3A5Transport_mat (by left; rfl)]
  intro j
  fin_cases j <;> decide +kernel

private theorem weylMatrix_e7T3A5Transport_one :
    weylMatrix (e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport) = e7T3ConjMat := by
  ext i j
  fin_cases i
  · exact e7T3A5Transport_row0 j
  · exact e7T3A5Transport_row1 j
  · exact e7T3A5Transport_row2 j
  · exact e7T3A5Transport_row3 j
  · exact e7T3A5Transport_row4 j
  · exact e7T3A5Transport_row5 j
  · exact e7T3A5Transport_row6 j

private theorem weylMatrix_e7T3A5Transport_neg :
    weylMatrix (e7T3A5Transport⁻¹ * e7T3Elt (-1) * e7T3A5Transport) = -e7T3ConjMat := by
  rw [e7T3A5Transport_mat (by right; rfl)]
  have hneg : ((-1 : ℤ) • e7T3W) = -((1 : ℤ) • e7T3W) := by
    norm_num [neg_smul]
  rw [hneg, Matrix.mul_neg, Matrix.neg_mul,
    ← e7T3A5Transport_mat (δ := 1) (by left; rfl), weylMatrix_e7T3A5Transport_one]

private theorem e7T3A5Transport_apply_one (x : Fin Tag.E7.rank → ℤ) :
    (e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport) • x = e7T3ConjMat *ᵥ x := by
  rw [← weylMatrix_mulVec, weylMatrix_e7T3A5Transport_one]

private theorem e7T3A5Transport_apply_neg (x : Fin Tag.E7.rank → ℤ) :
    (e7T3A5Transport⁻¹ * e7T3Elt (-1) * e7T3A5Transport) • x = (-e7T3ConjMat) *ᵥ x := by
  rw [← weylMatrix_mulVec, weylMatrix_e7T3A5Transport_neg]

private theorem e7T3A5Transport_maps_one :
    ∀ β ∈ parabolicRoots Tag.E7
      ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _),
      (e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport) • β ∈ parabolicRoots Tag.E7
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) := by
  intro β hβ
  rw [mem_parabolicRoots_iff_mem_e7T3A2Roots] at hβ ⊢
  rw [e7T3A5Transport_apply_one β]
  simp only [e7T3A2Roots, Finset.mem_insert, Finset.mem_singleton] at hβ
  rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [e7T3A2Roots, Finset.mem_insert, Finset.mem_singleton]
     repeat' first
       | left; funext a; fin_cases a <;> decide +kernel
       | right
       | funext a; fin_cases a <;> decide +kernel)

private theorem e7T3A5Transport_maps_neg :
    ∀ β ∈ parabolicRoots Tag.E7
      ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _),
      (e7T3A5Transport⁻¹ * e7T3Elt (-1) * e7T3A5Transport) • β ∈ parabolicRoots Tag.E7
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) := by
  intro β hβ
  rw [mem_parabolicRoots_iff_mem_e7T3A2Roots] at hβ ⊢
  rw [e7T3A5Transport_apply_neg β]
  simp only [e7T3A2Roots, Finset.mem_insert, Finset.mem_singleton] at hβ
  rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [e7T3A2Roots, Finset.mem_insert, Finset.mem_singleton]
     repeat' first
       | left; funext a; fin_cases a <;> decide +kernel
       | right
       | funext a; fin_cases a <;> decide +kernel)

private theorem extJ'_single {τ : Tag} {J : Set (Fin τ.rank)} [Fintype J] [DecidableEq J]
    (i : J) : extJ' J (Pi.single i 1) = Pi.single (i : Fin τ.rank) 1 := by
  funext a
  by_cases ha : a ∈ J
  · rw [extJ'_apply_mem _ ha]
    by_cases h : (⟨a, ha⟩ : J) = i
    · subst h; simp
    · have hv : a ≠ (i : Fin τ.rank) := fun hh => h (Subtype.ext hh)
      simp [Pi.single_apply, h, hv]
  · rw [extJ'_apply_notMem _ ha]
    have hv : a ≠ (i : Fin τ.rank) := fun hh => ha (hh ▸ i.2)
    simp [Pi.single_apply, hv]

private theorem e7T3A5Transport_block_one :
    blockP (e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) *
      blockP (e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) +
      blockP (e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) + 1 = 0 := by
  apply blockP_sq_add_self_add_one_of_weylMatrix (w :=
    e7T3A5Transport⁻¹ * e7T3Elt 1 * e7T3A5Transport) e7T3A5Transport_maps_one
  intro c
  rw [weylMatrix_e7T3A5Transport_one]
  fin_cases c
  · rw [extJ'_single]
    funext a; fin_cases a <;> decide +kernel
  · rw [extJ'_single]
    funext a; fin_cases a <;> decide +kernel

private theorem e7T3A5Transport_block_neg :
    blockP (e7T3A5Transport⁻¹ * e7T3Elt (-1) * e7T3A5Transport)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) *
      blockP (e7T3A5Transport⁻¹ * e7T3Elt (-1) * e7T3A5Transport)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) -
      blockP (e7T3A5Transport⁻¹ * e7T3Elt (-1) * e7T3A5Transport)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) + 1 = 0 := by
  apply blockP_sq_sub_self_add_one_of_weylMatrix (w :=
    e7T3A5Transport⁻¹ * e7T3Elt (-1) * e7T3A5Transport) e7T3A5Transport_maps_neg
  intro c
  rw [weylMatrix_e7T3A5Transport_neg]
  fin_cases c
  · rw [extJ'_single]
    funext a; fin_cases a <;> decide +kernel
  · rw [extJ'_single]
    funext a; fin_cases a <;> decide +kernel

theorem dvd_card_A5SubA2_inf_twistedFixedPoints (F : E7ThreeFrame K L ℓ f p ε)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hε : ε = 1 ∨ ε = -1)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) :
    p ∣ Nat.card ↥(rootSpan Tag.E7 L e7T3A5SubA2 ⊓
      twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hnW : weylQuotientHom Tag.E7 L ⟨F.n, F.hnm⟩ = e7T3Elt ε := by
    apply weylMatrix_injective
    have hE := weylMatrix_e7T3Elt hε
    ext i j
    have h := F.hnW (Pi.single j 1)
    rw [← weylMatrix_mulVec] at h
    simpa [Matrix.mulVec_single_one, ← hE] using congrFun h i
  have hmaps : ∀ β ∈ parabolicRoots Tag.E7
      ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _),
      (e7T3A5Transport⁻¹ * e7T3Elt ε * e7T3A5Transport) • β ∈ parabolicRoots Tag.E7
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) := by
    rcases hε with hε | hε
    · subst hε; exact e7T3A5Transport_maps_one
    · subst hε; exact e7T3A5Transport_maps_neg
  have hP : blockP (e7T3A5Transport⁻¹ * e7T3Elt ε * e7T3A5Transport)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) *
      blockP (e7T3A5Transport⁻¹ * e7T3Elt ε * e7T3A5Transport)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) +
      ε • blockP (e7T3A5Transport⁻¹ * e7T3Elt ε * e7T3A5Transport)
        ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) + 1 = 0 := by
    rcases hε with hε | hε
    · subst hε; simpa using e7T3A5Transport_block_one
    · subst hε; simpa [sub_eq_add_neg] using e7T3A5Transport_block_neg
  have h := dvd_card_rootSpan_image_inf_twistedFixedPoints_e7 (K := K) (L := L)
    (n := F.n) (hnm := F.hnm) hε hf hK hp hp3 hpf hnW e7T3A5Transport hmaps hP
  simpa [e7T3A5SubA2] using h

end A2Layer

end CFSG.LocalAnalysis.GLTheoremA.Y10F
