module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three11
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three2

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mul weylMatrix_mulVec chainRoot)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Certs

@[expose] def e8QWord : List (Fin Tag.E8.rank) := [7, 5, 6, 4, 5, 3, 4, 1, 3]

private def e8QWord1 : List (Fin Tag.E8.rank) := [7, 5, 6, 4]

private def e8QWord2 : List (Fin Tag.E8.rank) := [5, 3, 4, 1]

private def e8QWord3 : List (Fin Tag.E8.rank) := [3]

private def e8QM1 : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, -1, 1, 0, 0], [0, 0, 0, 1, -1, 1, -1, 1],
   [0, 0, 0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 1, -1, 0]]

private def e8QM2 : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0],
   [0, -1, 1, 1, -1, 1, 0, 0], [0, 0, 0, 1, -1, 1, 0, 0], [0, 0, 0, 1, -1, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]]

private def e8QM3 : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0],
   [0, 1, 1, -1, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def e8QM : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, -1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 2, -1, 0, 1, 0, 0], [0, 0, 2, -1, 0, 0, 1, 0], [0, 0, 2, -1, 0, 0, 0, 1],
   [0, 1, 1, -1, 0, 0, 0, 1], [0, 1, 1, -1, 0, 0, 0, 0]]

private theorem weylMatrix_e8QWord1 : weylMatrix ((coxeterSystem Tag.E8).wordProd e8QWord1) =
    toMat Tag.E8.rank e8QM1 :=
  weylMatrix_wordProd_of (by decide +kernel)

private theorem weylMatrix_e8QWord2 : weylMatrix ((coxeterSystem Tag.E8).wordProd e8QWord2) =
    toMat Tag.E8.rank e8QM2 :=
  weylMatrix_wordProd_of (by decide +kernel)

private theorem weylMatrix_e8QWord3 : weylMatrix ((coxeterSystem Tag.E8).wordProd e8QWord3) =
    toMat Tag.E8.rank e8QM3 :=
  weylMatrix_wordProd_of (by decide +kernel)

theorem weylMatrix_e8QWord :
    weylMatrix ((coxeterSystem Tag.E8).wordProd e8QWord) = toMat Tag.E8.rank e8QM := by
  rw [e8QWord, show ([7, 5, 6, 4, 5, 3, 4, 1, 3] : List (Fin Tag.E8.rank)) =
      e8QWord1 ++ (e8QWord2 ++ e8QWord3) from rfl,
    CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append, weylMatrix_mul, weylMatrix_mul,
    weylMatrix_e8QWord1, weylMatrix_e8QWord2, weylMatrix_e8QWord3,
    ← toMat_lmul, ← toMat_lmul]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem sigmaSetE8_e8QWord :
    sigmaSetE8 ((coxeterSystem Tag.E8).wordProd e8QWord) = e8A2Roots := by
  rw [e8A2Roots_explicit, sigmaSetE8_eq]
  ext r
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | (rw [sigmaRootE8_eq_smul, ← weylMatrix_mulVec, weylMatrix_e8QWord]
           decide +kernel)
  · rintro (h | h | h | h | h | h) <;>
      first
        | exact ⟨0, 1, by decide, by
            rw [h, sigmaRootE8_eq_smul, ← weylMatrix_mulVec, weylMatrix_e8QWord]
            decide +kernel⟩
        | exact ⟨1, 0, by decide, by
            rw [h, sigmaRootE8_eq_smul, ← weylMatrix_mulVec, weylMatrix_e8QWord]
            decide +kernel⟩
        | exact ⟨1, 2, by decide, by
            rw [h, sigmaRootE8_eq_smul, ← weylMatrix_mulVec, weylMatrix_e8QWord]
            decide +kernel⟩
        | exact ⟨2, 1, by decide, by
            rw [h, sigmaRootE8_eq_smul, ← weylMatrix_mulVec, weylMatrix_e8QWord]
            decide +kernel⟩
        | exact ⟨0, 2, by decide, by
            rw [h, sigmaRootE8_eq_smul, ← weylMatrix_mulVec, weylMatrix_e8QWord]
            decide +kernel⟩
        | exact ⟨2, 0, by decide, by
            rw [h, sigmaRootE8_eq_smul, ← weylMatrix_mulVec, weylMatrix_e8QWord]
            decide +kernel⟩

variable {L : Type} [Field L]

@[expose] def e8T3QLayer (n : ModGL Tag.E8 L) (Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L) :
    Subgroup (ModGL Tag.E8 L) :=
  rootSpan Tag.E8 L e8A2Roots ⊓ twistedFixedPoints n Φ

private theorem e8QWord_maps {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∀ β ∈ parabolicRoots Tag.E8 ({0, 2} : Set (Fin Tag.E8.rank)),
      (((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3We ε *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) • β ∈
        parabolicRoots Tag.E8 ({0, 2} : Set (Fin Tag.E8.rank)) := by
  intro β hβ
  have hβS : ((coxeterSystem Tag.E8).wordProd e8QWord) • β ∈ e8A2Roots := by
    rw [← sigmaSetE8_e8QWord]
    exact ⟨β, hβ, rfl⟩
  have hWS : e8T3We ε • (((coxeterSystem Tag.E8).wordProd e8QWord) • β) ∈ e8A2Roots :=
    e8T3We_smul_mem_e8A2Roots hε _ hβS
  have hpre : (fun γ => ((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ • γ) '' e8A2Roots =
      parabolicRoots Tag.E8 ({0, 2} : Set (Fin Tag.E8.rank)) := by
    rw [← sigmaSetE8_e8QWord]
    change (fun γ => ((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ • γ) ''
      ((fun γ => ((coxeterSystem Tag.E8).wordProd e8QWord) • γ) ''
        parabolicRoots Tag.E8 ({0, 2} : Set (Fin Tag.E8.rank))) = _
    rw [Set.image_image]
    ext γ
    simp
  rw [mul_smul, mul_smul]
  rw [← hpre]
  exact ⟨_, hWS, rfl⟩

private theorem e8QWord_rel {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (x : Fin Tag.E8.rank → ℤ) :
    (((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3We ε *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) •
      ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3We ε *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) • x) +
      ε • ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3We ε *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) • x) + x = 0 := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hU : ∀ y : Fin Tag.E8.rank → ℤ,
      (((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3W *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) •
      ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3W *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) • y) +
      (((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3W *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) • y + y = 0 := by
    intro y
    simpa using rel_conj e8T3W_rel ((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ y
  have hW : ∀ y : Fin Tag.E8.rank → ℤ,
      (((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3We ε *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) • y =
      ε • ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3W *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) • y) :=
    fun y => conj_smul_eq hε (fun _ => rfl) _ y
  have hWU : ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3We ε *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) •
      ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3W *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) • x)) =
      ε • ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3W *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) •
        ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3W *
          ((coxeterSystem Tag.E8).wordProd e8QWord)) • x)) := hW _
  have h1 : ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3We ε *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) •
      ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3We ε *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) • x)) =
      ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3W *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) •
        ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3W *
          ((coxeterSystem Tag.E8).wordProd e8QWord)) • x)) := by
    rw [hW x, smul_zsmul_E8, hWU, smul_smul, hε2, one_smul]
  have h2 : ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3We ε *
      ((coxeterSystem Tag.E8).wordProd e8QWord)) • x) =
      ε • ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3W *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) • x) := hW x
  rw [h1, h2]
  have hεU : ε • (ε • ((((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3W *
      ((coxeterSystem Tag.E8).wordProd e8QWord)) • x)) =
      (((coxeterSystem Tag.E8).wordProd e8QWord)⁻¹ * e8T3W *
        ((coxeterSystem Tag.E8).wordProd e8QWord)) • x := by
    rw [smul_smul, hε2, one_smul]
  rw [hεU]
  exact hU x

end Certs

section Layer

variable {L : Type} [Field L]

theorem isQuasisimple_e8T3QLayer {k : Type} [Field k] [Finite k] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP k ℓ] [Algebra k L] [IsAlgClosure k L] [IsAlgClosed L] [CharP L ℓ]
    (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq2 : ε = -1 → 2 < ℓ ^ f) (n : ModGL Tag.E8 L)
    (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : Fin Tag.E8.rank → ℤ,
      weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x) :
    CFSG.IsQuasisimple ↥(e8T3QLayer n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have h := isQuasisimple_a2Layer (L := L) hf hk hε hq2
    ((coxeterSystem Tag.E8).wordProd e8QWord) n hnm hnC hnW
    (fun α hα => by
      rw [sigmaSetE8_e8QWord] at hα ⊢
      exact e8T3We_smul_mem_e8A2Roots hε α hα)
    (fun α hα => by
      rw [sigmaSetE8_e8QWord] at hα ⊢
      exact neg_mem_e8A2Roots hα)
  rwa [sigmaSetE8_e8QWord] at h

theorem dvd_card_e8T3QLayer {k : Type} [Field k] [Finite k] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP k ℓ] [Algebra k L] [IsAlgClosure k L] [CharP L ℓ] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1)
    (hpf : (p : ℤ) ∣ (Nat.card k : ℤ) ^ 2 + ε * (Nat.card k : ℤ) + 1)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε) :
    p ∣ Nat.card ↥(e8T3QLayer n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  have h := dvd_card_rootSpan_image_inf_twistedFixedPoints_a2 hε k hf hk L hp
    hp3 hpf n hnm hnW ((coxeterSystem Tag.E8).wordProd e8QWord) 0 2 (by decide)
    (e8QWord_maps hε) (e8QWord_rel hε)
  rw [show (fun γ => ((coxeterSystem Tag.E8).wordProd e8QWord) • γ) ''
      parabolicRoots Tag.E8 ({0, 2} : Set (Fin Tag.E8.rank)) = e8A2Roots from
    sigmaSetE8_e8QWord] at h
  exact h

end Layer

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
