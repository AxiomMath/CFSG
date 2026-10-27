module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowConj
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

section Frame

variable {p f : ℕ} {K : Type} [Field K]

theorem u4_cls3_frame (h : UnitaryFieldData p f K) (hp : p ≠ 2) {A : GL (HypIndex 2 0) K}
    (hA : A ∈ hypUnitary h 2 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1) :
    ∃ (E : Matrix (HypIndex 2 0) (Fin 4) K) (d : Fin 4 → h.fixedField), (∀ i, d i ≠ 0) ∧
      ((E.map h.bar)ᵀ * hypGram 2 0 K * E = Matrix.diagonal fun i => (d i : K)) ∧
      (∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ (fun a => h.bar (E a i)) =
        fun a => E a i) := by
  classical
  have := h.finite
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have hn1 : 1 ≤ finrank K (HypIndex 2 0 → K) := by
    rw [finrank_hypIndex_fun]
    omega
  have hAA1 : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = (1 : K) • 1 := by
    rw [one_smul]; exact hAA
  have hμ : ∀ v, conjOp h (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      (conjOp h (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) v) =
        ((Units.mk0 (1 : K) one_ne_zero : Kˣ) : K) • v := conjOp_conjOp hAA1
  obtain ⟨hμ1, ⟨b₀, hb₀⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd hn1 (hypForm_isSymm h) (hypForm_separatingLeft h) _ (conjOp_bijective one_ne_zero hAA1)
    (hypForm_conjOp hA) (Units.mk0 (1 : K) one_ne_zero) hμ
  have hb1 : h.norm ((1 : Kˣ) : K) = (((Units.mk0 (1 : K) one_ne_zero : Kˣ)⁻¹ : Kˣ) : K) := by
    simp [UnitaryFieldData.norm]
  obtain ⟨-, hfin, -, hsym, -⟩ := hall 1 t hb1 ht
  rw [finrank_hypIndex_fun] at hfin
  obtain ⟨B, hBH, hBs, hBnd, -⟩ := hsym (Units.ext rfl)
  have hmem : ∀ w ∈ conjFixed h (((1 : Kˣ) : K) • conjOp h (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)),
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ (fun a => h.bar (w a)) = w := fun w hw => by
    have h1 := mem_conjFixed.mp hw
    simpa [conjOp_apply] using h1
  have h2k : (2 : h.fixedField) ≠ 0 := fun h0 => two_ne_zero_of_odd h hp (by
    rw [← map_ofNat h.fixedField.subtype 2, h0, map_zero])
  have : Invertible (2 : h.fixedField) := invertibleOfNonzero h2k
  obtain ⟨vb, hvb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B) ⟨fun x y => hBs.eq x y⟩
  have hbo : B.iIsOrtho vb := hvb
  have hd0 := hbo.not_isOrtho_basis_self_of_nondegenerate hBnd
  have hcard : Fintype.card (Fin 4) = Fintype.card (Fin (finrank h.fixedField
      (conjFixed h (((1 : Kˣ) : K) • conjOp h
        (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K))))) := by
    rw [Fintype.card_fin, Fintype.card_fin, hfin]
  let e := Fintype.equivOfCardEq hcard
  refine ⟨colMat fun i => ((vb (e i) : conjFixed h (((1 : Kˣ) : K) • conjOp h
    (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K))) : HypIndex 2 0 → K),
    fun i => B (vb (e i)) (vb (e i)), fun i => hd0 _, ?_, ?_⟩
  · rw [gram_colMat_eq_hypForm]
    ext i j
    rw [of_apply, diagonal_apply, ← hBH]
    by_cases hij : i = j
    · subst hij; simp
    · simp only [hij, ↓reduceIte]
      have := hvb (fun h0 => hij (e.injective h0))
      simpa using congrArg (fun x : h.fixedField => (x : K)) this
  · intro i
    exact hmem _ (vb (e i)).2

end Frame

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
