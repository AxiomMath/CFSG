module

public import CFSG.RankThree.PartOne.KE6.E8T3D4
public import CFSG.RankThree.PartOne.KD4L.TrialityLayer
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxBridge

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4L
open CFSG.RankThree.E6 CFSG.RankThree.Lattice
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
open scoped MatrixGroups

set_option linter.unusedSectionVars false


namespace LangLevi

variable {K : Type} [Field K] [Finite K] {w : WeylGroup Tag.E8} (D : LangLevi Tag.E8 K w)

theorem isQuasisimple_fixedRoot_D4 (v : WeylGroup Tag.E8) {S : Set (Fin Tag.E8.rank → ℤ)}
    (hS : S = (fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8))
    (hcert : ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
      (v⁻¹ * w * v) • α = permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α) :
    CFSG.IsQuasisimple ↥(D.fixedRoot S) := by
  classical
  subst hS
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨p, hpK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hpp, hcard⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : CharP D.L p := charP_of_injective_algebraMap (algebraMap K D.L).injective p
  have hcard' : Nat.card K = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hFr : D.Fr = iterateFrobenius D.L p (m : ℕ) :=
    RingHom.ext fun c => by rw [D.hFr, hcard', iterateFrobenius_def]
  have hnm : D.nW ∈ monomialSubgroup Tag.E8 D.L := canonicalRep_mem_monomialSubgroup D.L w
  have hnC : D.nW ∈ adjointGroup Tag.E8 D.L :=
    canonicalRep_mem_adjointGroup (coxeterSystem Tag.E8) D.L w
  have hwq : weylQuotientHom Tag.E8 D.L ⟨D.nW, hnm⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  obtain ⟨P, hP, hSF, -⟩ := e8_d4_factor d4TrialityLayer_E8 m.pos hcard' v D.nW hnm hnC 1 2 4
    (by decide) (by decide) (by decide) (Or.inl rfl) (Or.inr (Or.inl rfl))
    (Or.inr (Or.inr rfl))
    ⟨1, one_mem _, fun α hα => by rw [hwq, one_smul]; exact hcert α hα⟩
  have hP' : D.fixedRoot ((fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)) = P := by
    rw [hP]
    unfold LangLevi.fixedRoot LangLevi.frobGL
    rw [hFr]
  rw [hP']
  exact hSF.quasi ()

end LangLevi

namespace QuasiE8Twelve

@[expose] def wE8Twelve : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd TwClass.wordE8Twelve

@[expose] def vWord : List (Fin Tag.E8.rank) := [5, 6, 7, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 2, 0]

@[expose] def vE8 : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd vWord

@[expose] def d4ListA : List (Fin Tag.E8.rank → ℤ) :=
  [![0, -1, -1, -2, -1, 0, 0, 0], ![0, -1, -1, -1, -1, 0, 0, 0], ![0, -1, -1, -1, 0, 0, 0, 0], ![0, -1, 0, -1, -1, 0, 0, 0], ![0, -1, 0, -1, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, -1, -1, -1, 0, 0, 0], ![0, 0, -1, -1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, -1, -1, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0], ![0, 1, 1, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0, 0, 0], ![0, 1, 1, 2, 1, 0, 0, 0]]

@[expose] def d4ListB : List (Fin Tag.E8.rank → ℤ) :=
  [![-2, -3, -4, -6, -5, -4, -3, -2], ![-2, -3, -4, -6, -5, -4, -3, -1], ![-2, -3, -4, -6, -5, -4, -2, -1], ![-2, -2, -3, -4, -3, -2, -2, -1], ![-2, -2, -3, -4, -3, -2, -1, -1], ![-2, -2, -3, -4, -3, -2, -1, 0], ![0, -1, -1, -2, -2, -2, -2, -1], ![0, -1, -1, -2, -2, -2, -1, -1], ![0, -1, -1, -2, -2, -2, -1, 0], ![0, 0, 0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 1, 1, 2, 2, 2, 1, 0], ![0, 1, 1, 2, 2, 2, 1, 1], ![0, 1, 1, 2, 2, 2, 2, 1], ![2, 2, 3, 4, 3, 2, 1, 0], ![2, 2, 3, 4, 3, 2, 1, 1], ![2, 2, 3, 4, 3, 2, 2, 1], ![2, 3, 4, 6, 5, 4, 2, 1], ![2, 3, 4, 6, 5, 4, 3, 1], ![2, 3, 4, 6, 5, 4, 3, 2]]

theorem w_smul (x : Fin Tag.E8.rank → ℤ) :
    (wE8Twelve • x : Fin Tag.E8.rank → ℤ) = wordMat Tag.E8 TwClass.wordE8Twelve *ᵥ x :=
  wordProd_smul_eq_wordMat_mulVec Tag.E8 TwClass.wordE8Twelve x

theorem v_smul (x : Fin Tag.E8.rank → ℤ) :
    (vE8 • x : Fin Tag.E8.rank → ℤ) = wordMat Tag.E8 vWord *ᵥ x :=
  wordProd_smul_eq_wordMat_mulVec Tag.E8 vWord x

theorem S₂_sub : ∀ β ∈ rootFinset Tag.E8,
    (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Twelve.J₂ → β i = 0) → β ∈ d4ListA := by
  decide +kernel

theorem A_root : ∀ β ∈ d4ListA, β ∈ rootFinset Tag.E8 ∧
    ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Twelve.J₂ → β i = 0 := by decide +kernel

theorem S₂_eq : TwClass.e8Twelve.S₂ = {r | r ∈ d4ListA} := by
  ext β
  show (IsRoot Tag.E8 β ∧ ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Twelve.J₂ → β i = 0) ↔
    β ∈ d4ListA
  constructor
  · rintro ⟨hβ, hs⟩
    exact S₂_sub β (mem_rootFinset.2 hβ) hs
  · intro hβ
    exact ⟨mem_rootFinset.1 (A_root β hβ).1, (A_root β hβ).2⟩

theorem S₁_sub : ∀ β ∈ rootFinset Tag.E8, (∀ α ∈ d4ListA, iform (τ := Tag.E8) β α = 0) →
    β ∈ d4ListB := by decide +kernel

theorem B_root : ∀ β ∈ d4ListB, β ∈ rootFinset Tag.E8 ∧
    ∀ α ∈ d4ListA, iform (τ := Tag.E8) β α = 0 := by decide +kernel

theorem S₁_eq : TwClass.e8Twelve.S₁ = {r | r ∈ d4ListB} := by
  ext β
  show (IsRoot Tag.E8 β ∧ ∀ α ∈ TwClass.e8Twelve.S₂, iform (τ := Tag.E8) β α = 0) ↔
    β ∈ d4ListB
  constructor
  · rintro ⟨hβ, hs⟩
    exact S₁_sub β (mem_rootFinset.2 hβ) fun α hα => by
      rw [S₂_eq] at hs
      exact hs α hα
  · intro hβ
    refine ⟨mem_rootFinset.1 (B_root β hβ).1, fun α hα => ?_⟩
    rw [S₂_eq] at hα
    exact (B_root β hβ).2 α hα

theorem v_img : ∀ α ∈ d4ListA, wordMat Tag.E8 vWord *ᵥ α ∈ d4ListB := by decide +kernel

theorem v_cover : ∀ β ∈ d4ListB, ∃ α ∈ d4ListA, β = wordMat Tag.E8 vWord *ᵥ α := by
  decide +kernel

theorem parabolicRoots_eq : parabolicRoots Tag.E8 (d4Nodes Tag.E8) = TwClass.e8Twelve.S₂ := by
  ext α
  have h : ∀ i : Fin Tag.E8.rank, i ∉ d4Nodes Tag.E8 ↔ i.val ∉ TwClass.e8Twelve.J₂ := by
    intro i
    show ¬ (1 ≤ i.val ∧ i.val ≤ 4) ↔ i.val ∉ ({1, 2, 3, 4} : Finset ℕ)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  constructor
  · rintro ⟨hα, hs⟩
    exact ⟨hα, fun i hi => hs i ((h i).2 hi)⟩
  · rintro ⟨hα, hs⟩
    exact ⟨hα, fun i hi => hs i ((h i).1 hi)⟩

theorem image_eq : (fun γ => vE8 • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8) =
    TwClass.e8Twelve.S₁ := by
  rw [S₁_eq, parabolicRoots_eq, S₂_eq]
  ext r
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    show vE8 • γ ∈ d4ListB
    rw [v_smul]
    exact v_img γ hγ
  · intro hr
    obtain ⟨α, hα, hrα⟩ := v_cover r hr
    exact ⟨α, hα, by show vE8 • α = r; rw [v_smul]; exact hrα.symm⟩

theorem triality_A : ∀ α ∈ d4ListA, wordMat Tag.E8 TwClass.wordE8Twelve *ᵥ α =
    permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α := by decide +kernel

theorem triality_B : ∀ α ∈ d4ListA, wordMat Tag.E8 TwClass.wordE8Twelve *ᵥ
    (wordMat Tag.E8 vWord *ᵥ α) =
      wordMat Tag.E8 vWord *ᵥ permLattice (List.formPerm [(1 : Fin Tag.E8.rank), 2, 4]) α := by
  decide +kernel


theorem image_one : (fun γ => (1 : WeylGroup Tag.E8) • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8) =
    TwClass.e8Twelve.S₂ := by
  rw [parabolicRoots_eq]
  ext r
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    simpa using hγ
  · intro hr
    exact ⟨r, hr, one_smul _ _⟩

end QuasiE8Twelve

theorem isQuasisimple_e8Twelve_X₂ {K : Type} [Field K] [Finite K]
    (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) :
    CFSG.IsQuasisimple ↥(TwClass.e8Twelve.X₂ D) := by
  refine D.isQuasisimple_frame ?_
  refine D.isQuasisimple_fixedRoot_D4 (w := QuasiE8Twelve.wE8Twelve) 1
    (S := TwClass.e8Twelve.S₂) QuasiE8Twelve.image_one.symm (fun α hα => ?_)
  have hα' : α ∈ TwClass.e8Twelve.S₂ := by rw [← QuasiE8Twelve.parabolicRoots_eq]; exact hα
  rw [QuasiE8Twelve.S₂_eq] at hα'
  rw [inv_one, one_mul, mul_one, QuasiE8Twelve.w_smul]
  exact QuasiE8Twelve.triality_A α hα'

theorem isQuasisimple_e8Twelve_X₁ {K : Type} [Field K] [Finite K]
    (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) :
    CFSG.IsQuasisimple ↥(TwClass.e8Twelve.X₁ D) := by
  refine D.isQuasisimple_frame ?_
  refine D.isQuasisimple_fixedRoot_D4 (w := QuasiE8Twelve.wE8Twelve) QuasiE8Twelve.vE8
    (S := TwClass.e8Twelve.S₁) QuasiE8Twelve.image_eq.symm (fun α hα => ?_)
  have hα' : α ∈ TwClass.e8Twelve.S₂ := by rw [← QuasiE8Twelve.parabolicRoots_eq]; exact hα
  rw [QuasiE8Twelve.S₂_eq] at hα'
  rw [mul_smul, mul_smul, inv_smul_eq_iff, QuasiE8Twelve.w_smul, QuasiE8Twelve.v_smul,
    QuasiE8Twelve.v_smul]
  exact QuasiE8Twelve.triality_B α hα'

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
